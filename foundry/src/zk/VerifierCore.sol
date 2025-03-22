// SPDX-License-Identifier: SEE LICENSE IN LICENSE
pragma solidity ^0.8.19;

/**
 * @title VerifierCore
 * @dev Standalone elliptic curve operations for zk-SNARK verification on BN254
 * Deployable as an external verifier logic contract
 */
contract VerifierCore {
    uint256 private constant PRIME_Q = 21888242871839275222246405745257275088548364400416034343698204186575808495617;

    struct G1Point {
        uint256 X;
        uint256 Y;
    }

    struct G2Point {
        uint256[2] X;
        uint256[2] Y;
    }

    /**
     * @notice Negates a G1 point on BN254.
     * @param p G1 point to negate.
     * @return r The negated G1 point.
     */
    function negate(G1Point memory p) public pure returns (G1Point memory r) {
        if (p.X == 0 && p.Y == 0) {
            return G1Point(0, 0);
        }
        return G1Point(p.X, PRIME_Q - (p.Y % PRIME_Q));
    }

    /**
     * @notice Adds two G1 points on BN254.
     * @param p1 First point.
     * @param p2 Second point.
     * @return r The resulting point.
     */
    function addition(G1Point memory p1, G1Point memory p2) public view returns (G1Point memory r) {
        uint256[4] memory input;
        input[0] = p1.X;
        input[1] = p1.Y;
        input[2] = p2.X;
        input[3] = p2.Y;

        bool success;
        assembly {
            // Call ECADD precompile (0x06)
            success := staticcall(gas(), 0x06, input, 0x80, r, 0x40)
        }
        require(success, "EC addition failed");
    }

    /**
     * @notice Performs a pairing check.
     * @param p1 Array of G1 points.
     * @param p2 Array of G2 points.
     * @return isValid True if pairing product is 1.
     */
    function pairing(G1Point[] memory p1, G2Point[] memory p2) public view returns (bool isValid) {
        require(p1.length == p2.length, "Pairing input length mismatch");
        uint256 elements = p1.length;

        uint256 inputSize = elements * 6;
        uint256[] memory input = new uint256[](inputSize);

        for (uint256 i = 0; i < elements; i++) {
            uint256 j = i * 6;
            input[j + 0] = p1[i].X;
            input[j + 1] = p1[i].Y;
            input[j + 2] = p2[i].X[0];
            input[j + 3] = p2[i].X[1];
            input[j + 4] = p2[i].Y[0];
            input[j + 5] = p2[i].Y[1];
        }

        uint256[1] memory out;
        bool success;
        assembly {
            // Call BN256_PAIRING precompile (0x08)
            success := staticcall(gas(), 0x08, add(input, 0x20), mul(inputSize, 0x20), out, 0x20)
        }
        require(success, "Pairing check failed");
        return out[0] == 1;
    }
}
