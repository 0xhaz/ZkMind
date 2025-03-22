// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {IVerifierCore} from "src/interfaces/IVerifierCore.sol";
import {VKStorage} from "src/zk/VKStorage.sol";

/**
 * @title Halo2Verifier
 * @notice Groth16 verifier using external core contract.
 */
contract Halo2Verifier {
    IVerifierCore public immutable core;
    VKStorage public immutable vk;

    constructor(address _core, address _vkStorage) {
        core = IVerifierCore(_core);
        vk = VKStorage(_vkStorage);
    }

    /**
     * @notice Verifies Groth16 proof with given instances (public inputs).
     * @param proof Encoded proof: A.X, A.Y, B.X[0], B.X[1], B.Y[0], B.Y[1], C.X, C.Y (8 × 32 bytes).
     * @param instances Public inputs.
     * @return True if the proof is valid.
     */
    function verifyProof(bytes calldata proof, uint256[] calldata instances) public view returns (bool) {
        require(proof.length == 256, "Invalid proof length");

        // === Decode proof ===
        IVerifierCore.G1Point memory A = IVerifierCore.G1Point(_loadField(proof, 0), _loadField(proof, 32));
        IVerifierCore.G2Point memory B = IVerifierCore.G2Point(
            [_loadField(proof, 64), _loadField(proof, 96)], [_loadField(proof, 128), _loadField(proof, 160)]
        );
        IVerifierCore.G1Point memory C = IVerifierCore.G1Point(_loadField(proof, 192), _loadField(proof, 224));

        // === Compute vk_x ===
        uint256 icLength = vk.getICLength();
        require(instances.length + 1 == icLength, "Input length mismatch");

        IVerifierCore.G1Point memory vk_x = vk.getIC(0);
        for (uint256 i = 0; i < instances.length; ++i) {
            IVerifierCore.G1Point memory ic = vk.getIC(i + 1);
            IVerifierCore.G1Point memory mul = _ecMul(ic, instances[i]);
            vk_x = core.addition(vk_x, mul);
        }

        // === Build pairing inputs ===
        IVerifierCore.G1Point[] memory p1 = new IVerifierCore.G1Point[](4);
        IVerifierCore.G2Point[] memory p2 = new IVerifierCore.G2Point[](4);

        p1[0] = A;
        p2[0] = B;

        p1[1] = core.negate(vk_x);
        p2[1] = vk.getGamma2();

        p1[2] = C;
        p2[2] = vk.getDelta2();

        p1[3] = vk.getAlpha1();
        p2[3] = vk.getBeta2();

        // === Verify pairing equation ===
        return core.pairing(p1, p2);
    }

    /// @dev Loads a 32-byte field element from calldata at offset.
    function _loadField(bytes calldata data, uint256 offset) internal pure returns (uint256 result) {
        require(data.length >= offset + 32, "Slice out of bounds");
        assembly {
            result := calldataload(add(data.offset, offset))
        }
    }

    /// @dev Scalar multiplication via EC precompile (0x07)
    function _ecMul(IVerifierCore.G1Point memory p, uint256 s) internal view returns (IVerifierCore.G1Point memory r) {
        uint256[3] memory input = [p.X, p.Y, s];
        bool success;
        assembly {
            success := staticcall(gas(), 0x07, input, 0x60, r, 0x40)
        }
        require(success, "EC scalar mul failed");
    }
}
