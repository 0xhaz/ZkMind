// SPDX-License-Identifier: SEE LICENSE IN LICENSE
pragma solidity ^0.8.19;

interface IVerifierCore {
    struct G1Point {
        uint256 X;
        uint256 Y;
    }

    struct G2Point {
        uint256[2] X;
        uint256[2] Y;
    }

    function negate(G1Point calldata) external pure returns (G1Point memory);
    function addition(G1Point calldata, G1Point calldata) external view returns (G1Point memory);
    function pairing(G1Point[] calldata, G2Point[] calldata) external view returns (bool);
}
