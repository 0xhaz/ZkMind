// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

import {IVerifierCore} from "src/interfaces/IVerifierCore.sol";

/**
 * @title VKStorage
 * @notice Stores the Verification Key (VK) data for the Halo2Verifier contract.
 */
contract VKStorage {
    /// @notice Returns the alpha_1 G1 point.
    function alpha1() public pure returns (IVerifierCore.G1Point memory) {
        return IVerifierCore.G1Point({
            X: 0x2e854db8337d7a7e628ce1fbd5f8eb481bc07fc9750c67c11b663e6a3c26e007,
            Y: 0x27ecaf83164fd64d45af806ec351af3b4f0d897d8ec3a7007e9ad0ebae6d7871
        });
    }

    /// @notice Returns the beta_2 G2 point.
    function beta2() public pure returns (IVerifierCore.G2Point memory) {
        return IVerifierCore.G2Point({
            X: [
                0x22b39cf53f21dbcc7fec3302efbfb95f6c012f2c95cd28ab73b02a10e1c307e0,
                0x17bd4f19d6a432d396fd86207f87cf20b23ccaa96c0616d187aa20e2e8123431
            ],
            Y: [
                0x4728951ed88caf60e679626834b39257963d86b915242ba862763c4f8e0c84d0,
                0x82b884c9c3c0d6a35c2621fae937dd892b87c30df9ad4ce843e0309d6d963e42
            ]
        });
    }

    /// @notice Returns the gamma_2 G2 point.
    function gamma2() public pure returns (IVerifierCore.G2Point memory) {
        return IVerifierCore.G2Point({
            X: [
                0x04991a4cbe4c45273b761fc2442f0b76067a5495124e26163092791012f27e3a,
                0x2965b4c4ef6ca46574e3614c1076059f2a54c2bdb04a871162f8696184d4a16b
            ],
            Y: [
                0x2e2cf894e8de75de0bd4958a2847f316687cdcebe13e002284d739dd2f2f7797,
                0x0b62201eb4e7e60737c80a99cecfa2df7c55e35b4afec1e6a56ecf3d65a047114
            ]
        });
    }

    /// @notice Returns the delta_2 G2 point.
    function delta2() public pure returns (IVerifierCore.G2Point memory) {
        return IVerifierCore.G2Point({
            X: [
                0x98758fe2a1619bfd1f589659daac1e727034720011df062d855058807f3e3d4d,
                0xf155040d0d53bbee28074a3c201e5dd24c264db61738bcdc12c357dcc13d61e9
            ],
            Y: [
                0xeca0c22763cccb2103a052ed1fd2daf3095c4868857af52e291b3b2a3f854383,
                0x04dee4d5d33bdbf41f589659daac1e727034720011df062d855058807f3e3d4d
            ]
        });
    }

    /// @notice Returns the i-th G1Point from the IC array.
    function ic(uint256 i) public pure returns (IVerifierCore.G1Point memory) {
        IVerifierCore.G1Point[10] memory points = [
            IVerifierCore.G1Point(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effffc1e, 0),
            IVerifierCore.G1Point(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effffe72, 0),
            IVerifierCore.G1Point(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593efffff44, 0),
            IVerifierCore.G1Point(0x000000000000000000000000000000000000000000000000000000000000022c, 0),
            IVerifierCore.G1Point(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effffca9, 0),
            IVerifierCore.G1Point(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effffc38, 0),
            IVerifierCore.G1Point(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effff457, 0),
            IVerifierCore.G1Point(0x0000000000000000000000000000000000000000000000000000000000000824, 0),
            IVerifierCore.G1Point(0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593effffe6e, 0),
            IVerifierCore.G1Point(0x00000000000000000000000000000000000000000000000000000000000000a0, 0)
        ];
        require(i < points.length, "Index out of bounds");
        return points[i];
    }

    /// @notice Returns the number of IC points.
    function getICLength() external pure returns (uint256) {
        return 10;
    }

    /// @notice Returns the i-th G1Point from the IC array.
    function getIC(uint256 i) external pure returns (IVerifierCore.G1Point memory) {
        return ic(i);
    }

    /// @notice Returns the gamma_2 G2 point.
    function getGamma2() external pure returns (IVerifierCore.G2Point memory) {
        return gamma2();
    }

    /// @notice Returns the alpha_1 G1 point.
    function getAlpha1() external pure returns (IVerifierCore.G1Point memory) {
        return alpha1();
    }

    /// @notice Returns the beta_2 G2 point.
    function getBeta2() external pure returns (IVerifierCore.G2Point memory) {
        return beta2();
    }

    /// @notice Returns the delta_2 G2 point.
    function getDelta2() external pure returns (IVerifierCore.G2Point memory) {
        return delta2();
    }
}
