// SPDX-License-Identifier: SEE LICENSE IN LICENSE
pragma solidity ^0.8.19;

import {Script, console2} from "forge-std/Script.sol";
import {Halo2Verifier} from "src/zk/VerificationContract.sol";
import {VerifierCore} from "src/zk/VerifierCore.sol";
import {VKStorage} from "src/zk/VKStorage.sol";

contract DeployVerificationContract is Script {
    function run() public returns (address) {
        vm.startBroadcast();
        VerifierCore verifierCore = new VerifierCore();
        console2.log("Verifier core deployed at:", address(verifierCore));

        VKStorage vkStorage = new VKStorage();
        console2.log("VK storage deployed at:", address(vkStorage));

        Halo2Verifier vkContract = new Halo2Verifier(address(verifierCore), address(vkStorage));
        console2.log("Verification contract deployed at:", address(vkContract));
        vm.stopBroadcast();

        return address(vkContract);
    }
}
