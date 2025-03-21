// SPDX-License-Identifier: SEE LICENSE IN LICENSE
pragma solidity ^0.8.19;

import {FingerprintRegistry} from "src/core/FingerprintRegistry.sol";
import {Script, console2} from "forge-std/Script.sol";

contract DeployFingerprintRegistry is Script {
    FingerprintRegistry public registry;

    function run() public returns (address) {
        vm.startBroadcast();
        registry = new FingerprintRegistry();
        vm.stopBroadcast();
        console2.log("FingerprintRegistry deployed at:", address(registry));
        return address(registry);
    }
}
