// SPDX-License-Identifier: SEE LICENSE IN LICENSE
pragma solidity ^0.8.24;

import {FingerprintRegistry} from "src/core/FingerprintRegistry.sol";
import {Script, console2} from "forge-std/Script.sol";

contract DeployFingerprintRegistry is Script {
    FingerprintRegistry public registry;

    function run() public returns (address) {
        registry = new FingerprintRegistry();
        console2.log("FingerprintRegistry deployed at:", address(registry));
        return address(registry);
    }
}
