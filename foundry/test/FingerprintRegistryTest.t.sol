// SPDX-License-Identifier: SEE LICENSE IN LICENSE
pragma solidity ^0.8.19;

import {DeployFingerprintRegistry} from "script/DeployFingerprintRegistry.s.sol";
import {FingerprintRegistry} from "src/core/FingerprintRegistry.sol";
import {Test, console2} from "forge-std/Test.sol";

contract FingerprintRegistryTest is Test {
    string constant CID = "bafybeiavkv6bba5ps7xlzlrorbtqbsk564ghlwhjrpnezcoubwcikgzgh4";
    string constant FINGERPRINT = "5792e1051219b3c6cc071e6c227f8b64770077ad64e360f9b6491bb472aa3c78";
    address OWNER = makeAddr("owner");

    FingerprintRegistry registry;

    function setUp() public {
        DeployFingerprintRegistry deployer = new DeployFingerprintRegistry();
        address registryAddr = deployer.run();
        registry = FingerprintRegistry(registryAddr);
    }

    function testRegisterModel() public {
        vm.prank(OWNER);
        registry.registerModel(CID, FINGERPRINT);

        assertEq(registry.recordCount(), 1);

        FingerprintRegistry.ModelRecord memory record = registry.getRecord(1);

        assertEq(record.cid, CID);
        assertEq(record.fingerprint, FINGERPRINT);
        assertEq(record.owner, OWNER);
        assertGt(record.timestamp, 0);
    }

    function testInvalidRecord() public {
        vm.expectRevert();
        FingerprintRegistry.ModelRecord memory record = registry.getRecord(999);

        assertEq(record.cid, "");
        assertEq(record.fingerprint, "");
        assertEq(record.owner, address(0));
        assertEq(record.timestamp, 0);
    }
}
