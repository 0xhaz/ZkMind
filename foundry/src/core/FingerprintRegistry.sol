// SPDX-License-Identifier: SEE LICENSE IN LICENSE
pragma solidity ^0.8.19;

contract FingerprintRegistry {
    struct ModelRecord {
        string cid; // IPFS CID of the model and fingerprint
        string fingerprint; // SHA-256 hash of the model
        uint256 timestamp; // Timestamp of the model registration
        address owner; // Owner of the model
    }

    constructor() {}

    mapping(uint256 => ModelRecord) public records;
    uint256 public recordCount;

    event ModelRegistered(uint256 id, string cid, string fingerprint, uint256 timestamp, address owner);

    function registerModel(string memory _cid, string memory _fingerprint) external {
        recordCount++;
        records[recordCount] =
            ModelRecord({cid: _cid, fingerprint: _fingerprint, timestamp: block.timestamp, owner: msg.sender});
        emit ModelRegistered(recordCount, _cid, _fingerprint, block.timestamp, msg.sender);
    }

    function getRecord(uint256 _id) external view returns (ModelRecord memory) {
        require(_id > 0 && _id <= recordCount, "Invalid ID");
        return records[_id];
    }
}
