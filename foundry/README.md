# ZkMind - Decentralized AI Verification & Reputation Hub

## Week 1: AI Model Training & Fingerprinting

- **Model**: MNIST classifier (98.81% accuracy).
- **Fingerprint**: `5792e1051219b3c6cc071e6c227f8b64770077ad64e360f9b6491bb472aa3c78`.
- **Storacha CID**: `bafybeiavkv6bba5ps7xlzlrorbtqbsk564ghlwhjrpnezcoubwcikgzgh4`.
- **Contract**: `0x388Fc77700AEF34087bAD543Cea69F6b132b9fA5` (Calibration testnet).
- **Deployment Tx**: `0xdad965a3320c3dc81fcf311ac9ee90e2bace1e51d0c9c0640d4d000024e97e68`.
- **Registration Tx**: `0x1ea92beea58bfb365da7cc966392ff847bbc23de3d01fa4a09e02b8ac92c485e`.
- **Details**: Record ID 1 stores CID, fingerprint, timestamp (1742576130), and owner.

## Week 2: Privacy-Preserving AI Model Verification (ZKML)

### Day 1 (March 26): Proof Generation

- **Model**: MNIST classifier (from Week 1).
- **Input**: Flattened MNIST test image `[1, 784]`.
- **EZKL**: Generated ZK proof of inference.
- **Files**:
  - `mnist.onnx`: Exported model.
  - `mnist.ezkl`: Compiled circuit.
  - `input.json`: Normalized input.
  - `witness.json`: 115 KB computation trace.
  - `proof.json`: ZK proof (verified locally).
  - `pk.key`, `vk.key`: Keys for proving/verification.
