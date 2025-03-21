import torch
from torchvision import datasets, transforms
import ezkl
import os
import json
import asyncio

async def generate_zk_proof():
    # Load a sample MNIST image
    transform = transforms.Compose([transforms.ToTensor(), transforms.Normalize((0.1307,), (0.3081,))])
    test_dataset = datasets.MNIST(root="../data", train=False, transform=transform, download=True)
    sample_image, sample_label = test_dataset[0]
    sample_input = sample_image.flatten().tolist()  # [784]

    # Save input as JSON
    input_json = {"input_data": [sample_input]}  # [1, 784]
    input_path = "../zkml/input.json"
    with open(input_path, "w") as f:
        json.dump(input_json, f)

    # EZKL setup
    model_path = "../zkml/mnist.onnx"
    compiled_model_path = "../zkml/mnist.ezkl"
    settings_path = "../zkml/settings.json"
    srs_path = "../zkml/kzg.srs"
    pk_path = "../zkml/pk.key"
    vk_path = "../zkml/vk.key"
    witness_path = "../zkml/witness.json"
    proof_path = "../zkml/proof.json"

    # 1. Generate settings
    ezkl.gen_settings(model_path, settings_path)
    print("Settings generated")

    # 2. Compile the model
    ezkl.compile_circuit(model_path, compiled_model_path, settings_path)
    print("Model compiled")

    # 3. Ensure SRS
    if not os.path.exists(srs_path):
        ezkl.get_srs(settings_path=settings_path, srs_path=srs_path)
        print("SRS downloaded")

    # 4. Generate keys
    ezkl.setup(compiled_model_path, vk_path, pk_path, srs_path=srs_path)
    print("Keys generated")

    # 5. Generate witness
    print(f"Generating witness with input: {input_path}, model: {compiled_model_path}, output: {witness_path}")
    ezkl.gen_witness(input_path, compiled_model_path, witness_path)
    if os.path.exists(witness_path):
        print("Witness generated successfully")
    else:
        raise RuntimeError(f"Witness file not created at {witness_path}")

    # 6. Generate proof
    ezkl.prove(witness_path, compiled_model_path, pk_path, proof_path, proof_type="single", srs_path=srs_path)
    print(f"Proof generated and saved to {proof_path}")

    # 7. Verify locally
    result = ezkl.verify(proof_path, settings_path, vk_path, srs_path)
    print(f"Proof verification result: {result}")

if __name__ == "__main__":
    asyncio.run(generate_zk_proof())