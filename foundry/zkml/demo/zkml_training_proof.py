import torch
import torch.nn as nn
import torch.optim as optim
import json
import os
import subprocess

# Define a simple neural network
class SimpleNN(nn.Module):
    def __init__(self):
        super(SimpleNN, self).__init__()
        self.fc1 = nn.Linear(2, 4)  # Input: 2 neurons, Hidden: 4 neurons
        self.fc2 = nn.Linear(4, 1)  # Output: 1 neuron

    def forward(self, x):
        x = torch.relu(self.fc1(x))
        x = torch.sigmoid(self.fc2(x))  # Sigmoid for binary classification
        return x

# Train the model (for demonstration purposes)
def train_model():
    model = SimpleNN()
    criterion = nn.BCELoss()  # Binary Cross-Entropy Loss
    optimizer = optim.Adam(model.parameters(), lr=0.01)

    X_train = torch.tensor([[0, 0], [0, 1], [1, 0], [1, 1]], dtype=torch.float32)
    y_train = torch.tensor([[0], [1], [1], [0]], dtype=torch.float32)

    for epoch in range(500):
        optimizer.zero_grad()
        outputs = model(X_train)
        loss = criterion(outputs, y_train)
        loss.backward()
        optimizer.step()

    return model, X_train, y_train

# Save the model parameters for ZK proof generation with batch size 4
def save_model(model):
    model_path = "zkml_model.onnx"
    dummy_input = torch.zeros(4, 2, dtype=torch.float32)  # Explicitly set batch size 4
    torch.onnx.export(
        model,
        dummy_input,
        model_path,
        export_params=True,
        opset_version=11,
        input_names=["input"],
        output_names=["output"],
        dynamic_axes=None,  # Ensure static batch size
    )
    print(f"✅ Model saved to {model_path} with batch size 4")
    return model_path

# Run an EZKL command and check for success
def run_ezkl_command(command, error_msg, ezkl_path="/Users/haz/.ezkl/ezkl"):
    print(f"Executing: {command}")
    result = subprocess.run(
        f"{ezkl_path} {command}",
        shell=True,
        capture_output=True,
        text=True
    )
    if result.returncode != 0:
        print(f"❌ {error_msg}")
        print(f"Command: {command}")
        print(f"Exit code: {result.returncode}")
        print(f"Standard output: {result.stdout}")
        print(f"Error output: {result.stderr}")
        print("Troubleshooting tips:")
        print(f"- Verify EZKL installation: `{ezkl_path} --version`")
        print(f"- Check model details: `{ezkl_path} table --model zkml_model.onnx`")
        print("- Validate settings: `cat zkml_settings.json`")
        raise RuntimeError(f"EZKL command failed: {command}")
    print(f"✅ {command.split()[0]} completed successfully")
    print(f"Output: {result.stdout}")
    return result

# Generate ZK proof using EZKL
def generate_zk_proof(model_path, input_data, ezkl_path="/Users/haz/.ezkl/ezkl"):
    compiled_model_path = "zkml_model.compiled"
    witness_path = "zkml_witness.json"
    proof_path = "zkml_proof.json"
    vk_path = "zkml_vk.key"
    pk_path = "zkml_pk.key"
    settings_path = "zkml_settings.json"
    input_path = "zkml_input.json"

    # Convert input data to JSON format with 2D array under "input_data" and "input"
    inputs = input_data.tolist()
    proof_config = {
        "input_data": inputs
    }
    with open(input_path, "w") as f:
        json.dump(proof_config, f)
    print(f"Input data saved to {input_path}")
    print(json.dumps(proof_config, indent=4))

    # Load and adapt the generated settings.json
    if os.path.exists("settings.json"):
        print("Using generated settings.json from ezkl gen-settings...")
        with open("settings.json", "r") as f:
            settings = json.load(f)
        settings["model"] = model_path
        settings["run_args"]["variables"] = [["batch_size", 4]]  # Match 4 XOR examples
        settings["model_instance_shapes"] = [[4, 2]]  # [batch_size, output_dim]
        settings["model_input_scales"] = [7]  # Explicitly set input scale
    else:
        settings = {
            "model": model_path,
            "run_args": {
                "logrows": 17,
                "scale": 7,
                "input_scale": 7,
                "param_scale": 7,
                "scale_rebase_multiplier": 10,
                "lookup_range": [-20, 20],
                "num_inner_cols": 2,
                "variables": [["batch_size", 4]],
                "bits": 16,
                "mode": "safe",
                "output_visibility": "Public",
                "param_visibility": "Private",
                "num_inner_cols": 2,
                "ignore_range_check_inputs_outputs": False,
                "rebase_frac_zero_constants": False
            },
            "model_instance_shapes": [[4, 2]],
            "model_input_scales": [7]
        }
    with open(settings_path, "w") as f:
        json.dump(settings, f)
    print(f"Settings saved to {settings_path}")

    # Step-by-step EZKL process with error checking
    try:
        print("Step: Compiling circuit...")
        if not os.path.exists(model_path):
            raise FileNotFoundError(f"Model file {model_path} not found")
        run_ezkl_command(
            f"compile-circuit --model {model_path} --settings-path {settings_path} --compiled-circuit {compiled_model_path}",
            "Failed to compile circuit",
            ezkl_path
        )

        print("Step: Setting up proving and verifying keys...")
        if not os.path.exists(compiled_model_path):
            raise FileNotFoundError(f"Compiled circuit {compiled_model_path} not found")
        run_ezkl_command(
            f"setup --compiled-circuit {compiled_model_path} --pk-path {pk_path} --vk-path {vk_path}",
            "Failed to setup proving/verifying keys",
            ezkl_path
        )

        print("Step: Generating witness...")
        if not os.path.exists(input_path):
            raise FileNotFoundError(f"Input file {input_path} not found")
        run_ezkl_command(
            f"gen-witness --compiled-circuit {compiled_model_path} --data {input_path} --output {witness_path}",
            "Failed to generate witness",
            ezkl_path
        )

        print("Step: Generating proof...")
        if not os.path.exists(witness_path):
            raise FileNotFoundError(f"Witness file {witness_path} not found")
        run_ezkl_command(
            f"prove --compiled-circuit {compiled_model_path} --witness {witness_path} --pk-path {pk_path} --proof-path {proof_path}",
            "Failed to generate proof",
            ezkl_path
        )

    except (RuntimeError, FileNotFoundError) as e:
        print(f"❌ Proof generation halted: {e}")
        return None

    print(f"ZKML Proof generated: {proof_path}")
    return proof_path

# Main function
if __name__ == "__main__":
    print("Training AI Model...")
    model, X_train, y_train = train_model()

    print("Saving Model...")
    model_path = save_model(model)

    print("Generating Zero-Knowledge Proof...")
    proof_path = generate_zk_proof(model_path, X_train)

    if proof_path:
        print("Proof generation completed! Stored in:", proof_path)
    else:
        print("Proof generation failed.")