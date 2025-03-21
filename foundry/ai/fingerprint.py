import hashlib
import os

# Path to the saved model
model_path = "./models/mnist.pth"

# Check if the model file exists
if not os.path.exists(model_path):
    raise FileNotFoundError(f"Model file not found at {model_path}")

# Function to compute SHA-256 hash of a file
def compute_file_hash(file_path):
    sha256_hash = hashlib.sha256()
    with open(file_path, "rb") as f:
        # Read the file in chunks to handle large files efficiently
        for byte_block in iter(lambda: f.read(4096), b""):
            sha256_hash.update(byte_block)
    return sha256_hash.hexdigest()

# Generate the fingerprint
try:
    fingerprint = compute_file_hash(model_path)
    print(f"Model Fingerprint (SHA-256): {fingerprint}")
    print(f"Fingerprint length: {len(fingerprint)} characters")

    # Optionally save the fingerprint to a file for later use
    with open("./models/mnist_fingerprint.txt", "w") as f:
        f.write(fingerprint)
    print("Fingerprint saved to ./models/mnist_fingerprint.txt")
except Exception as e:
    print(f"Error generating fingerprint: {e}")