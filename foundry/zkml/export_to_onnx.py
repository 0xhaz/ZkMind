import torch
import torch.nn as nn
from torchvision import transforms

class MNISTClassifier(nn.Module):
    def __init__(self):
        super(MNISTClassifier, self).__init__()
        self.conv1 = nn.Conv2d(1, 16, kernel_size=3, stride=1, padding=1)
        self.relu = nn.ReLU()
        self.pool = nn.MaxPool2d(kernel_size=2, stride=2)
        self.conv2 = nn.Conv2d(16, 32, kernel_size=3, stride=1, padding=1)
        self.fc1 = nn.Linear(32 * 7 * 7, 128)
        self.fc2 = nn.Linear(128, 10)

    def forward(self, x):
        x = self.pool(self.relu(self.conv1(x)))
        x = self.pool(self.relu(self.conv2(x)))
        x = x.view(-1, 32 * 7 * 7)
        x = self.relu(self.fc1(x))
        x = self.fc2(x)
        return x

device = torch.device("cpu")
model = MNISTClassifier().to(device)
model.load_state_dict(torch.load("../ai/models/mnist.pth", map_location=device))
model.eval()

dummy_input = torch.randn(1, 1, 28, 28).to(device)  # Correct shape
onnx_path = "../zkml/mnist.onnx"
torch.onnx.export(model, dummy_input, onnx_path, input_names=["input"], output_names=["output"], opset_version=11)
print(f"Model exported to {onnx_path}")