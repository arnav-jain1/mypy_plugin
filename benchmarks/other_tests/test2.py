import numpy as np
from typing_extensions import reveal_type
# Need rand, ones, np.array

# 1. Create input data (common in ML pipelines)
samples = np.random.randint(0, 256, size=(10, 32, 32, 3))  # 10 RGB images of 32x32
print("\n1. Raw image data:")
print("Type:", samples.dtype, "Shape:", samples.shape)

reveal_type(samples)

# 2. Normalize pixel values (common preprocessing)
normalized = samples / 255.0
print("\n2. After normalization:")
print("Type:", normalized.dtype, "Shape:", normalized.shape)

reveal_type(normalized)

# 3. Flatten images for a fully connected layer
flattened = normalized.reshape(5 * 2, -1)  # -1 infers the remaining dimension
print("\n3. After flattening:")
print("Type:", flattened.dtype, "Shape:", flattened.shape)

reveal_type(flattened)

# 4. Create and apply weights matrix (simulated neural network layer)
weights = np.random.normal(size=(3072, 512))
print("\n4. Weight matrix:")
print("Type:", weights.dtype, "Shape:", weights.shape)

reveal_type(weights)

# 5. Matrix multiplication (fully connected layer)
hidden_layer = flattened @ weights
print("\n5. After matrix multiplication:")
print("Type:", hidden_layer.dtype, "Shape:", hidden_layer.shape)

reveal_type(hidden_layer)

# # 6. Apply ReLU activation (common non-linearity)
# relu_output = np.maximum(hidden_layer, 0)
# print("\n6. After ReLU activation:")
# print("Type:", relu_output.dtype, "Shape:", relu_output.shape)

# reveal_type(relu_output)


# # 8. Final reshape for output
# output = relu_output.reshape(10, 16, 32)  # Reshape for further processing
# print("\n8. Final reshaped output:")
# print("Type:", output.dtype, "Shape:", output.shape)


# reveal_type(output)