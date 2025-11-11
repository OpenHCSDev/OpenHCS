"""
Template system for custom function creation.

Provides starter code templates for different memory types (numpy, cupy, torch, etc.)
with proper imports, decorators, and docstring examples.

All functions follow OpenHCS contracts:
    - First parameter must be named 'image' (3D array: C, Y, X)
    - Must be decorated with memory type decorator (@numpy, @cupy, etc.)
    - Must return processed image (optionally with metadata dict)
"""

from typing import Dict

# Available memory types for custom functions
AVAILABLE_MEMORY_TYPES = ["numpy", "cupy", "torch", "tensorflow", "jax", "pyclesperanto"]


def get_default_template() -> str:
    """
    Get the default custom function template (numpy backend).

    Returns:
        Template string with numpy decorator and example function
    """
    return NUMPY_TEMPLATE


def get_template_for_memory_type(memory_type: str) -> str:
    """
    Get template for a specific memory type.

    Args:
        memory_type: One of 'numpy', 'cupy', 'torch', 'tensorflow', 'jax', 'pyclesperanto'

    Returns:
        Template string with appropriate decorator and imports

    Raises:
        ValueError: If memory_type is not recognized
    """
    template_map: Dict[str, str] = {
        'numpy': NUMPY_TEMPLATE,
        'cupy': CUPY_TEMPLATE,
        'torch': TORCH_TEMPLATE,
        'tensorflow': TENSORFLOW_TEMPLATE,
        'jax': JAX_TEMPLATE,
        'pyclesperanto': PYCLESPERANTO_TEMPLATE,
    }

    if memory_type not in template_map:
        raise ValueError(
            f"Unknown memory type: {memory_type}. "
            f"Must be one of: {', '.join(AVAILABLE_MEMORY_TYPES)}"
        )

    return template_map[memory_type]


# Template constants with proper typing and documentation

NUMPY_TEMPLATE = """from openhcs.core.memory.decorators import numpy
import numpy as np

@numpy
def my_custom_function(image, scale: float = 1.0, offset: float = 0.0):
    \"\"\"
    Custom image processing function using NumPy.

    Args:
        image: Input image as 3D numpy array (C, Y, X)
               C = channels, Y = height, X = width
        scale: Scaling factor to multiply image values
        offset: Offset to add after scaling

    Returns:
        Processed image as 3D numpy array (C, Y, X)

    Example:
        # Simple brightness adjustment
        result = my_custom_function(image, scale=1.2, offset=10)

    Notes:
        - First parameter MUST be named 'image'
        - Must be decorated with @numpy
        - Input and output must be 3D arrays (C, Y, X)
        - Return type can be: image_array OR (image_array, metadata_dict)
    \"\"\"
    # Your processing code here
    # Example: linear transformation
    processed = image * scale + offset

    # Optional: return metadata alongside image
    # metadata = {"mean_intensity": float(np.mean(processed))}
    # return processed, metadata

    return processed
"""


CUPY_TEMPLATE = """from openhcs.core.memory.decorators import cupy
import cupy as cp

@cupy
def my_custom_function(image, sigma: float = 1.0):
    \"\"\"
    Custom image processing function using CuPy (GPU-accelerated).

    Args:
        image: Input image as 3D cupy array (C, Y, X)
               C = channels, Y = height, X = width
        sigma: Gaussian blur sigma parameter

    Returns:
        Processed image as 3D cupy array (C, Y, X)

    Notes:
        - Requires CUDA-compatible GPU
        - First parameter MUST be named 'image'
        - Must be decorated with @cupy
        - Input and output must be 3D arrays (C, Y, X)
    \"\"\"
    # Your GPU processing code here
    # Example: simple thresholding
    threshold = cp.mean(image) + sigma * cp.std(image)
    processed = cp.where(image > threshold, image, 0)

    return processed
"""


TORCH_TEMPLATE = """from openhcs.core.memory.decorators import torch
import torch

@torch
def my_custom_function(image, kernel_size: int = 3):
    \"\"\"
    Custom image processing function using PyTorch.

    Args:
        image: Input image as 3D torch tensor (C, Y, X)
               C = channels, Y = height, X = width
        kernel_size: Size of processing kernel

    Returns:
        Processed image as 3D torch tensor (C, Y, X)

    Notes:
        - Can run on CPU or GPU (automatic device handling)
        - First parameter MUST be named 'image'
        - Must be decorated with @torch
        - Input and output must be 3D tensors (C, Y, X)
    \"\"\"
    # Your PyTorch processing code here
    # Example: max pooling followed by upsampling
    import torch.nn.functional as F

    # Add batch dimension for pooling
    x = image.unsqueeze(0)  # (1, C, Y, X)

    # Apply max pooling
    pooled = F.max_pool2d(x, kernel_size=kernel_size, stride=1, padding=kernel_size//2)

    # Remove batch dimension
    processed = pooled.squeeze(0)  # (C, Y, X)

    return processed
"""


TENSORFLOW_TEMPLATE = """from openhcs.core.memory.decorators import tensorflow
import tensorflow as tf

@tensorflow
def my_custom_function(image, strength: float = 0.5):
    \"\"\"
    Custom image processing function using TensorFlow.

    Args:
        image: Input image as 3D tensorflow tensor (C, Y, X)
               C = channels, Y = height, X = width
        strength: Processing strength parameter

    Returns:
        Processed image as 3D tensorflow tensor (C, Y, X)

    Notes:
        - First parameter MUST be named 'image'
        - Must be decorated with @tensorflow
        - Input and output must be 3D tensors (C, Y, X)
    \"\"\"
    # Your TensorFlow processing code here
    # Example: contrast adjustment
    mean = tf.reduce_mean(image)
    processed = (image - mean) * (1.0 + strength) + mean

    return processed
"""


JAX_TEMPLATE = """from openhcs.core.memory.decorators import jax
import jax.numpy as jnp

@jax
def my_custom_function(image, power: float = 2.0):
    \"\"\"
    Custom image processing function using JAX.

    Args:
        image: Input image as 3D jax array (C, Y, X)
               C = channels, Y = height, X = width
        power: Power transformation parameter

    Returns:
        Processed image as 3D jax array (C, Y, X)

    Notes:
        - JAX provides automatic differentiation and JIT compilation
        - First parameter MUST be named 'image'
        - Must be decorated with @jax
        - Input and output must be 3D arrays (C, Y, X)
    \"\"\"
    # Your JAX processing code here
    # Example: power transformation
    # Normalize to [0, 1] range
    img_min = jnp.min(image)
    img_max = jnp.max(image)
    normalized = (image - img_min) / (img_max - img_min + 1e-7)

    # Apply power transformation
    transformed = jnp.power(normalized, power)

    # Scale back to original range
    processed = transformed * (img_max - img_min) + img_min

    return processed
"""


PYCLESPERANTO_TEMPLATE = """from openhcs.core.memory.decorators import pyclesperanto
import pyclesperanto_prototype as cle

@pyclesperanto
def my_custom_function(image, radius: float = 2.0):
    \"\"\"
    Custom image processing function using pyclesperanto (GPU-accelerated).

    Args:
        image: Input image as 3D array compatible with pyclesperanto (C, Y, X)
               C = channels, Y = height, X = width
        radius: Radius for morphological operations

    Returns:
        Processed image as 3D array (C, Y, X)

    Notes:
        - Optimized for GPU execution via OpenCL
        - First parameter MUST be named 'image'
        - Must be decorated with @pyclesperanto
        - Input and output must be 3D arrays (C, Y, X)
    \"\"\"
    # Your pyclesperanto processing code here
    # Example: Gaussian blur using cle
    processed = cle.gaussian_blur(image, sigma_x=radius, sigma_y=radius, sigma_z=0)

    return processed
"""
