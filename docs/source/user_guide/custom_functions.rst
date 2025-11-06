Creating Custom Functions
=========================

OpenHCS allows you to create custom processing functions directly in the GUI without modifying the codebase. Custom functions are automatically integrated into the function registry and available alongside standard library functions.

**Why This Matters**: Every microscopy workflow has unique processing needs. Instead of requesting features or forking the codebase, you can create custom functions in minutes with full GPU acceleration support.

Quick Start (5 Minutes)
------------------------

**1. Open the Function Selector Dialog**

.. code-block:: bash

   # From Pipeline Editor or any interface with function selection
   # Click "Add Function" or similar button to open Function Selector Dialog

**2. Click "Custom Function" button**

The code editor opens with a template for creating custom functions.

**3. Edit the template**

.. code-block:: python

   from openhcs.core.memory.decorators import numpy
   import numpy as np

   @numpy
   def my_custom_function(image, scale: float = 1.0, offset: float = 0.0):
       """
       Custom image processing function using NumPy.

       Args:
           image: Input image as 3D numpy array (C, Y, X)
           scale: Scaling factor to multiply image values
           offset: Offset to add after scaling

       Returns:
           Processed image as 3D numpy array (C, Y, X)
       """
       # Your processing code here
       processed = image * scale + offset
       return processed

**4. Save and register**

Save the file to automatically register the function. It now appears in the function selector alongside standard functions.

**5. Use in pipelines**

Your custom function is available in all function selectors throughout OpenHCS:

- Function Pattern Editor
- Pipeline Editor
- Experimental Analysis configurations
- Anywhere functions can be selected

Basic Custom Functions
----------------------

**Simple Thresholding Function**

.. code-block:: python

   from openhcs.core.memory.decorators import numpy
   import numpy as np

   @numpy
   def adaptive_threshold(image, percentile: float = 75.0):
       """
       Apply adaptive thresholding based on percentile.

       Args:
           image: Input image (C, Y, X)
           percentile: Percentile value for threshold (0-100)

       Returns:
           Thresholded binary image
       """
       threshold = np.percentile(image, percentile)
       return (image > threshold).astype(image.dtype)

**Linear Intensity Adjustment**

.. code-block:: python

   from openhcs.core.memory.decorators import numpy
   import numpy as np

   @numpy
   def linear_adjustment(image, min_out: float = 0.0, max_out: float = 1.0):
       """
       Linear intensity rescaling to specified range.

       Args:
           image: Input image (C, Y, X)
           min_out: Minimum output value
           max_out: Maximum output value

       Returns:
           Rescaled image
       """
       # Normalize to [0, 1]
       img_min, img_max = image.min(), image.max()
       normalized = (image - img_min) / (img_max - img_min + 1e-7)

       # Scale to output range
       return normalized * (max_out - min_out) + min_out

**Background Subtraction**

.. code-block:: python

   from openhcs.core.memory.decorators import numpy
   import numpy as np
   from scipy import ndimage

   @numpy
   def rolling_ball_background(image, radius: int = 50):
       """
       Remove background using rolling ball algorithm.

       Args:
           image: Input image (C, Y, X)
           radius: Radius of rolling ball in pixels

       Returns:
           Background-subtracted image
       """
       # Estimate background with maximum filter
       background = ndimage.maximum_filter(image, size=radius)

       # Subtract background
       return np.maximum(image - background, 0)

GPU-Accelerated Functions
--------------------------

**CuPy GPU Function**

.. code-block:: python

   from openhcs.core.memory.decorators import cupy
   import cupy as cp

   @cupy
   def gpu_median_filter(image, kernel_size: int = 3):
       """
       GPU-accelerated median filter using CuPy.

       Args:
           image: Input image (C, Y, X) as CuPy array
           kernel_size: Size of median filter kernel

       Returns:
           Filtered image (C, Y, X) as CuPy array

       Notes:
           Requires CUDA-compatible GPU
       """
       from cupyx.scipy import ndimage as cp_ndimage

       # Apply median filter to each channel
       filtered = cp.empty_like(image)
       for c in range(image.shape[0]):
           filtered[c] = cp_ndimage.median_filter(
               image[c],
               size=kernel_size
           )

       return filtered

**PyTorch Neural Network Function**

.. code-block:: python

   from openhcs.core.memory.decorators import torch
   import torch
   import torch.nn.functional as F

   @torch
   def denoise_with_net(image, strength: float = 0.1):
       """
       Simple denoising using PyTorch operations.

       Args:
           image: Input image (C, Y, X) as torch tensor
           strength: Denoising strength (0-1)

       Returns:
           Denoised image (C, Y, X) as torch tensor
       """
       # Add batch dimension
       x = image.unsqueeze(0)  # (1, C, Y, X)

       # Apply Gaussian blur as simple denoising
       kernel_size = int(strength * 10) * 2 + 1
       x = F.avg_pool2d(
           x,
           kernel_size=kernel_size,
           stride=1,
           padding=kernel_size//2
       )

       # Remove batch dimension
       return x.squeeze(0)  # (C, Y, X)

Advanced Features
-----------------

**Returning Metadata**

Custom functions can return metadata alongside the processed image:

.. code-block:: python

   from openhcs.core.memory.decorators import numpy
   import numpy as np

   @numpy
   def analyze_and_process(image, threshold: float = 0.5):
       """
       Process image and return analysis metadata.

       Args:
           image: Input image (C, Y, X)
           threshold: Threshold value

       Returns:
           Tuple of (processed_image, metadata_dict)
       """
       # Process image
       binary = image > threshold

       # Calculate statistics
       metadata = {
           "mean_intensity": float(np.mean(image)),
           "threshold_used": threshold,
           "percent_above_threshold": float(np.mean(binary) * 100),
           "max_intensity": float(np.max(image)),
       }

       return binary.astype(image.dtype), metadata

**Multi-Channel Processing**

Process each channel differently based on channel index:

.. code-block:: python

   from openhcs.core.memory.decorators import numpy
   import numpy as np

   @numpy
   def channel_specific_processing(
       image,
       channel_scales: str = "1.0,1.2,0.8"
   ):
       """
       Apply different scaling to each channel.

       Args:
           image: Input image (C, Y, X)
           channel_scales: Comma-separated scale factors for each channel

       Returns:
           Processed image with per-channel scaling
       """
       # Parse scale factors
       scales = [float(s.strip()) for s in channel_scales.split(',')]

       # Apply per-channel scaling
       result = image.copy()
       for c, scale in enumerate(scales[:image.shape[0]]):
           result[c] = result[c] * scale

       return result

**Conditional Processing**

Apply different algorithms based on image properties:

.. code-block:: python

   from openhcs.core.memory.decorators import numpy
   import numpy as np
   from scipy import ndimage

   @numpy
   def adaptive_processing(image, auto_detect: bool = True):
       """
       Choose processing method based on image characteristics.

       Args:
           image: Input image (C, Y, X)
           auto_detect: Automatically select method based on image stats

       Returns:
           Processed image
       """
       if auto_detect:
           # Detect if image is high or low contrast
           contrast = np.std(image)

           if contrast > 0.2:
               # High contrast: simple threshold
               threshold = np.mean(image)
               return (image > threshold).astype(image.dtype)
           else:
               # Low contrast: enhance first
               enhanced = (image - image.min()) / (image.max() - image.min())
               return ndimage.gaussian_filter(enhanced, sigma=1.0)
       else:
           # Default processing
           return ndimage.gaussian_filter(image, sigma=1.0)

Function Requirements
---------------------

All custom functions must follow these requirements:

**1. First Parameter Must Be Named 'image'**

.. code-block:: python

   # ✅ CORRECT
   @numpy
   def my_func(image, param1, param2):
       return image

   # ❌ INCORRECT - will fail validation
   @numpy
   def my_func(img, param1, param2):  # Wrong parameter name
       return img

**2. Must Have Memory Type Decorator**

.. code-block:: python

   # ✅ CORRECT
   from openhcs.core.memory.decorators import numpy

   @numpy
   def my_func(image):
       return image

   # ❌ INCORRECT - will fail validation
   def my_func(image):  # Missing decorator
       return image

**3. Must Process 3D Arrays (C, Y, X)**

.. code-block:: python

   # Input: 3D array where C=channels, Y=height, X=width
   # Output: Must be 3D array with same shape or compatible shape

   @numpy
   def my_func(image):
       # image.shape is (C, Y, X)
       assert image.ndim == 3, "Expected 3D array"

       # Process each channel
       for c in range(image.shape[0]):
           # Process image[c] which is 2D (Y, X)
           pass

       return processed_image  # Must be 3D (C, Y, X)

**4. Should Include Docstring**

.. code-block:: python

   @numpy
   def my_func(image, threshold: float = 0.5):
       """
       Brief description of what the function does.

       Args:
           image: Input image as 3D array (C, Y, X)
           threshold: Description of this parameter

       Returns:
           Processed image as 3D array (C, Y, X)

       Notes:
           Optional additional information
       """
       return processed_image

Memory Type Selection
---------------------

Choose the appropriate memory type decorator based on your needs:

**NumPy (CPU)**

.. code-block:: python

   from openhcs.core.memory.decorators import numpy

   @numpy
   def cpu_function(image):
       """Runs on CPU, works everywhere."""
       import numpy as np
       return np.array(image) * 2

**Best for**: Universal compatibility, testing, small images

**CuPy (CUDA GPU)**

.. code-block:: python

   from openhcs.core.memory.decorators import cupy

   @cupy
   def gpu_function(image):
       """Runs on NVIDIA GPU."""
       import cupy as cp
       return cp.array(image) * 2

**Best for**: Fast processing on NVIDIA GPUs, large images

**PyTorch (CPU/GPU)**

.. code-block:: python

   from openhcs.core.memory.decorators import torch

   @torch
   def torch_function(image):
       """Runs on CPU or GPU automatically."""
       import torch
       return image * 2

**Best for**: Deep learning operations, automatic device selection

**pyclesperanto (OpenCL GPU)**

.. code-block:: python

   from openhcs.core.memory.decorators import pyclesperanto

   @pyclesperanto
   def opencl_function(image):
       """Runs on OpenCL-compatible GPUs."""
       import pyclesperanto_prototype as cle
       return cle.multiply_image_and_scalar(image, scalar=2)

**Best for**: Cross-platform GPU (AMD, Intel, NVIDIA)

Managing Custom Functions
--------------------------

**List Custom Functions**

.. code-block:: python

   from openhcs.processing.custom_functions import CustomFunctionManager

   manager = CustomFunctionManager()
   functions = manager.list_custom_functions()

   for func_info in functions:
       print(f"Name: {func_info.name}")
       print(f"Memory Type: {func_info.memory_type}")
       print(f"File: {func_info.file_path}")
       print(f"Doc: {func_info.doc[:100]}...")
       print()

**Delete Custom Function**

.. code-block:: python

   from openhcs.processing.custom_functions import CustomFunctionManager

   manager = CustomFunctionManager()
   success = manager.delete_custom_function('my_old_function')

   if success:
       print("Function deleted successfully")
   else:
       print("Function not found")

**Reload Custom Functions**

.. code-block:: python

   from openhcs.processing.custom_functions import CustomFunctionManager

   manager = CustomFunctionManager()
   count = manager.load_all_custom_functions()

   print(f"Loaded {count} custom functions")

Storage Location
----------------

Custom functions are stored in your user data directory:

**Linux/macOS**: ``~/.local/share/openhcs/custom_functions/``

**Windows**: ``%LOCALAPPDATA%\openhcs\custom_functions\``

Each function is saved as a separate ``.py`` file:

.. code-block:: text

   ~/.local/share/openhcs/custom_functions/
   ├── my_threshold_function.py
   ├── custom_blur.py
   └── intensity_normalization.py

**Auto-Loading**: Custom functions are automatically loaded when OpenHCS starts.

**Backup**: Copy this directory to backup your custom functions.

**Sharing**: Share ``.py`` files with colleagues to distribute custom functions.

Common Patterns
---------------

**Pattern 1: Parameter-Based Processing**

.. code-block:: python

   @numpy
   def configurable_filter(image, method: str = "gaussian"):
       """Switch between different filtering methods."""
       import numpy as np
       from scipy import ndimage

       if method == "gaussian":
           return ndimage.gaussian_filter(image, sigma=1.0)
       elif method == "median":
           return ndimage.median_filter(image, size=3)
       elif method == "mean":
           return ndimage.uniform_filter(image, size=3)
       else:
           return image  # No filtering

**Pattern 2: Multi-Step Processing**

.. code-block:: python

   @numpy
   def preprocessing_pipeline(
       image,
       normalize: bool = True,
       denoise: bool = True,
       enhance: bool = True
   ):
       """Apply multiple preprocessing steps."""
       import numpy as np
       from scipy import ndimage

       result = image.copy()

       if normalize:
           result = (result - result.min()) / (result.max() - result.min())

       if denoise:
           result = ndimage.gaussian_filter(result, sigma=0.5)

       if enhance:
           result = result ** 0.5  # Gamma correction

       return result

**Pattern 3: Statistical Analysis**

.. code-block:: python

   @numpy
   def analyze_intensity(image):
       """Compute intensity statistics and normalize."""
       import numpy as np

       # Calculate statistics
       mean_val = np.mean(image)
       std_val = np.std(image)

       # Z-score normalization
       normalized = (image - mean_val) / (std_val + 1e-7)

       # Return with metadata
       metadata = {
           "original_mean": float(mean_val),
           "original_std": float(std_val),
           "min_value": float(np.min(image)),
           "max_value": float(np.max(image)),
       }

       return normalized, metadata

Troubleshooting
---------------

**Error: "No valid functions found with memory type decorators"**

Solution: Ensure your function has a decorator like ``@numpy``, ``@cupy``, etc.

.. code-block:: python

   # Add the decorator
   from openhcs.core.memory.decorators import numpy

   @numpy  # ← Add this line
   def my_function(image):
       return image

**Error: "First parameter is 'img', but must be 'image'"**

Solution: Rename the first parameter to ``image``:

.. code-block:: python

   # Change this:
   def my_function(img, threshold):
       return img > threshold

   # To this:
   def my_function(image, threshold):
       return image > threshold

**Error: "Dangerous import detected: 'os'"**

Solution: Remove dangerous imports. Use only processing libraries:

.. code-block:: python

   # ❌ Don't import these
   import os
   import subprocess
   import sys

   # ✅ Use these instead
   import numpy as np
   from scipy import ndimage
   import skimage

**Function Not Appearing in UI**

Solution: Check that the function was registered successfully:

.. code-block:: python

   from openhcs.processing.custom_functions import CustomFunctionManager

   manager = CustomFunctionManager()
   functions = manager.list_custom_functions()

   # Your function should appear in this list
   for func in functions:
       print(func.name)

If missing, try re-registering or check the logs for errors.

Best Practices
--------------

**1. Start Simple**

Begin with simple functions and add complexity as needed:

.. code-block:: python

   # Start with this
   @numpy
   def my_filter(image, sigma: float = 1.0):
       from scipy import ndimage
       return ndimage.gaussian_filter(image, sigma=sigma)

   # Not this (too complex for first attempt)
   @numpy
   def complex_pipeline(image, ...15 parameters...):
       # Complex multi-step processing
       ...

**2. Test with Small Images First**

Test your function with small test images before running on full datasets.

**3. Include Type Hints**

Add type hints to parameters for better documentation:

.. code-block:: python

   @numpy
   def my_function(
       image,
       threshold: float = 0.5,  # Type hint
       mode: str = "binary"      # Type hint
   ):
       ...

**4. Return Metadata for Analysis**

Include useful statistics in metadata return:

.. code-block:: python

   @numpy
   def process_and_analyze(image):
       processed = ...
       metadata = {
           "metric1": value1,
           "metric2": value2,
       }
       return processed, metadata

**5. Handle Edge Cases**

Check for empty images, invalid parameters, etc.:

.. code-block:: python

   @numpy
   def safe_function(image, threshold: float = 0.5):
       import numpy as np

       # Handle empty images
       if image.size == 0:
           return image

       # Clip threshold to valid range
       threshold = np.clip(threshold, 0.0, 1.0)

       # Process
       return image > threshold

Next Steps
----------

**Learn More**:

- :doc:`../architecture/custom_function_registration_system` - Technical architecture
- :doc:`../architecture/function_registry_system` - Function registry system
- :doc:`../architecture/memory_type_system` - Memory type decorators

**Advanced Topics**:

- Creating custom memory type decorators
- Integrating with external libraries
- Performance optimization for GPU functions
- Contributing custom functions to OpenHCS

**Get Help**:

- Check GitHub issues for similar questions
- Review example custom functions in the documentation
- Ask on the OpenHCS community forum
