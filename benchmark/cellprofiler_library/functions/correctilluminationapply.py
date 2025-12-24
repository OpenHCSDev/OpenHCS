"""
Converted from CellProfiler: CorrectIlluminationApply
Original: correct_illumination_apply
"""

import numpy as np
from typing import Tuple
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract


class IlluminationCorrectionMethod(Enum):
    DIVIDE = "divide"
    SUBTRACT = "subtract"


@numpy(contract=ProcessingContract.FLEXIBLE)
def correct_illumination_apply(
    image: np.ndarray,
    method: IlluminationCorrectionMethod = IlluminationCorrectionMethod.DIVIDE,
    truncate_low: bool = True,
    truncate_high: bool = True,
) -> np.ndarray:
    """
    Apply illumination correction to an image using a provided illumination function.
    
    This function corrects uneven illumination by either dividing or subtracting
    an illumination function from the input image.
    
    Args:
        image: Shape (2, H, W) - two images stacked:
               image[0] = image to correct
               image[1] = illumination function
        method: Method to apply correction - DIVIDE or SUBTRACT
        truncate_low: Set output values less than 0 equal to 0
        truncate_high: Set output values greater than 1 equal to 1
    
    Returns:
        Corrected image with shape (1, H, W)
    """
    # Unstack inputs from dimension 0
    image_pixels = image[0]  # (H, W) - image to correct
    illum_function = image[1]  # (H, W) - illumination function
    
    # Validate shapes match
    assert image_pixels.shape == illum_function.shape, \
        f"Input image shape {image_pixels.shape} and illumination function shape {illum_function.shape} must be equal"
    
    # Apply illumination correction
    if method == IlluminationCorrectionMethod.DIVIDE:
        # Avoid division by zero
        # Add small epsilon where illumination function is zero
        safe_illum = np.where(illum_function == 0, 1e-10, illum_function)
        output_pixels = image_pixels / safe_illum
    elif method == IlluminationCorrectionMethod.SUBTRACT:
        output_pixels = image_pixels - illum_function
    else:
        raise ValueError(f"Unhandled option for divide or subtract: {method.value}")
    
    # Optionally clip values
    if truncate_low:
        output_pixels = np.maximum(output_pixels, 0.0)
    if truncate_high:
        output_pixels = np.minimum(output_pixels, 1.0)
    
    # Return with shape (1, H, W) to maintain 3D convention
    return output_pixels[np.newaxis, ...].astype(np.float32)