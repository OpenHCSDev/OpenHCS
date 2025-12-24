"""
Converted from CellProfiler: CorrectIlluminationApply
Original: correct_illumination_apply
"""

import numpy as np
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_inputs

class Method(Enum):
    DIVIDE = "Divide"
    SUBTRACT = "Subtract"

@numpy(contract=ProcessingContract.FLEXIBLE)
@special_inputs("illum_function")
def correct_illumination_apply(
    image: np.ndarray,
    illum_function: np.ndarray,
    method_divide_or_subtract: Method = Method.DIVIDE,
    truncate_low: bool = True,
    truncate_high: bool = True,
) -> np.ndarray:
    """
    Apply an illumination correction function to an image.
    
    Args:
        image: The input image to be corrected. Shape (D, H, W).
        illum_function: The illumination correction image. Shape (1, H, W) or (D, H, W).
        method_divide_or_subtract: Whether to divide or subtract the illumination function.
        truncate_low: If True, values less than 0 are set to 0.
        truncate_high: If True, values greater than 1 are set to 1.
        
    Returns:
        Corrected image of shape (D, H, W).
    """
    # Ensure illum_function matches spatial dimensions
    # If illum_function is (1, H, W) and image is (D, H, W), broadcasting handles it.
    
    if method_divide_or_subtract == Method.DIVIDE:
        # Avoid division by zero: CellProfiler typically handles this by 
        # setting output to 0 where the illumination function is 0.
        mask = illum_function == 0
        output_pixels = np.divide(image, illum_function, out=np.zeros_like(image), where=~mask)
    elif method_divide_or_subtract == Method.SUBTRACT:
        output_pixels = image - illum_function
    else:
        raise ValueError(f"Unhandled method: {method_divide_or_subtract}")

    if truncate_low:
        output_pixels = np.maximum(output_pixels, 0)
    
    if truncate_high:
        output_pixels = np.minimum(output_pixels, 1)

    return output_pixels