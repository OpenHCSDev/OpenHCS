"""
Converted from CellProfiler: MedianFilter
Original: medianfilter
"""

import numpy as np
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

@numpy(contract=ProcessingContract.PURE_2D)
def median_filter(
    image: np.ndarray,
    window_size: int = 3,
    mode: str = "reflect"
) -> np.ndarray:
    """
    Apply a median filter to the image.
    
    Args:
        image: Input image (H, W)
        window_size: The size of the window to use for the median filter. 
                    Default is 3 (3x3 window).
        mode: The mode parameter determines how the input array is extended 
              beyond its boundaries. Default is 'reflect'.
              
    Returns:
        Filtered image of shape (H, W)
    """
    from scipy.ndimage import median_filter as scipy_median_filter
    
    # Ensure window_size is an integer
    size = int(window_size)
    
    # scipy.ndimage.median_filter handles 2D arrays directly
    filtered_image = scipy_median_filter(
        image, 
        size=size, 
        mode=mode
    )
    
    return filtered_image.astype(image.dtype)