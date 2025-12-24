"""
Converted from CellProfiler: Gaussianfilter
Original: gaussianfilter
"""

import numpy as np
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

@numpy(contract=ProcessingContract.PURE_2D)
def gaussian_filter(
    image: np.ndarray,
    sigma: float = 1.0
) -> np.ndarray:
    """
    Apply a Gaussian filter to an image.
    
    Args:
        image: Input image slice (H, W).
        sigma: Standard deviation for Gaussian kernel.
        
    Returns:
        Filtered image (H, W).
    """
    from scipy.ndimage import gaussian_filter as scipy_gaussian
    
    # Ensure image is float for precise filtering
    if not np.issubdtype(image.dtype, np.floating):
        image = image.astype(np.float32)
        
    filtered_image = scipy_gaussian(image, sigma=sigma)
    
    return filtered_image