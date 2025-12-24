"""
Converted from CellProfiler: Opening
Original: opening
"""

import numpy as np
from typing import Tuple
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

@numpy(contract=ProcessingContract.PURE_2D)
def opening(
    image: np.ndarray,
    structuring_element_shape: str = "disk",
    structuring_element_size: int = 3
) -> np.ndarray:
    """
    Perform morphological opening on an image.
    
    Opening is erosion followed by dilation. It is used to remove small objects 
    and noise from the foreground while preserving the shape and size of larger 
    objects in the image.

    Args:
        image: Input image (H, W)
        structuring_element_shape: Shape of the structuring element ('disk', 'square', 'diamond', 'star')
        structuring_element_size: Radius or size of the structuring element in pixels
        
    Returns:
        np.ndarray: The opened image
    """
    from skimage import morphology

    # Generate structuring element
    if structuring_element_shape == "disk":
        selem = morphology.disk(structuring_element_size)
    elif structuring_element_shape == "square":
        selem = morphology.square(structuring_element_size * 2 + 1)
    elif structuring_element_shape == "diamond":
        selem = morphology.diamond(structuring_element_size)
    elif structuring_element_shape == "star":
        selem = morphology.star(structuring_element_size)
    else:
        # Default to disk if unknown shape provided
        selem = morphology.disk(structuring_element_size)

    # Perform opening
    # morphology.opening handles both binary and grayscale images
    result = morphology.opening(image, selem)

    return result