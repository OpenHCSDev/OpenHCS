"""
Converted from CellProfiler: Opening
Morphological opening operation (erosion followed by dilation)
"""

import numpy as np
from typing import Literal
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract


@numpy(contract=ProcessingContract.PURE_2D)
def opening(
    image: np.ndarray,
    structuring_element: Literal["disk", "square", "diamond", "octagon", "star"] = "disk",
    size: int = 3,
) -> np.ndarray:
    """
    Apply morphological opening to an image.
    
    Opening is erosion followed by dilation. It removes small bright spots
    (noise) and smooths object boundaries while preserving object size.
    
    Args:
        image: Input image with shape (H, W)
        structuring_element: Shape of the structuring element.
            Options: "disk", "square", "diamond", "octagon", "star"
        size: Size of the structuring element (radius for disk, side length for square, etc.)
    
    Returns:
        Opened image with shape (H, W)
    """
    from skimage.morphology import (
        opening as skimage_opening,
        disk,
        square,
        diamond,
        octagon,
        star,
    )
    
    # Create structuring element based on type
    if structuring_element == "disk":
        selem = disk(size)
    elif structuring_element == "square":
        selem = square(size)
    elif structuring_element == "diamond":
        selem = diamond(size)
    elif structuring_element == "octagon":
        # octagon requires two parameters, use size for both
        selem = octagon(size, size)
    elif structuring_element == "star":
        selem = star(size)
    else:
        # Default to disk
        selem = disk(size)
    
    # Apply morphological opening
    result = skimage_opening(image, selem)
    
    return result.astype(image.dtype)