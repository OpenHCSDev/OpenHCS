"""
Converted from CellProfiler: Closing
Original: closing
"""

import numpy as np
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

@numpy(contract=ProcessingContract.PURE_2D)
def closing(
    image: np.ndarray,
    structuring_element_shape: str = "disk",
    structuring_element_size: int = 3
) -> np.ndarray:
    """
    Perform morphological closing on an image.
    
    Args:
        image: Input image (H, W)
        structuring_element_shape: Shape of the structuring element ('disk', 'square', 'diamond')
        structuring_element_size: Radius or size of the structuring element
        
    Returns:
        np.ndarray: The closed image
    """
    from skimage import morphology

    # Generate structuring element
    if structuring_element_shape == "disk":
        selem = morphology.disk(structuring_element_size)
    elif structuring_element_shape == "square":
        selem = morphology.square(structuring_element_size)
    elif structuring_element_shape == "diamond":
        selem = morphology.diamond(structuring_element_size)
    else:
        # Default to disk if unknown shape provided
        selem = morphology.disk(structuring_element_size)

    # Perform closing
    # Note: skimage.morphology.closing works on both grayscale and binary
    closed_image = morphology.closing(image, selem)

    return closed_image