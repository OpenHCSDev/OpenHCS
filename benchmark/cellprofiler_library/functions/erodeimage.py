"""
Converted from CellProfiler: ErodeImage
Original: erode_image
"""

import numpy as np
from enum import Enum
from typing import Union, Tuple
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

class StructuringElementShape(Enum):
    DISK = "disk"
    SQUARE = "square"
    DIAMOND = "diamond"
    OCTAGON = "octagon"
    STAR = "star"

@numpy(contract=ProcessingContract.PURE_2D)
def erode_image(
    image: np.ndarray,
    shape: StructuringElementShape = StructuringElementShape.DISK,
    size: int = 3
) -> np.ndarray:
    """
    Apply morphological erosion to an image using a specified structuring element.
    
    Args:
        image: Input 2D image slice (H, W).
        shape: The shape of the structuring element (disk, square, diamond, etc.).
        size: The radius or size parameter for the structuring element.
        
    Returns:
        np.ndarray: The eroded image.
    """
    from skimage import morphology
    import scipy.ndimage as ndimage

    # Generate structuring element based on shape
    if shape == StructuringElementShape.DISK:
        selem = morphology.disk(size)
    elif shape == StructuringElementShape.SQUARE:
        selem = morphology.square(size * 2 + 1)
    elif shape == StructuringElementShape.DIAMOND:
        selem = morphology.diamond(size)
    elif shape == StructuringElementShape.OCTAGON:
        # Octagon requires two parameters in skimage, approximating with disk if not available
        selem = morphology.octagon(size, size // 2) if hasattr(morphology, 'octagon') else morphology.disk(size)
    elif shape == StructuringElementShape.STAR:
        selem = morphology.star(size)
    else:
        selem = morphology.disk(size)

    # Perform erosion
    # For grayscale images, this is a local minimum filter
    # For binary images, this is standard morphological erosion
    if image.dtype == bool:
        return ndimage.binary_erosion(image, structure=selem).astype(bool)
    else:
        return ndimage.grey_erosion(image, footprint=selem)