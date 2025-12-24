"""
Converted from CellProfiler: ErodeObjects
Original: erode_objects
"""

import numpy as np
from typing import Tuple, Union
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_outputs

class StructuringElementShape(Enum):
    DISK = "disk"
    SQUARE = "square"
    DIAMOND = "diamond"

@numpy(contract=ProcessingContract.PURE_2D)
@special_outputs("eroded_labels")
def erode_objects(
    image: np.ndarray,
    shape: StructuringElementShape = StructuringElementShape.DISK,
    size: int = 1,
    preserve_midpoints: bool = False,
    relabel_objects: bool = False
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Erode objects based on a structuring element.
    
    Args:
        image: Input label image (H, W).
        shape: Shape of the structuring element.
        size: Size/radius of the structuring element.
        preserve_midpoints: If True, ensures objects are not completely eroded away.
        relabel_objects: If True, relabels resulting objects.
        
    Returns:
        Tuple of (original_image, eroded_labels)
    """
    from skimage.morphology import disk, square, diamond, erosion, label
    from skimage.measure import regionprops
    
    # 1. Create structuring element
    if shape == StructuringElementShape.DISK:
        selem = disk(size)
    elif shape == StructuringElementShape.SQUARE:
        selem = square(size * 2 + 1)
    elif shape == StructuringElementShape.DIAMOND:
        selem = diamond(size)
    else:
        selem = disk(size)

    # 2. Perform erosion
    # We iterate through unique labels to avoid merging objects during erosion
    # if they are adjacent.
    eroded_labels = np.zeros_like(image)
    unique_labels = np.unique(image)
    unique_labels = unique_labels[unique_labels != 0]

    for obj_id in unique_labels:
        mask = (image == obj_id)
        eroded_mask = erosion(mask, selem)
        
        if preserve_midpoints and not np.any(eroded_mask):
            # If object disappeared and we want to preserve midpoints,
            # find the centroid or a point within the original mask
            coords = np.argwhere(mask)
            if len(coords) > 0:
                midpoint = coords[len(coords) // 2]
                eroded_mask[midpoint[0], midpoint[1]] = True
        
        eroded_labels[eroded_mask] = obj_id

    # 3. Relabel if requested
    if relabel_objects:
        eroded_labels = label(eroded_labels > 0).astype(image.dtype)

    return image, eroded_labels