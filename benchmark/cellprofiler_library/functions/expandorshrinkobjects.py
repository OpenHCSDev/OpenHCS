"""
Converted from CellProfiler: ExpandOrShrinkObjects
Original: expand_or_shrink_objects
"""

import numpy as np
from enum import Enum
from typing import Tuple, Optional
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

class ExpandShrinkMode(Enum):
    EXPAND_DEFINED = "expand_defined_pixels"
    EXPAND_INFINITE = "expand_infinite"
    SHRINK_DEFINED = "shrink_defined_pixels"
    SHRINK_TO_POINT = "shrink_to_point"
    ADD_DIVIDING_LINES = "add_dividing_lines"
    DESPUR = "despur"
    SKELETONIZE = "skeletonize"

@numpy(contract=ProcessingContract.PURE_2D)
def expand_or_shrink_objects(
    image: np.ndarray,
    mode: ExpandShrinkMode = ExpandShrinkMode.EXPAND_DEFINED,
    iterations: int = 1,
    fill_holes: bool = False
) -> np.ndarray:
    """
    Expand or shrink objects (labels) in an image.
    
    Args:
        image: Label image (H, W)
        mode: Operation mode (expand, shrink, skeletonize, etc.)
        iterations: Number of pixels to expand or shrink
        fill_holes: Whether to fill holes during shrinking
    """
    from scipy.ndimage import binary_dilation, binary_erosion, distance_transform_edt
    from skimage.segmentation import watershed, expand_labels
    from skimage.morphology import skeletonize as sk_skeletonize
    from skimage.morphology import thin

    labels = image.astype(np.int32)
    
    if mode == ExpandShrinkMode.EXPAND_DEFINED:
        # Expand objects by a defined number of pixels without merging
        return expand_labels(labels, distance=iterations)

    elif mode == ExpandShrinkMode.EXPAND_INFINITE:
        # Expand objects until they touch or reach image edge
        mask = labels > 0
        # Use watershed to expand labels into the background
        distance = distance_transform_edt(~mask)
        return watershed(distance, labels)

    elif mode == ExpandShrinkMode.SHRINK_DEFINED:
        # Shrink objects by a defined number of pixels
        # We process label by label to avoid merging/disappearing issues in simple erosion
        output = np.zeros_like(labels)
        for obj_id in np.unique(labels):
            if obj_id == 0: continue
            obj_mask = labels == obj_id
            shrunk = binary_erosion(obj_mask, iterations=iterations)
            output[shrunk] = obj_id
        return output

    elif mode == ExpandShrinkMode.SHRINK_TO_POINT:
        # Shrink objects to a single point (ultimate erosion)
        # Approximate using distance transform peaks
        output = np.zeros_like(labels)
        for obj_id in np.unique(labels):
            if obj_id == 0: continue
            obj_mask = labels == obj_id
            dist = distance_transform_edt(obj_mask)
            max_dist = np.max(dist)
            # Find a single pixel at the maximum distance
            coords = np.argwhere(dist == max_dist)
            if len(coords) > 0:
                y, x = coords[0]
                output[y, x] = obj_id
        return output

    elif mode == ExpandShrinkMode.ADD_DIVIDING_LINES:
        # Shrink objects by 1 pixel to create background lines between touching objects
        mask = labels > 0
        eroded = binary_erosion(mask, iterations=1)
        return (labels * eroded).astype(np.int32)

    elif mode == ExpandShrinkMode.DESPUR:
        # Remove small branches (spurs) from skeletonized objects
        # Implemented via thinning with limited iterations
        return thin(labels > 0, max_num_iter=iterations).astype(np.int32) * labels

    elif mode == ExpandShrinkMode.SKELETONIZE:
        # Reduce objects to 1-pixel wide skeletons
        output = np.zeros_like(labels)
        for obj_id in np.unique(labels):
            if obj_id == 0: continue
            obj_mask = labels == obj_id
            skel = sk_skeletonize(obj_mask)
            output[skel] = obj_id
        return output

    return labels