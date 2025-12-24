"""
Converted from CellProfiler: FillObjects
Original: fillobjects
"""

import numpy as np
from typing import Tuple
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

@numpy(contract=ProcessingContract.PURE_2D)
def fill_objects(
    image: np.ndarray,
    mode: str = "holes",
    diameter: float = 64.0
) -> np.ndarray:
    """
    Fills holes in objects or computes convex hulls for objects in a label image.
    
    Args:
        image: Label image (H, W) where 0 is background and integers are object IDs.
        mode: Either "holes" to fill internal holes or "convex hull" to fill the convex hull of each object.
        diameter: Maximum hole size to fill (only used in "holes" mode).
        
    Returns:
        np.ndarray: Processed label image.
    """
    from skimage.morphology import remove_small_holes, convex_hull_object
    
    if image.max() == 0:
        return image

    if mode.lower() == "holes":
        # CellProfiler's fill_object_holes typically uses area-based filling.
        # Diameter is converted to area: pi * (d/2)^2
        area_threshold = np.pi * ((diameter / 2.0) ** 2)
        
        # We process each object ID to ensure we don't merge distinct objects
        # via background hole filling.
        output_labels = np.zeros_like(image)
        for obj_id in np.unique(image):
            if obj_id == 0:
                continue
            mask = (image == obj_id)
            filled_mask = remove_small_holes(mask, area_threshold=area_threshold)
            output_labels[filled_mask] = obj_id
        return output_labels

    elif mode.lower() in ("convex hull", "convex_hull"):
        # skimage.morphology.convex_hull_object computes the hull for each 
        # labeled object individually.
        return convex_hull_object(image).astype(image.dtype)

    else:
        raise ValueError(f"Mode '{mode}' is not supported. Available modes are: 'holes' and 'convex hull'.")