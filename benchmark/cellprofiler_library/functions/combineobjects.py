"""
Converted from CellProfiler: CombineObjects
Original: combineobjects
"""

import numpy as np
from enum import Enum
from typing import Tuple
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

class CombineMethod(Enum):
    MERGE = "merge"
    PRESERVE = "preserve"
    DISCARD = "discard"
    SEGMENT = "segment"

@numpy(contract=ProcessingContract.FLEXIBLE)
def combine_objects(
    image: np.ndarray,
    method: CombineMethod = CombineMethod.MERGE
) -> np.ndarray:
    """
    Combines two sets of objects (labels) using various logical methods.
    
    Args:
        image: Shape (2, H, W) or (2, D, H, W) - two label images stacked along dim 0.
        method: The method used to combine objects.
            - merge: Objects in labels_x and labels_y that overlap are merged.
            - preserve: Keeps objects in labels_x that overlap with objects in labels_y.
            - discard: Discards objects in labels_x that overlap with objects in labels_y.
            - segment: Segments labels_x using labels_y as seeds/markers.
            
    Returns:
        np.ndarray: The combined label image.
    """
    from skimage.segmentation import watershed
    from skimage.measure import label

    # Unstack inputs from dimension 0
    labels_x = image[0].astype(np.int32)
    labels_y = image[1].astype(np.int32)

    method_val = method.value if isinstance(method, CombineMethod) else method.lower()

    if method_val == "merge":
        # Objects in X and Y that overlap are joined into a single object
        # We use a connected components approach on the union of masks
        mask = (labels_x > 0) | (labels_y > 0)
        return label(mask).astype(np.int32)

    elif method_val == "preserve":
        # Keep objects in labels_x that have any overlap with labels_y
        overlap_mask = (labels_x > 0) & (labels_y > 0)
        overlapping_labels = np.unique(labels_x[overlap_mask])
        
        output = np.zeros_like(labels_x)
        # Filter to keep only labels found in the overlap
        keep_mask = np.isin(labels_x, overlapping_labels[overlapping_labels > 0])
        output[keep_mask] = labels_x[keep_mask]
        return output

    elif method_val == "discard":
        # Discard objects in labels_x that have any overlap with labels_y
        overlap_mask = (labels_x > 0) & (labels_y > 0)
        overlapping_labels = np.unique(labels_x[overlap_mask])
        
        output = labels_x.copy()
        # Remove labels found in the overlap
        discard_mask = np.isin(labels_x, overlapping_labels[overlapping_labels > 0])
        output[discard_mask] = 0
        return output

    elif method_val == "segment":
        # Use labels_y as seeds to segment the mask defined by labels_x
        mask = labels_x > 0
        # Watershed requires seeds (labels_y) and a mask (labels_x)
        # We use the inverse of labels_x as the "elevation" (0 inside, 1 outside)
        # so that the watershed fills the existing objects.
        combined = watershed(
            image=-mask.astype(np.float32),
            markers=labels_y,
            mask=mask
        )
        return combined.astype(np.int32)

    else:
        raise ValueError(f"Unsupported method: {method_val}")