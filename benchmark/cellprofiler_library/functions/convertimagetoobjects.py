"""
Converted from CellProfiler: Convertimagetoobjects
Original: convert_image_to_objects
"""

import numpy as np
from typing import Tuple, Optional
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_outputs

@numpy(contract=ProcessingContract.PURE_2D)
@special_outputs("labels")
def convert_image_to_objects(
    image: np.ndarray,
    cast_to_bool: bool = True,
    preserve_label: bool = False,
    background: int = 0,
    connectivity: Optional[int] = None
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Converts an image (grayscale or binary) into an object label matrix.
    
    Args:
        image: Input image (H, W)
        cast_to_bool: If True, treats non-zero pixels as foreground (binary conversion)
        preserve_label: If True, uses existing pixel values as labels (no re-labeling)
        background: Pixel value to be treated as background
        connectivity: Maximum number of orthogonal hops for neighbor connectivity
        
    Returns:
        Tuple of (original_image, label_matrix)
    """
    from skimage.measure import label

    # Handle background subtraction/masking
    work_image = np.copy(image)
    mask = work_image != background

    if preserve_label:
        # Ensure background is 0 and return existing labels
        labels = np.zeros_like(work_image, dtype=np.int32)
        labels[mask] = work_image[mask].astype(np.int32)
    else:
        if cast_to_bool:
            # Convert to binary based on background value
            binary_input = mask
            labels = label(binary_input, connectivity=connectivity).astype(np.int32)
        else:
            # Label connected components of the same grayscale value
            # (Standard behavior for non-binary images in skimage.measure.label)
            labels = label(work_image, connectivity=connectivity, background=background).astype(np.int32)

    return image, labels