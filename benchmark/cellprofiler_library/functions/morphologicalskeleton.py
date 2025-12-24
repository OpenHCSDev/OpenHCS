"""
Converted from CellProfiler: Morphologicalskeleton
Original: morphologicalskeleton
"""

import numpy as np
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

@numpy(contract=ProcessingContract.FLEXIBLE)
def morphological_skeleton(
    image: np.ndarray,
    volumetric: bool = False
) -> np.ndarray:
    """
    Computes the skeleton of a binary image. 
    Thinning reduces foreground objects to 1-pixel wide (2D) or 1-voxel wide (3D) 
    skeletal representations.
    
    Args:
        image: Input binary image (D, H, W).
        volumetric: If True, treats the input as a 3D volume for skeletonization.
                   If False, processes each slice independently.
    """
    from skimage.morphology import skeletonize, skeletonize_3d

    # Ensure input is boolean for skimage
    binary_image = image > 0

    if volumetric:
        # PURE_3D logic: Process the entire (D, H, W) volume
        # skeletonize_3d is specifically for volumetric data
        skeleton = skeletonize_3d(binary_image)
    else:
        # PURE_2D logic: Process slice by slice
        # We iterate over dimension 0 (D)
        skeleton = np.zeros_like(image)
        for i in range(image.shape[0]):
            skeleton[i] = skeletonize(binary_image[i])

    return skeleton.astype(image.dtype)