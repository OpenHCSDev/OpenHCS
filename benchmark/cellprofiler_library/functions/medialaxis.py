"""
Converted from CellProfiler: Medialaxis
Original: medialaxis
"""

import numpy as np
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

@numpy(contract=ProcessingContract.PURE_2D)
def medialaxis(
    image: np.ndarray,
    multichannel: bool = False
) -> np.ndarray:
    """
    Computes the medial axis transform (skeletonization) of a binary image.
    
    Args:
        image: Input image. If PURE_2D, shape is (H, W).
        multichannel: If True, converts RGB to grayscale before processing.
        
    Returns:
        np.ndarray: The medial axis of the input image.
    """
    from skimage.morphology import medial_axis
    
    # Handle multichannel conversion if necessary
    if multichannel and image.ndim == 3:
        # Assuming standard RGB weights if 3 channels present at (C, H, W) or (H, W, C)
        # In OpenHCS PURE_2D, image is (H, W). If it's multichannel, it would be handled 
        # via the dimension 0 unstacking or explicit logic. 
        # Here we implement the grayscale conversion logic for a 2D slice.
        if image.shape[0] == 3: # (3, H, W)
            image = 0.2125 * image[0] + 0.7154 * image[1] + 0.0721 * image[2]
        elif image.shape[-1] == 3: # (H, W, 3)
            image = 0.2125 * image[:, :, 0] + 0.7154 * image[:, :, 1] + 0.0721 * image[:, :, 2]

    # skimage.morphology.medial_axis expects a boolean/binary image
    # We ensure it is boolean. If it's intensity, any non-zero is True.
    binary_input = image > 0
    
    skeleton = medial_axis(binary_input)
    
    # Return as float32 for consistency in OpenHCS pipelines
    return skeleton.astype(np.float32)