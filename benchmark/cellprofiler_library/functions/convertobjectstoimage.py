"""
Converted from CellProfiler: ConvertObjectsToImage
Original: convert_objects_to_image
"""

import numpy as np
from enum import Enum
from typing import Tuple, Optional
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

class ImageMode(Enum):
    BINARY = "binary"
    GRAYSCALE = "grayscale"
    COLOR = "color"
    UINT16 = "uint16"

@numpy(contract=ProcessingContract.PURE_2D)
def convert_objects_to_image(
    image: np.ndarray,
    image_mode: ImageMode = ImageMode.GRAYSCALE,
    colormap: str = "viridis"
) -> np.ndarray:
    """
    Converts label objects into an image format.
    
    Args:
        image: The input label image (H, W).
        image_mode: The output format (Binary, Grayscale, Color, or uint16).
        colormap: The colormap to use if image_mode is Color.
    
    Returns:
        np.ndarray: The converted image.
    """
    labels = image.astype(np.int32)
    shape = labels.shape
    mask = labels != 0

    if image_mode == ImageMode.BINARY:
        return mask.astype(np.float32)

    if image_mode == ImageMode.GRAYSCALE:
        # Normalize labels to [0, 1] for grayscale
        if np.any(mask):
            res = labels.astype(np.float32)
            res[mask] = res[mask] / np.max(res)
            return res
        return np.zeros(shape, dtype=np.float32)

    if image_mode == ImageMode.UINT16:
        # Return raw labels cast to uint16
        return labels.astype(np.uint16)

    if image_mode == ImageMode.COLOR:
        import matplotlib.pyplot as plt
        
        # Create a normalized version for the colormap
        if not np.any(mask):
            return np.zeros(shape + (3,), dtype=np.float32)
            
        # We use a shuffled label approach or direct colormap to distinguish objects
        # To mimic CP behavior, we often use the labels as indices into a colormap
        norm_labels = labels.astype(np.float32)
        max_label = np.max(norm_labels)
        norm_labels[mask] = norm_labels[mask] / max_label
        
        try:
            cm = plt.get_cmap(colormap)
        except ValueError:
            cm = plt.get_cmap("viridis")
            
        # Apply colormap (returns RGBA)
        color_image = cm(norm_labels)
        
        # Strip alpha channel and return RGB
        rgb_image = color_image[:, :, :3].astype(np.float32)
        # Set background to black
        rgb_image[~mask] = 0
        
        return rgb_image

    return image.astype(np.float32)