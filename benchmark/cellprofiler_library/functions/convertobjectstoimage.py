"""
Converted from CellProfiler: ConvertObjectsToImage
Original: convert_objects_to_image

Converts object labels to various image representations (binary, grayscale, color, uint16).
"""

import numpy as np
from typing import Tuple
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline.function_contracts import special_inputs


class ImageMode(Enum):
    BINARY = "binary"
    GRAYSCALE = "grayscale"
    COLOR = "color"
    UINT16 = "uint16"


def _get_colormap(colormap_name: str, num_labels: int) -> np.ndarray:
    """Generate colors for labels using matplotlib colormap."""
    try:
        from matplotlib import colormaps
        cmap = colormaps.get_cmap(colormap_name)
    except (ImportError, ValueError):
        # Fallback to random colors if matplotlib not available or invalid colormap
        np.random.seed(42)
        return np.random.rand(num_labels + 1, 3)
    
    colors = np.zeros((num_labels + 1, 3))
    for i in range(1, num_labels + 1):
        colors[i] = cmap(i / max(num_labels, 1))[:3]
    return colors


@numpy(contract=ProcessingContract.PURE_2D)
@special_inputs("labels")
def convert_objects_to_image(
    image: np.ndarray,
    labels: np.ndarray,
    image_mode: ImageMode = ImageMode.COLOR,
    colormap_value: str = "jet",
) -> np.ndarray:
    """
    Convert object labels to an image representation.
    
    Args:
        image: Input image (H, W) - used for shape reference
        labels: Object labels (H, W) - integer labels where 0 is background
        image_mode: Output image format (BINARY, GRAYSCALE, COLOR, UINT16)
        colormap_value: Matplotlib colormap name for COLOR mode
    
    Returns:
        Converted image:
        - BINARY: (H, W) boolean mask where objects are True
        - GRAYSCALE: (H, W) float with normalized label values
        - COLOR: (H, W, 3) RGB image with colored objects
        - UINT16: (H, W) integer labels
    """
    labels = labels.astype(np.int32)
    h, w = labels.shape
    
    if image_mode == ImageMode.BINARY:
        # Binary mask: objects are 1, background is 0
        pixel_data = (labels > 0).astype(np.float32)
        
    elif image_mode == ImageMode.GRAYSCALE:
        # Grayscale: normalize labels to 0-1 range
        max_label = labels.max()
        if max_label > 0:
            pixel_data = labels.astype(np.float32) / max_label
        else:
            pixel_data = np.zeros((h, w), dtype=np.float32)
            
    elif image_mode == ImageMode.COLOR:
        # Color: apply colormap to labels
        max_label = labels.max()
        colors = _get_colormap(colormap_value, max_label)
        
        # Map labels to colors
        pixel_data = np.zeros((h, w, 3), dtype=np.float32)
        for label_id in range(1, max_label + 1):
            mask = labels == label_id
            if np.any(mask):
                pixel_data[mask] = colors[label_id]
        
        # For 2D output compatibility, we need to return (H, W)
        # Convert RGB to grayscale luminance for single-channel output
        # Or we could return the first channel - using luminance for better representation
        pixel_data = 0.299 * pixel_data[:, :, 0] + 0.587 * pixel_data[:, :, 1] + 0.114 * pixel_data[:, :, 2]
        
    elif image_mode == ImageMode.UINT16:
        # UINT16: return labels as float (will be cast appropriately downstream)
        pixel_data = labels.astype(np.float32)
        
    else:
        # Default to grayscale
        max_label = labels.max()
        if max_label > 0:
            pixel_data = labels.astype(np.float32) / max_label
        else:
            pixel_data = np.zeros((h, w), dtype=np.float32)
    
    return pixel_data