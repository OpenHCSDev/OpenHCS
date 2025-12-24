"""
Converted from CellProfiler: Colortogray
Original: color_to_gray
"""

import numpy as np
from typing import Tuple, List, Union, Optional
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

class ImageChannelType(Enum):
    RGB = "RGB"
    HSV = "HSV"
    CHANNELS = "Channels"

@numpy(contract=ProcessingContract.PURE_2D)
def color_to_gray(
    image: np.ndarray,
    image_type: ImageChannelType = ImageChannelType.RGB,
    should_combine: bool = True,
    channels: Optional[List[int]] = None,
    contributions: Optional[List[float]] = None,
) -> np.ndarray:
    """
    Converts a color image to grayscale by either combining channels or splitting them.
    
    Args:
        image: Shape (C, H, W) where C is the number of channels.
        image_type: The color space of the input image.
        should_combine: If True, returns a single grayscale image (1, H, W).
                        If False, returns all split channels (C, H, W).
        channels: List of channel indices to use for combination.
        contributions: List of weights for each channel in the combination.
    
    Returns:
        np.ndarray: Shape (1, H, W) if combined, or (C, H, W) if split.
    """
    # Ensure image is 3D (C, H, W)
    if image.ndim == 2:
        image = image[np.newaxis, ...]
    
    if should_combine:
        # Default to equal weighting if not provided
        if channels is None:
            channels = list(range(image.shape[0]))
        if contributions is None:
            contributions = [1.0 / len(channels)] * len(channels)
            
        # Initialize output
        combined = np.zeros(image.shape[1:], dtype=np.float32)
        
        for idx, weight in zip(channels, contributions):
            if idx < image.shape[0]:
                combined += image[idx] * weight
        
        return combined[np.newaxis, ...]

    else:
        if image_type == ImageChannelType.HSV:
            # Manual RGB to HSV conversion for the first 3 channels
            # Note: This assumes input is RGB in range [0, 1]
            r, g, b = image[0], image[1], image[2]
            max_c = np.max(image[:3], axis=0)
            min_c = np.min(image[:3], axis=0)
            delta = max_c - min_c
            
            # Hue
            h = np.zeros_like(max_c)
            mask = delta != 0
            h[mask & (max_c == r)] = (60 * ((g[mask & (max_c == r)] - b[mask & (max_c == r)]) / delta[mask & (max_c == r)]) % 360)
            h[mask & (max_c == g)] = (60 * ((b[mask & (max_c == g)] - r[mask & (max_c == g)]) / delta[mask & (max_c == g)]) + 120)
            h[mask & (max_c == b)] = (60 * ((r[mask & (max_c == b)] - g[mask & (max_c == b)]) / delta[mask & (max_c == b)]) + 240)
            h /= 360.0 # Normalize to [0, 1]
            
            # Saturation
            s = np.zeros_like(max_c)
            s[max_c != 0] = delta[max_c != 0] / max_c[max_c != 0]
            
            # Value
            v = max_c
            
            return np.stack([h, s, v])
            
        # For RGB or Channels, we simply return the existing stack
        return image