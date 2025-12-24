"""
Converted from CellProfiler: ColorToGray
Original: color_to_gray, split_colortogray
"""

import numpy as np
from typing import Tuple
from enum import Enum
from openhcs.core.memory.decorators import numpy


class ImageChannelType(Enum):
    RGB = "rgb"
    HSV = "hsv"
    CHANNELS = "channels"


class ColorToGrayMode(Enum):
    COMBINE = "combine"
    SPLIT = "split"


@numpy
def color_to_gray(
    image: np.ndarray,
    mode: ColorToGrayMode = ColorToGrayMode.SPLIT,
    image_type: ImageChannelType = ImageChannelType.RGB,
    channel_indices: Tuple[int, ...] = (0, 1, 2),
    contributions: Tuple[float, ...] = (1.0, 1.0, 1.0),
) -> np.ndarray:
    """
    Convert color image to grayscale by combining or splitting channels.
    
    Args:
        image: Shape (C, H, W) - color image with channels stacked in dim 0
               For RGB: (3, H, W), for multichannel: (N, H, W)
        mode: COMBINE to merge channels into single grayscale,
              SPLIT to separate channels (returns stacked grayscale images)
        image_type: RGB, HSV, or CHANNELS - determines how to interpret input
        channel_indices: Which channels to use when combining (0-indexed)
        contributions: Weight for each channel when combining (will be normalized)
    
    Returns:
        If mode=COMBINE: Shape (1, H, W) - single grayscale image
        If mode=SPLIT: Shape (C, H, W) - each channel as separate grayscale
    """
    if mode == ColorToGrayMode.COMBINE:
        return _combine_colortogray(image, channel_indices, contributions)
    else:
        return _split_colortogray(image, image_type)


def _combine_colortogray(
    image: np.ndarray,
    channel_indices: Tuple[int, ...],
    contributions: Tuple[float, ...],
) -> np.ndarray:
    """
    Combine specified channels into a single grayscale image.
    
    Args:
        image: Shape (C, H, W)
        channel_indices: Which channels to combine
        contributions: Weights for each channel
    
    Returns:
        Shape (1, H, W) - combined grayscale image
    """
    if len(channel_indices) != len(contributions):
        raise ValueError("channel_indices and contributions must have same length")
    
    # Normalize contributions to sum to 1
    total = sum(contributions)
    if total == 0:
        raise ValueError("Contributions cannot all be zero")
    normalized_weights = [c / total for c in contributions]
    
    # Extract and combine channels
    h, w = image.shape[1], image.shape[2]
    result = np.zeros((h, w), dtype=np.float32)
    
    for idx, weight in zip(channel_indices, normalized_weights):
        if idx < image.shape[0]:
            result += image[idx].astype(np.float32) * weight
    
    # Return as (1, H, W)
    return result[np.newaxis, :, :]


def _split_colortogray(
    image: np.ndarray,
    image_type: ImageChannelType,
) -> np.ndarray:
    """
    Split color image into separate grayscale channels.
    
    Args:
        image: Shape (C, H, W)
        image_type: How to interpret the channels
    
    Returns:
        Shape (C, H, W) - each channel as grayscale
    """
    if image_type == ImageChannelType.RGB:
        # RGB: just return channels as-is (already separated in dim 0)
        return image.astype(np.float32)
    
    elif image_type == ImageChannelType.HSV:
        # Convert RGB to HSV then split
        # Assume input is RGB (3, H, W), convert to HSV
        if image.shape[0] != 3:
            raise ValueError("HSV conversion requires 3-channel RGB input")
        
        # Transpose to (H, W, C) for conversion
        rgb = np.transpose(image, (1, 2, 0)).astype(np.float32)
        
        # Normalize to 0-1 if needed
        if rgb.max() > 1.0:
            rgb = rgb / 255.0
        
        # RGB to HSV conversion
        r, g, b = rgb[:, :, 0], rgb[:, :, 1], rgb[:, :, 2]
        
        maxc = np.maximum(np.maximum(r, g), b)
        minc = np.minimum(np.minimum(r, g), b)
        v = maxc
        
        deltac = maxc - minc
        s = np.where(maxc != 0, deltac / maxc, 0)
        
        # Hue calculation
        h = np.zeros_like(r)
        mask = deltac != 0
        
        # When max is R
        idx = (maxc == r) & mask
        h[idx] = ((g[idx] - b[idx]) / deltac[idx]) % 6
        
        # When max is G
        idx = (maxc == g) & mask
        h[idx] = (b[idx] - r[idx]) / deltac[idx] + 2
        
        # When max is B
        idx = (maxc == b) & mask
        h[idx] = (r[idx] - g[idx]) / deltac[idx] + 4
        
        h = h / 6.0  # Normalize to 0-1
        
        # Stack as (3, H, W)
        hsv = np.stack([h, s, v], axis=0).astype(np.float32)
        return hsv
    
    elif image_type == ImageChannelType.CHANNELS:
        # Generic multichannel: just return as-is
        return image.astype(np.float32)
    
    else:
        raise ValueError(f"Unsupported image type: {image_type}")