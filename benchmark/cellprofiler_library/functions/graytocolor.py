"""
Converted from CellProfiler: GrayToColor
Original: GrayToColor module

Takes grayscale images and produces a color image from them.
Supports RGB, CMYK, Stack, and Composite color schemes.
"""

import numpy as np
from typing import Tuple, List, Optional
from enum import Enum
from openhcs.core.memory.decorators import numpy


class ColorScheme(Enum):
    RGB = "rgb"
    CMYK = "cmyk"
    STACK = "stack"
    COMPOSITE = "composite"


def _hex_to_rgb(hex_color: str) -> Tuple[float, float, float]:
    """Convert hex color string to RGB tuple (0-1 range)."""
    hex_color = hex_color.lstrip('#')
    r = int(hex_color[0:2], 16) / 255.0
    g = int(hex_color[2:4], 16) / 255.0
    b = int(hex_color[4:6], 16) / 255.0
    return (r, g, b)


@numpy
def gray_to_color_rgb(
    image: np.ndarray,
    red_channel: int = 0,
    green_channel: int = 1,
    blue_channel: int = 2,
    red_weight: float = 1.0,
    green_weight: float = 1.0,
    blue_weight: float = 1.0,
    rescale_intensity: bool = True,
) -> np.ndarray:
    """
    Combine grayscale images into an RGB color image.

    Args:
        image: Shape (N, H, W) - N grayscale images stacked along dim 0
        red_channel: Index of channel to use for red (default 0, use -1 for black)
        green_channel: Index of channel to use for green (default 1, use -1 for black)
        blue_channel: Index of channel to use for blue (default 2, use -1 for black)
        red_weight: Relative weight for the red image.
        green_weight: Relative weight for the green image.
        blue_weight: Relative weight for the blue image.
        rescale_intensity: Whether to rescale each channel to 0-1 range.

    Returns:
        Shape (H, W, 3) RGB color image.

    CellProfiler Parameter Mapping:
    (CellProfiler setting -> Python parameter)
        'Select the image to be colored red' -> red_channel
        'Select the image to be colored green' -> green_channel
        'Select the image to be colored blue' -> blue_channel
        'Relative weight for the red image' -> red_weight
        'Relative weight for the green image' -> green_weight
        'Relative weight for the blue image' -> blue_weight
    """
    h, w = image.shape[1], image.shape[2]

    # Get channels (use zeros if -1)
    red_img = image[red_channel].astype(np.float64) if red_channel >= 0 else np.zeros((h, w), dtype=np.float64)
    green_img = image[green_channel].astype(np.float64) if green_channel >= 0 else np.zeros((h, w), dtype=np.float64)
    blue_img = image[blue_channel].astype(np.float64) if blue_channel >= 0 else np.zeros((h, w), dtype=np.float64)
    
    if rescale_intensity:
        if np.max(red_img) > 0:
            red_img = red_img / np.max(red_img)
        if np.max(green_img) > 0:
            green_img = green_img / np.max(green_img)
        if np.max(blue_img) > 0:
            blue_img = blue_img / np.max(blue_img)
    
    # Apply weights
    red_img = red_img * red_weight
    green_img = green_img * green_weight
    blue_img = blue_img * blue_weight
    
    # Stack into RGB image (H, W, 3)
    rgb_image = np.dstack([red_img, green_img, blue_img])
    
    # Clip values that went out of range after multiplication
    if rescale_intensity:
        rgb_image = np.clip(rgb_image, 0, 1)
    
    return rgb_image.astype(np.float32)


@numpy
def gray_to_color_cmyk(
    image: np.ndarray,
    cyan_channel: int = 0,
    magenta_channel: int = 1,
    yellow_channel: int = 2,
    gray_channel: int = 3,
    cyan_weight: float = 1.0,
    magenta_weight: float = 1.0,
    yellow_weight: float = 1.0,
    gray_weight: float = 1.0,
    rescale_intensity: bool = True,
) -> np.ndarray:
    """
    Combine grayscale images into a color image using CMYK scheme.

    Args:
        image: Shape (N, H, W) - N grayscale images stacked along dim 0
        cyan_channel: Index of channel to use for cyan (default 0, use -1 for black)
        magenta_channel: Index of channel to use for magenta (default 1, use -1 for black)
        yellow_channel: Index of channel to use for yellow (default 2, use -1 for black)
        gray_channel: Index of channel to use for brightness (default 3, use -1 for black)
        cyan_weight: Relative weight for the cyan image.
        magenta_weight: Relative weight for the magenta image.
        yellow_weight: Relative weight for the yellow image.
        gray_weight: Relative weight for the brightness image.
        rescale_intensity: Whether to rescale each channel to 0-1 range.

    Returns:
        Shape (H, W, 3) RGB color image.
    """
    h, w = image.shape[1], image.shape[2]

    # Get channels (use zeros if -1)
    cyan_img = image[cyan_channel].astype(np.float64) if cyan_channel >= 0 else np.zeros((h, w), dtype=np.float64)
    magenta_img = image[magenta_channel].astype(np.float64) if magenta_channel >= 0 else np.zeros((h, w), dtype=np.float64)
    yellow_img = image[yellow_channel].astype(np.float64) if yellow_channel >= 0 else np.zeros((h, w), dtype=np.float64)
    gray_img = image[gray_channel].astype(np.float64) if gray_channel >= 0 else np.zeros((h, w), dtype=np.float64)
    
    if rescale_intensity:
        if np.max(cyan_img) > 0:
            cyan_img = cyan_img / np.max(cyan_img)
        if np.max(magenta_img) > 0:
            magenta_img = magenta_img / np.max(magenta_img)
        if np.max(yellow_img) > 0:
            yellow_img = yellow_img / np.max(yellow_img)
        if np.max(gray_img) > 0:
            gray_img = gray_img / np.max(gray_img)
    
    # CMYK to RGB conversion with weights
    # Cyan adds to green and blue (0, 0.5, 0.5)
    # Magenta adds to red and blue (0.5, 0, 0.5)
    # Yellow adds to red and green (0.5, 0.5, 0)
    # Gray adds equally to all (1/3, 1/3, 1/3)
    
    rgb_image = np.zeros((h, w, 3), dtype=np.float64)
    
    # Cyan contribution
    rgb_image[:, :, 1] += cyan_img * cyan_weight * 0.5  # green
    rgb_image[:, :, 2] += cyan_img * cyan_weight * 0.5  # blue
    
    # Magenta contribution
    rgb_image[:, :, 0] += magenta_img * magenta_weight * 0.5  # red
    rgb_image[:, :, 2] += magenta_img * magenta_weight * 0.5  # blue
    
    # Yellow contribution
    rgb_image[:, :, 0] += yellow_img * yellow_weight * 0.5  # red
    rgb_image[:, :, 1] += yellow_img * yellow_weight * 0.5  # green
    
    # Gray contribution
    rgb_image[:, :, 0] += gray_img * gray_weight * (1.0 / 3.0)  # red
    rgb_image[:, :, 1] += gray_img * gray_weight * (1.0 / 3.0)  # green
    rgb_image[:, :, 2] += gray_img * gray_weight * (1.0 / 3.0)  # blue
    
    # Clip values
    if rescale_intensity:
        rgb_image = np.clip(rgb_image, 0, 1)
    
    return rgb_image.astype(np.float32)


@numpy
def gray_to_color_stack(
    image: np.ndarray,
) -> np.ndarray:
    """
    Stack grayscale images into a multi-channel image.
    
    Args:
        image: Shape (N, H, W) - N grayscale images stacked.
    
    Returns:
        Shape (H, W, N) multi-channel image.
    """
    # Transpose from (N, H, W) to (H, W, N)
    return np.transpose(image, (1, 2, 0)).astype(np.float32)


@numpy
def gray_to_color_composite(
    image: np.ndarray,
    colors: List[str] = None,
    weights: List[float] = None,
    rescale_intensity: bool = True,
) -> np.ndarray:
    """
    Combine grayscale images into a composite color image.
    
    Each grayscale image is assigned a color and weighted, then
    all colored images are added together.
    
    Args:
        image: Shape (N, H, W) - N grayscale images stacked.
        colors: List of N hex color strings (e.g., ['#ff0000', '#00ff00']).
                Defaults to cycling through red, green, blue, yellow, magenta, cyan.
        weights: List of N weights for each image. Defaults to 1.0 for all.
        rescale_intensity: Whether to rescale each channel to 0-1 range.
    
    Returns:
        Shape (H, W, 3) RGB color image.
    """
    n_channels = image.shape[0]
    h, w = image.shape[1], image.shape[2]
    
    # Default colors
    default_colors = ['#ff0000', '#00ff00', '#0000ff', '#808000', '#800080', '#008080']
    if colors is None:
        colors = [default_colors[i % len(default_colors)] for i in range(n_channels)]
    
    # Default weights
    if weights is None:
        weights = [1.0] * n_channels
    
    rgb_image = np.zeros((h, w, 3), dtype=np.float64)
    
    for i in range(n_channels):
        channel_img = image[i].astype(np.float64)
        
        if rescale_intensity and np.max(channel_img) > 0:
            channel_img = channel_img / np.max(channel_img)
        
        # Get RGB color
        r, g, b = _hex_to_rgb(colors[i])
        weight = weights[i]
        
        # Add weighted colored image
        rgb_image[:, :, 0] += channel_img * r * weight
        rgb_image[:, :, 1] += channel_img * g * weight
        rgb_image[:, :, 2] += channel_img * b * weight
    
    # Clip values
    if rescale_intensity:
        rgb_image = np.clip(rgb_image, 0, 1)
    
    return rgb_image.astype(np.float32)