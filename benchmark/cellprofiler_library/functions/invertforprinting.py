"""Converted from CellProfiler: InvertForPrinting

Inverts fluorescent images into brightfield-looking images for printing.
This module turns a single or multi-channel immunofluorescent-stained
image into an image that resembles a brightfield image stained with
similarly colored stains, which generally prints better.

Input: Stacked grayscale images (up to 3 channels: R, G, B) with shape (C, H, W)
       where C is 1-3 channels, or a color image with shape (3, H, W)
Output: Inverted color image with shape (3, H, W) representing RGB channels
"""

import numpy as np
from enum import Enum
from openhcs.core.memory.decorators import numpy


class OutputMode(Enum):
    COLOR = "color"
    GRAYSCALE = "grayscale"


@numpy
def invert_for_printing(
    image: np.ndarray,
    output_mode: OutputMode = OutputMode.COLOR,
    output_red: bool = True,
    output_green: bool = True,
    output_blue: bool = True,
) -> np.ndarray:
    """
    Invert fluorescent images into brightfield-looking images for printing.
    
    This function converts immunofluorescent-stained images into images that
    resemble brightfield staining, which generally prints better.
    
    Args:
        image: Input image with shape (C, H, W) where C is 1-3 channels.
               - If C=1: Single grayscale image (used for all missing channels as 0)
               - If C=2: Two grayscale images (third channel treated as 0)
               - If C=3: Three grayscale images or RGB color image
               Channels are interpreted as [Red, Green, Blue] in order.
        output_mode: Whether to output a single color image or separate grayscale channels.
                     COLOR returns (3, H, W), GRAYSCALE returns selected channels stacked.
        output_red: If output_mode is GRAYSCALE, whether to include inverted red channel.
        output_green: If output_mode is GRAYSCALE, whether to include inverted green channel.
        output_blue: If output_mode is GRAYSCALE, whether to include inverted blue channel.
    
    Returns:
        Inverted image. Shape depends on output_mode:
        - COLOR: (3, H, W) RGB inverted color image
        - GRAYSCALE: (N, H, W) where N is number of selected output channels
    """
    # Handle input dimensions
    if image.ndim == 2:
        # Single 2D image, treat as single channel
        image = image[np.newaxis, :, :]
    
    num_channels = image.shape[0]
    h, w = image.shape[1], image.shape[2]
    
    # Extract RGB channels, defaulting to 0 for missing channels
    red_image = image[0] if num_channels >= 1 else np.zeros((h, w), dtype=image.dtype)
    green_image = image[1] if num_channels >= 2 else np.zeros((h, w), dtype=image.dtype)
    blue_image = image[2] if num_channels >= 3 else np.zeros((h, w), dtype=image.dtype)
    
    # Perform the inversion transformation
    # This creates a brightfield-like appearance from fluorescent images
    # The formula simulates subtractive color mixing (like dyes/stains)
    inverted_red = (1.0 - green_image) * (1.0 - blue_image)
    inverted_green = (1.0 - red_image) * (1.0 - blue_image)
    inverted_blue = (1.0 - red_image) * (1.0 - green_image)
    
    if output_mode == OutputMode.COLOR:
        # Return full RGB color image
        inverted_color = np.stack([inverted_red, inverted_green, inverted_blue], axis=0)
        return inverted_color.astype(np.float32)
    else:
        # Return selected grayscale channels stacked
        output_channels = []
        if output_red:
            output_channels.append(inverted_red)
        if output_green:
            output_channels.append(inverted_green)
        if output_blue:
            output_channels.append(inverted_blue)
        
        if len(output_channels) == 0:
            # If no channels selected, return empty with correct spatial dims
            return np.zeros((1, h, w), dtype=np.float32)
        
        return np.stack(output_channels, axis=0).astype(np.float32)