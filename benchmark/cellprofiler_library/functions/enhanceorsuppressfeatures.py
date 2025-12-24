"""
Converted from CellProfiler: EnhanceOrSuppressFeatures
Original: enhance_or_suppress_features
"""

import numpy as np
from enum import Enum
from typing import Tuple, Optional
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

class OperationMethod(Enum):
    ENHANCE = "Enhance"
    SUPPRESS = "Suppress"

class EnhanceMethod(Enum):
    SPECKLES = "Speckles"
    NEURITES = "Neurites"
    DARK_HOLES = "Dark holes"
    CIRCLES = "Circles"
    TEXTURE = "Texture"
    DIC = "DIC"

class SpeckleAccuracy(Enum):
    FAST = "Fast"
    SLOW = "Slow"

class NeuriteMethod(Enum):
    GRADIENT = "Tubeness"
    HOLE = "Hole"

@numpy(contract=ProcessingContract.PURE_2D)
def enhance_or_suppress_features(
    image: np.ndarray,
    operation: OperationMethod = OperationMethod.ENHANCE,
    feature_type: EnhanceMethod = EnhanceMethod.SPECKLES,
    feature_size: float = 10.0,
    speckle_accuracy: SpeckleAccuracy = SpeckleAccuracy.FAST,
    neurite_method: NeuriteMethod = NeuriteMethod.GRADIENT,
    neurite_rescale: bool = True,
    dark_hole_min: int = 1,
    dark_hole_max: int = 10,
    smoothing_scale: float = 2.0,
    dic_angle: float = 0.0,
    dic_decay: float = 0.95
) -> np.ndarray:
    """
    Enhances or suppresses specific image features like speckles, neurites, or circles.
    """
    from scipy import ndimage
    from skimage import filters, morphology, feature, measure

    # Helper for Suppress (Top-hat subtraction)
    if operation == OperationMethod.SUPPRESS:
        # Suppress features by performing a white top-hat transform and subtracting it
        selem = morphology.disk(feature_size)
        top_hat = morphology.white_tophat(image, selem)
        return np.clip(image - top_hat, 0, 1)

    # Enhance Logic
    if feature_type == EnhanceMethod.SPECKLES:
        # Speckles enhancement via white top-hat
        selem = morphology.disk(feature_size)
        return morphology.white_tophat(image, selem)

    elif feature_type == EnhanceMethod.CIRCLES:
        # Circles enhancement via multiscale rolling ball or simple white top-hat
        selem = morphology.disk(feature_size)
        return morphology.white_tophat(image, selem)

    elif feature_type == EnhanceMethod.NEURITES:
        # Neurite enhancement using Frangi or Meijering filters (Tubeness)
        if neurite_method == NeuriteMethod.GRADIENT:
            # Frangi filter is standard for neurite/vessel enhancement
            enhanced = filters.frangi(image, sigmas=np.arange(1, smoothing_scale + 1, 1))
        else:
            # Alternative: Meijering filter
            enhanced = filters.meijering(image, sigmas=np.arange(1, smoothing_scale + 1, 1))
        
        if neurite_rescale:
            img_min, img_max = enhanced.min(), enhanced.max()
            if img_max > img_min:
                enhanced = (enhanced - img_min) / (img_max - img_min)
        return enhanced

    elif feature_type == EnhanceMethod.DARK_HOLES:
        # Enhance dark holes via black top-hat (closing - original)
        # We use a range of scales if min/max are provided
        combined = np.zeros_like(image)
        for r in range(dark_hole_min, dark_hole_max + 1):
            selem = morphology.disk(r)
            combined = np.maximum(combined, morphology.black_tophat(image, selem))
        return combined

    elif feature_type == EnhanceMethod.TEXTURE:
        # Texture enhancement via local variance/standard deviation
        mean = ndimage.gaussian_filter(image, smoothing_scale)
        sq_mean = ndimage.gaussian_filter(image**2, smoothing_scale)
        variance = np.maximum(0, sq_mean - mean**2)
        return np.sqrt(variance)

    elif feature_type == EnhanceMethod.DIC:
        # DIC enhancement via integration along the shear angle
        # This is a simplified implementation of the line integration
        angle_rad = np.deg2rad(dic_angle)
        cos_a, sin_a = np.cos(angle_rad), np.sin(angle_rad)
        
        # Apply smoothing first
        smoothed = ndimage.gaussian_filter(image, smoothing_scale)
        
        # Simple directional derivative approximation
        grad_x = ndimage.sobel(smoothed, axis=1)
        grad_y = ndimage.sobel(smoothed, axis=0)
        enhanced = grad_x * cos_a + grad_y * sin_a
        
        # Apply decay/integration logic (simplified)
        return np.clip(enhanced, 0, 1)

    return image