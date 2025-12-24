"""
Converted from CellProfiler: EnhanceEdges
Original: enhanceedges
"""

import numpy as np
from enum import Enum
from typing import Optional
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

class EdgeMethod(Enum):
    SOBEL = "sobel"
    PREWITT = "prewitt"
    CANNY = "canny"
    LOG = "log"
    ROBERTS = "roberts"
    KIRSCH = "kirsch"

class EdgeDirection(Enum):
    ALL = "all"
    HORIZONTAL = "horizontal"
    VERTICAL = "vertical"

@numpy(contract=ProcessingContract.PURE_2D)
def enhance_edges(
    image: np.ndarray,
    method: EdgeMethod = EdgeMethod.SOBEL,
    direction: EdgeDirection = EdgeDirection.ALL,
    automatic_gaussian: bool = True,
    sigma: float = 1.0,
    automatic_threshold: bool = True,
    manual_threshold: float = 0.2,
    threshold_adjustment_factor: float = 1.0,
    automatic_low_threshold: bool = True,
    low_threshold: float = 0.1,
) -> np.ndarray:
    """
    Enhances edges in an image using various algorithms.
    
    Args:
        image: Input 2D image (H, W)
        method: Algorithm to use (Sobel, Prewitt, Canny, LoG, Roberts, Kirsch)
        direction: Direction of edges to enhance (Sobel/Prewitt only)
        automatic_gaussian: If True, sigma is calculated automatically (Canny/LoG)
        sigma: Standard deviation of the Gaussian filter
        automatic_threshold: If True, uses Otsu to find Canny threshold
        manual_threshold: High threshold for Canny (0-1)
        threshold_adjustment_factor: Multiplier for Canny threshold
        automatic_low_threshold: If True, low threshold is 0.4 * high threshold
        low_threshold: Low threshold for Canny (0-1)
    """
    from skimage import feature, filters
    from scipy import ndimage

    # Handle sigma for LoG and Canny
    # CellProfiler default for 'automatic' sigma is often 1.0 or based on object size
    # Here we use the provided sigma if not automatic, else a standard default
    actual_sigma = 1.0 if (automatic_gaussian and method in [EdgeMethod.LOG, EdgeMethod.CANNY]) else sigma

    method_str = method.value.lower()

    if method_str == "sobel":
        if direction == EdgeDirection.HORIZONTAL:
            return filters.sobel_h(image)
        elif direction == EdgeDirection.VERTICAL:
            return filters.sobel_v(image)
        else:
            return filters.sobel(image)

    elif method_str == "prewitt":
        if direction == EdgeDirection.HORIZONTAL:
            return filters.prewitt_h(image)
        elif direction == EdgeDirection.VERTICAL:
            return filters.prewitt_v(image)
        else:
            return filters.prewitt(image)

    elif method_str == "canny":
        # Calculate thresholds
        if automatic_threshold:
            high_thresh = filters.threshold_otsu(image) * threshold_adjustment_factor
        else:
            high_thresh = manual_threshold
        
        if automatic_low_threshold:
            low_thresh = 0.4 * high_thresh
        else:
            low_thresh = low_threshold

        # skimage.feature.canny returns a boolean mask; convert to float
        edges = feature.canny(
            image,
            sigma=actual_sigma,
            low_threshold=low_thresh,
            high_threshold=high_thresh
        )
        return edges.astype(np.float32)

    elif method_str == "log":
        # Laplacian of Gaussian
        return ndimage.gaussian_laplace(image, sigma=actual_sigma)

    elif method_str == "roberts":
        return filters.roberts(image)

    elif method_str == "kirsch":
        # Kirsch operator implementation using custom kernels
        # Kirsch is 8 directions, taking the maximum
        def kirsch_filter(img):
            kernels = [
                np.array([[ 5,  5,  5], [-3,  0, -3], [-3, -3, -3]]),
                np.array([[ 5,  5, -3], [ 5,  0, -3], [-3, -3, -3]]),
                np.array([[ 5, -3, -3], [ 5,  0, -3], [ 5, -3, -3]]),
                np.array([[-3, -3, -3], [ 5,  0, -3], [ 5,  5, -3]]),
                np.array([[-3, -3, -3], [-3,  0, -3], [ 5,  5,  5]]),
                np.array([[-3, -3, -3], [-3,  0,  5], [-3,  5,  5]]),
                np.array([[-3, -3,  5], [-3,  0,  5], [-3, -3,  5]]),
                np.array([[-3,  5,  5], [-3,  0,  5], [-3, -3, -3]])
            ]
            res = np.zeros(img.shape)
            for k in kernels:
                res = np.maximum(res, ndimage.convolve(img, k))
            return res
        return kirsch_filter(image)

    else:
        raise ValueError(f"Unsupported edge enhancement method: {method_str}")