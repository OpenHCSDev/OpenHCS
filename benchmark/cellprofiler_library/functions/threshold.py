"""
Converted from CellProfiler: Threshold
Original: threshold
"""

import numpy as np
from typing import Tuple, Optional, Union, Any
from dataclasses import dataclass
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_outputs
from openhcs.processing.materialization import csv_materializer

class Scope(Enum):
    GLOBAL = "global"
    ADAPTIVE = "adaptive"

class Method(Enum):
    OTSU = "otsu"
    MINIMUM_CROSS_ENTROPY = "minimum_cross_entropy"
    LI = "li"
    ROBUST_BACKGROUND = "robust_background"
    MANUAL = "manual"

class Assignment(Enum):
    FOREGROUND = "foreground"
    BACKGROUND = "background"

class AveragingMethod(Enum):
    MEAN = "mean"
    MEDIAN = "median"

class VarianceMethod(Enum):
    STANDARD_DEVIATION = "standard_deviation"
    MAD = "mad"

@dataclass
class ThresholdMeasurements:
    final_threshold: float
    original_threshold: float
    guide_threshold: Optional[float]
    sigma: float

@numpy(contract=ProcessingContract.PURE_2D)
@special_outputs(("threshold_measurements", csv_materializer(
    fields=["final_threshold", "original_threshold", "guide_threshold", "sigma"]
)))
def threshold(
    image: np.ndarray,
    threshold_scope: Scope = Scope.GLOBAL,
    threshold_method: Method = Method.OTSU,
    assign_middle_to_foreground: Assignment = Assignment.FOREGROUND,
    log_transform: bool = False,
    threshold_correction_factor: float = 1.0,
    threshold_min: float = 0.0,
    threshold_max: float = 1.0,
    window_size: int = 50,
    smoothing: float = 0.0,
    lower_outlier_fraction: float = 0.05,
    upper_outlier_fraction: float = 0.05,
    averaging_method: AveragingMethod = AveragingMethod.MEAN,
    variance_method: VarianceMethod = VarianceMethod.STANDARD_DEVIATION,
    number_of_deviations: int = 2,
    predefined_threshold: Optional[float] = None,
    automatic: bool = False,
) -> Tuple[np.ndarray, ThresholdMeasurements]:
    """
    Apply thresholding to an image. Returns a binary mask and threshold metrics.
    """
    from skimage.filters import (
        threshold_otsu, 
        threshold_li, 
        threshold_minimum, 
        threshold_local
    )
    from scipy.ndimage import gaussian_filter

    # Handle Automatic override
    if automatic:
        smoothing = 1.0
        log_transform = False
        threshold_scope = Scope.GLOBAL
        threshold_method = Method.MINIMUM_CROSS_ENTROPY

    # Pre-processing: Smoothing
    working_image = image.copy()
    if smoothing > 0:
        working_image = gaussian_filter(working_image, sigma=smoothing)

    # Pre-processing: Log Transform
    if log_transform:
        working_image = np.log1p(working_image)

    def calculate_global(img, method):
        if method == Method.OTSU:
            return threshold_otsu(img)
        elif method == Method.LI:
            return threshold_li(img)
        elif method == Method.MINIMUM_CROSS_ENTROPY:
            # Minimum cross entropy is often approximated by Li or Minimum in skimage
            return threshold_li(img)
        elif method == Method.ROBUST_BACKGROUND:
            # Simplified Robust Background implementation
            lower = np.percentile(img, lower_outlier_fraction * 100)
            upper = np.percentile(img, (1 - upper_outlier_fraction) * 100)
            subset = img[(img >= lower) & (img <= upper)]
            if averaging_method == AveragingMethod.MEAN:
                avg = np.mean(subset)
            else:
                avg = np.median(subset)
            
            if variance_method == VarianceMethod.STANDARD_DEVIATION:
                dev = np.std(subset)
            else:
                dev = np.median(np.abs(subset - np.median(subset)))
            return avg + (number_of_deviations * dev)
        else:
            return threshold_otsu(img)

    # Logic for Predefined/Manual
    if predefined_threshold is not None:
        orig_threshold = predefined_threshold
        guide_threshold = None
    else:
        if threshold_scope == Scope.GLOBAL:
            orig_threshold = calculate_global(working_image, threshold_method)
            guide_threshold = None
        else: # Adaptive
            # Calculate local threshold map
            block_size = window_size if window_size % 2 != 0 else window_size + 1
            orig_threshold = threshold_local(working_image, block_size=block_size, method='gaussian')
            guide_threshold = calculate_global(working_image, threshold_method)

    # Apply correction and bounds
    final_threshold = orig_threshold * threshold_correction_factor
    if threshold_min is not None or threshold_max is not None:
        final_threshold = np.clip(final_threshold, threshold_min, threshold_max)

    # Generate Binary Mask
    binary_image = (working_image > final_threshold).astype(np.float32)
    
    # If adaptive, final_threshold is an array; for measurements we return the mean
    meas_final = float(np.mean(final_threshold))
    meas_orig = float(np.mean(orig_threshold))
    meas_guide = float(guide_threshold) if guide_threshold is not None else None

    return binary_image, ThresholdMeasurements(
        final_threshold=meas_final,
        original_threshold=meas_orig,
        guide_threshold=meas_guide,
        sigma=smoothing
    )