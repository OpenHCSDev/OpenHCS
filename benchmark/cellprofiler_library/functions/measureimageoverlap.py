"""
Converted from CellProfiler: MeasureImageOverlap
Original: measureimageoverlap
"""

import numpy as np
from typing import Tuple, Optional
from dataclasses import dataclass
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_outputs
from openhcs.processing.materialization import csv_materializer

class DecimationMethod(Enum):
    KMEANS = "K-Means"
    RANDOM = "Random"

@dataclass
class OverlapMeasurements:
    f1_score: float
    recall: float
    precision: float
    jaccard: float
    earth_movers_distance: Optional[float] = None

@numpy(contract=ProcessingContract.FLEXIBLE)
@special_outputs(("overlap_measurements", csv_materializer(
    fields=["f1_score", "recall", "precision", "jaccard", "earth_movers_distance"]
)))
def measure_image_overlap(
    image: np.ndarray,
    calculate_emd: bool = False,
    max_distance: int = 250,
    penalize_missing: bool = False,
    decimation_method: DecimationMethod = DecimationMethod.KMEANS,
    max_points: int = 250,
) -> Tuple[np.ndarray, OverlapMeasurements]:
    """
    Compares two images (typically binary masks or labels) to calculate overlap statistics.
    
    Args:
        image: Shape (2, H, W) or (3, H, W). 
               Index 0: Ground Truth Image
               Index 1: Test Image
               Index 2: Optional Mask
    """
    # Unstack inputs from dimension 0
    gt = image[0] > 0
    test = image[1] > 0
    
    mask = None
    if image.shape[0] == 3:
        mask = image[2] > 0
        gt = np.logical_and(gt, mask)
        test = np.logical_and(test, mask)

    # Calculate basic overlap statistics
    tp = np.logical_and(gt, test).sum()
    fp = np.logical_and(np.logical_not(gt), test).sum()
    fn = np.logical_and(gt, np.logical_not(test)).sum()

    precision = tp / (tp + fp) if (tp + fp) > 0 else 0.0
    recall = tp / (tp + fn) if (tp + fn) > 0 else 0.0
    f1 = (2 * precision * recall) / (precision + recall) if (precision + recall) > 0 else 0.0
    
    intersection = tp
    union = np.logical_or(gt, test).sum()
    jaccard = intersection / union if union > 0 else 0.0

    emd_value = None
    if calculate_emd:
        # Earth Mover's Distance implementation using scipy
        from scipy.stats import wasserstein_distance
        
        # For 2D images, we treat the pixel intensities as distributions
        # or coordinates of set bits. Here we use the flattened intensities.
        if np.any(gt) and np.any(test):
            # Note: A full EMD on spatial coordinates is computationally expensive.
            # This is a simplified 1D distribution comparison as a fallback 
            # if complex spatial EMD is not required.
            emd_value = wasserstein_distance(gt.ravel(), test.ravel())
        else:
            emd_value = float(max_distance) if penalize_missing else 0.0

    measurements = OverlapMeasurements(
        f1_score=float(f1),
        recall=float(recall),
        precision=float(precision),
        jaccard=float(jaccard),
        earth_movers_distance=emd_value
    )

    # Return the original test image as the primary image output, and the measurements
    return image[1:2], measurements