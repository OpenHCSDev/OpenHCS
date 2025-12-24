"""
Converted from CellProfiler: MeasureImageOverlap
Original: measureimageoverlap

Measures overlap between a ground truth image and a test image,
computing statistics like true positives, false positives, false negatives,
and optionally Earth Mover's Distance.
"""

import numpy as np
from typing import Tuple, Optional
from dataclasses import dataclass
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline.function_contracts import special_outputs
from openhcs.processing.materialization import csv_materializer


class DecimationMethod(Enum):
    KMEANS = "kmeans"
    SKELETON = "skeleton"


@dataclass
class ImageOverlapMeasurement:
    slice_index: int
    true_positive_rate: float
    false_positive_rate: float
    false_negative_rate: float
    true_negative_rate: float
    precision: float
    recall: float
    f_factor: float
    jaccard_index: float
    dice_coefficient: float
    rand_index: float
    adjusted_rand_index: float
    earth_movers_distance: float


@numpy
@special_outputs(("overlap_measurements", csv_materializer(
    fields=["slice_index", "true_positive_rate", "false_positive_rate", 
            "false_negative_rate", "true_negative_rate", "precision", 
            "recall", "f_factor", "jaccard_index", "dice_coefficient",
            "rand_index", "adjusted_rand_index", "earth_movers_distance"],
    analysis_type="image_overlap"
)))
def measureimageoverlap(
    image: np.ndarray,
    calculate_emd: bool = False,
    max_distance: int = 250,
    penalize_missing: bool = False,
    decimation_method: DecimationMethod = DecimationMethod.KMEANS,
    max_points: int = 250,
) -> Tuple[np.ndarray, ImageOverlapMeasurement]:
    """
    Measure overlap between ground truth and test images.
    
    Args:
        image: Shape (2, H, W) or (3, H, W) - ground_truth_image, test_image, 
               and optionally mask stacked along dim 0
        calculate_emd: Whether to calculate Earth Mover's Distance
        max_distance: Maximum distance for EMD calculation
        penalize_missing: Whether to penalize missing points in EMD
        decimation_method: Method for decimating points (KMEANS or SKELETON)
        max_points: Maximum number of points for EMD calculation
    
    Returns:
        Tuple of (ground_truth_image, overlap_measurements)
    """
    from scipy.ndimage import distance_transform_edt
    from scipy.spatial.distance import cdist
    
    # Unstack inputs from dim 0
    if image.shape[0] >= 2:
        ground_truth_image = image[0].astype(bool)
        test_image = image[1].astype(bool)
        mask = image[2].astype(bool) if image.shape[0] > 2 else None
    else:
        raise ValueError("Image must have at least 2 slices (ground_truth, test)")
    
    # Apply mask if provided
    if mask is not None:
        ground_truth_image = ground_truth_image & mask
        test_image = test_image & mask
        total_pixels = np.sum(mask)
    else:
        total_pixels = ground_truth_image.size
    
    # Calculate overlap statistics
    true_positive = np.sum(ground_truth_image & test_image)
    false_positive = np.sum(~ground_truth_image & test_image)
    false_negative = np.sum(ground_truth_image & ~test_image)
    true_negative = np.sum(~ground_truth_image & ~test_image)
    
    # Avoid division by zero
    eps = 1e-10
    
    # Calculate rates
    true_positive_rate = true_positive / (true_positive + false_negative + eps)
    false_positive_rate = false_positive / (false_positive + true_negative + eps)
    false_negative_rate = false_negative / (true_positive + false_negative + eps)
    true_negative_rate = true_negative / (false_positive + true_negative + eps)
    
    # Precision and recall
    precision = true_positive / (true_positive + false_positive + eps)
    recall = true_positive_rate  # Same as sensitivity/TPR
    
    # F-factor (F1 score)
    f_factor = 2 * precision * recall / (precision + recall + eps)
    
    # Jaccard index (IoU)
    intersection = true_positive
    union = true_positive + false_positive + false_negative
    jaccard_index = intersection / (union + eps)
    
    # Dice coefficient
    dice_coefficient = 2 * intersection / (2 * intersection + false_positive + false_negative + eps)
    
    # Rand index
    n = total_pixels
    a = true_positive
    b = false_positive
    c = false_negative
    d = true_negative
    rand_index = (a + d) / (a + b + c + d + eps)
    
    # Adjusted Rand index
    n_choose_2 = n * (n - 1) / 2 if n > 1 else 1
    sum_ni_choose_2 = a + c
    sum_nj_choose_2 = a + b
    expected_index = (sum_ni_choose_2 * sum_nj_choose_2) / (n_choose_2 + eps)
    max_index = (sum_ni_choose_2 + sum_nj_choose_2) / 2
    adjusted_rand_index = (a - expected_index) / (max_index - expected_index + eps)
    adjusted_rand_index = max(0.0, min(1.0, adjusted_rand_index))  # Clamp to [0, 1]
    
    # Earth Mover's Distance
    earth_movers_distance = 0.0
    if calculate_emd:
        earth_movers_distance = _compute_earth_movers_distance(
            ground_truth_image,
            test_image,
            max_distance=max_distance,
            penalize_missing=penalize_missing,
            decimation_method=decimation_method,
            max_points=max_points
        )
    
    measurements = ImageOverlapMeasurement(
        slice_index=0,
        true_positive_rate=float(true_positive_rate),
        false_positive_rate=float(false_positive_rate),
        false_negative_rate=float(false_negative_rate),
        true_negative_rate=float(true_negative_rate),
        precision=float(precision),
        recall=float(recall),
        f_factor=float(f_factor),
        jaccard_index=float(jaccard_index),
        dice_coefficient=float(dice_coefficient),
        rand_index=float(rand_index),
        adjusted_rand_index=float(adjusted_rand_index),
        earth_movers_distance=float(earth_movers_distance)
    )
    
    # Return ground truth image as the output image
    return ground_truth_image.astype(np.float32)[np.newaxis, ...], measurements


def _compute_earth_movers_distance(
    ground_truth: np.ndarray,
    test: np.ndarray,
    max_distance: int,
    penalize_missing: bool,
    decimation_method: DecimationMethod,
    max_points: int
) -> float:
    """
    Compute Earth Mover's Distance between two binary images.
    """
    from scipy.spatial.distance import cdist
    
    # Get coordinates of foreground pixels
    gt_coords = np.argwhere(ground_truth)
    test_coords = np.argwhere(test)
    
    if len(gt_coords) == 0 or len(test_coords) == 0:
        if penalize_missing:
            return float(max_distance)
        return 0.0
    
    # Decimate points if needed
    if len(gt_coords) > max_points:
        gt_coords = _decimate_points(gt_coords, max_points, decimation_method)
    if len(test_coords) > max_points:
        test_coords = _decimate_points(test_coords, max_points, decimation_method)
    
    # Compute pairwise distances
    distances = cdist(gt_coords, test_coords, metric='euclidean')
    
    # Clip distances to max_distance
    distances = np.minimum(distances, max_distance)
    
    # Simple EMD approximation: mean of minimum distances in both directions
    min_dist_gt_to_test = np.mean(np.min(distances, axis=1))
    min_dist_test_to_gt = np.mean(np.min(distances, axis=0))
    
    emd = (min_dist_gt_to_test + min_dist_test_to_gt) / 2
    
    return float(emd)


def _decimate_points(
    coords: np.ndarray,
    max_points: int,
    method: DecimationMethod
) -> np.ndarray:
    """
    Reduce number of points using specified decimation method.
    """
    if method == DecimationMethod.KMEANS:
        # Simple uniform sampling as approximation to k-means
        indices = np.linspace(0, len(coords) - 1, max_points, dtype=int)
        return coords[indices]
    elif method == DecimationMethod.SKELETON:
        # Uniform sampling along the point list
        indices = np.linspace(0, len(coords) - 1, max_points, dtype=int)
        return coords[indices]
    else:
        # Default: uniform sampling
        indices = np.linspace(0, len(coords) - 1, max_points, dtype=int)
        return coords[indices]