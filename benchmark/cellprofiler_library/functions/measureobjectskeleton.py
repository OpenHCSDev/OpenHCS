"""
Converted from CellProfiler: MeasureObjectSkeleton
Original: MeasureObjectSkeleton

Measures branching structures (neurons, vasculature, roots) that originate
from seed objects. Counts trunks, branches, endpoints, and total skeleton length.
"""

import numpy as np
from typing import Tuple
from dataclasses import dataclass
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_inputs, special_outputs
from openhcs.processing.materialization import csv_materializer


@dataclass
class ObjectSkeletonMeasurement:
    """Measurements for skeleton branching structures per seed object."""
    slice_index: int
    object_label: int
    number_trunks: int
    number_non_trunk_branches: int
    number_branch_ends: int
    total_skeleton_length: float


def _strel_disk(radius: float) -> np.ndarray:
    """Create a disk structuring element."""
    r = int(radius + 0.5)
    y, x = np.ogrid[-r:r+1, -r:r+1]
    return (x*x + y*y <= radius*radius).astype(np.uint8)


def _skeletonize(binary: np.ndarray) -> np.ndarray:
    """Skeletonize a binary image."""
    from skimage.morphology import skeletonize
    return skeletonize(binary > 0)


def _branchpoints(skeleton: np.ndarray) -> np.ndarray:
    """Find branchpoints in skeleton (pixels with >2 neighbors)."""
    from scipy.ndimage import convolve
    kernel = np.array([[1, 1, 1],
                       [1, 0, 1],
                       [1, 1, 1]], dtype=np.uint8)
    neighbor_count = convolve(skeleton.astype(np.uint8), kernel, mode='constant', cval=0)
    return (skeleton > 0) & (neighbor_count > 2)


def _endpoints(skeleton: np.ndarray) -> np.ndarray:
    """Find endpoints in skeleton (pixels with exactly 1 neighbor)."""
    from scipy.ndimage import convolve
    kernel = np.array([[1, 1, 1],
                       [1, 0, 1],
                       [1, 1, 1]], dtype=np.uint8)
    neighbor_count = convolve(skeleton.astype(np.uint8), kernel, mode='constant', cval=0)
    return (skeleton > 0) & (neighbor_count == 1)


def _fill_small_holes(binary: np.ndarray, max_hole_size: int) -> np.ndarray:
    """Fill holes smaller than max_hole_size pixels."""
    from scipy.ndimage import label, binary_fill_holes
    from skimage.morphology import remove_small_holes
    return remove_small_holes(binary, area_threshold=max_hole_size)


def _propagate_labels(labels: np.ndarray, mask: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    """Propagate labels to masked region, returning labels and distance."""
    from scipy.ndimage import distance_transform_edt, label as ndlabel
    
    # Distance from each point to nearest labeled region
    distance = distance_transform_edt(labels == 0)
    
    # For each point in mask, find nearest label
    from scipy.ndimage import grey_dilation
    
    propagated = labels.copy()
    max_dist = int(np.max(distance[mask])) + 1
    
    for _ in range(max_dist):
        dilated = grey_dilation(propagated, size=3)
        propagated = np.where((propagated == 0) & mask, dilated, propagated)
    
    return propagated, distance


def _skeleton_length_per_label(labeled_skeleton: np.ndarray, label_range: np.ndarray) -> np.ndarray:
    """Calculate total skeleton length per label."""
    from scipy.ndimage import sum as ndsum
    if len(label_range) == 0:
        return np.zeros(0)
    lengths = ndsum(labeled_skeleton > 0, labeled_skeleton, label_range)
    return np.atleast_1d(lengths).astype(float)


@numpy(contract=ProcessingContract.FLEXIBLE)
@special_inputs("seed_labels")
@special_outputs(("skeleton_measurements", csv_materializer(
    fields=["slice_index", "object_label", "number_trunks", 
            "number_non_trunk_branches", "number_branch_ends", "total_skeleton_length"],
    analysis_type="object_skeleton"
)))
def measure_object_skeleton(
    image: np.ndarray,
    seed_labels: np.ndarray,
    fill_small_holes: bool = True,
    maximum_hole_size: int = 10,
) -> Tuple[np.ndarray, list]:
    """
    Measure branching structures in skeletonized images relative to seed objects.
    
    Args:
        image: Shape (D, H, W) - skeletonized binary image (D slices)
        seed_labels: Shape (D, H, W) - labeled seed objects (e.g., nuclei/soma)
        fill_small_holes: Whether to fill small holes before analysis
        maximum_hole_size: Maximum hole size to fill in pixels
    
    Returns:
        Tuple of (image unchanged, list of ObjectSkeletonMeasurement)
    """
    from scipy.ndimage import grey_dilation, grey_erosion, sum as ndsum
    
    all_measurements = []
    
    for slice_idx in range(image.shape[0]):
        skeleton = image[slice_idx] > 0
        labels = seed_labels[slice_idx].astype(np.int32)
        
        labels_count = int(np.max(labels))
        if labels_count == 0:
            continue
            
        label_range = np.arange(1, labels_count + 1, dtype=np.int32)
        
        # Create disk structuring element
        disk = _strel_disk(1.5)
        
        # Dilate labels to create seed mask
        dilated_labels = grey_dilation(labels, footprint=disk)
        seed_mask = dilated_labels > 0
        
        # Combine skeleton with seed mask
        combined_skel = skeleton | seed_mask
        
        # Erode to find seed center
        closed_labels = grey_erosion(dilated_labels, footprint=disk)
        seed_center = closed_labels > 0
        
        # Remove seed center from skeleton
        combined_skel = combined_skel & (~seed_center)
        
        # Fill small holes if requested
        if fill_small_holes:
            combined_skel = _fill_small_holes(combined_skel, maximum_hole_size)
        
        # Reskeletonize
        combined_skel = _skeletonize(combined_skel)
        
        # Skeleton outside of labels
        outside_skel = combined_skel & (dilated_labels == 0)
        
        # Propagate labels to skeleton
        dlabels, distance_map = _propagate_labels(dilated_labels, combined_skel)
        
        # Remove skeleton points not connected to seeds
        combined_skel = combined_skel & (dlabels > 0)
        
        # Find branchpoints and endpoints
        branch_points = _branchpoints(combined_skel)
        end_points = _endpoints(combined_skel)
        
        # Calculate branching counts
        from scipy.ndimage import convolve
        kernel = np.array([[1, 1, 1],
                           [1, 0, 1],
                           [1, 1, 1]], dtype=np.uint8)
        neighbor_count = convolve(combined_skel.astype(np.uint8), kernel, mode='constant', cval=0)
        branching_counts = np.clip(neighbor_count - 2, 0, 2)
        branching_counts[~combined_skel] = 0
        
        # Only take branches within 1 pixel of outside skeleton
        from scipy.ndimage import binary_dilation
        dilated_skel = binary_dilation(outside_skel, structure=np.ones((3, 3)))
        branching_counts[~dilated_skel] = 0
        
        # Nearby labels (within 1.5 pixels)
        nearby_labels = dlabels.copy()
        nearby_labels[distance_map > 1.5] = 0
        
        # Outside labels
        outside_labels = dlabels.copy()
        outside_labels[nearby_labels > 0] = 0
        
        # Count trunks (branchpoints within seed region)
        trunk_counts = np.zeros(labels_count, dtype=np.int32)
        for lbl in label_range:
            trunk_counts[lbl - 1] = int(np.sum(branching_counts[nearby_labels == lbl]))
        
        # Count branches (branchpoints outside seed region)
        branch_counts = np.zeros(labels_count, dtype=np.int32)
        for lbl in label_range:
            branch_counts[lbl - 1] = int(np.sum(branch_points[outside_labels == lbl]))
        
        # Count endpoints
        end_counts = np.zeros(labels_count, dtype=np.int32)
        for lbl in label_range:
            end_counts[lbl - 1] = int(np.sum(end_points[outside_labels == lbl]))
        
        # Calculate skeleton lengths
        labeled_outside = dlabels * outside_skel.astype(np.int32)
        total_distance = _skeleton_length_per_label(labeled_outside, label_range)
        
        # Create measurements for each object
        for i, lbl in enumerate(label_range):
            measurement = ObjectSkeletonMeasurement(
                slice_index=slice_idx,
                object_label=int(lbl),
                number_trunks=int(trunk_counts[i]),
                number_non_trunk_branches=int(branch_counts[i]),
                number_branch_ends=int(end_counts[i]),
                total_skeleton_length=float(total_distance[i]) if i < len(total_distance) else 0.0
            )
            all_measurements.append(measurement)
    
    return image, all_measurements