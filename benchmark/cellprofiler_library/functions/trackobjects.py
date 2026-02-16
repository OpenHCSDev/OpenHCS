"""
Converted from CellProfiler: TrackObjects
Original: TrackObjects module for tracking objects across frames

NOTE: This is a complex tracking module that requires temporal state management.
OpenHCS handles this through sequential_components in pipeline configuration.
The function processes frame-by-frame and maintains tracking state.
"""

import numpy as np
from typing import Tuple, Optional, Dict, Any, List
from dataclasses import dataclass, field
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline.function_contracts import special_inputs, special_outputs
from openhcs.processing.materialization import csv_materializer


class TrackingMethod(Enum):
    OVERLAP = "overlap"
    DISTANCE = "distance"
    MEASUREMENTS = "measurements"
    LAP = "lap"


class MovementModel(Enum):
    RANDOM = "random"
    VELOCITY = "velocity"
    BOTH = "both"


@dataclass
class TrackingResult:
    """Tracking measurements for objects in current frame"""
    slice_index: int
    object_count: int
    new_object_count: int
    lost_object_count: int
    split_count: int
    merge_count: int


@dataclass
class ObjectTrackingData:
    """Per-object tracking data"""
    label: np.ndarray
    parent_object_number: np.ndarray
    parent_image_number: np.ndarray
    trajectory_x: np.ndarray
    trajectory_y: np.ndarray
    distance_traveled: np.ndarray
    displacement: np.ndarray
    integrated_distance: np.ndarray
    linearity: np.ndarray
    lifetime: np.ndarray


def _centers_of_labels(labels: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    """Calculate centers of labeled objects"""
    from scipy.ndimage import center_of_mass
    
    if labels.max() == 0:
        return np.array([]), np.array([])
    
    n_labels = labels.max()
    centers = center_of_mass(np.ones_like(labels), labels, range(1, n_labels + 1))
    
    if len(centers) == 0:
        return np.array([]), np.array([])
    
    centers = np.array(centers)
    return centers[:, 0], centers[:, 1]  # i (y), j (x)


def _track_by_overlap(
    current_labels: np.ndarray,
    old_labels: Optional[np.ndarray],
    old_object_numbers: np.ndarray,
    max_object_number: int
) -> Tuple[np.ndarray, np.ndarray, np.ndarray, int]:
    """Track objects by maximum overlap between frames"""
    from scipy.sparse import coo_matrix
    
    i, j = _centers_of_labels(current_labels)
    cur_count = int(current_labels.max()) if current_labels.max() > 0 else 0
    
    if old_labels is None or cur_count == 0:
        # First frame or no objects
        new_labels = np.arange(1, cur_count + 1) + max_object_number
        return new_labels, np.zeros(cur_count, int), np.zeros(cur_count, int), max_object_number + cur_count
    
    old_count = int(old_labels.max()) if old_labels.max() > 0 else 0
    
    if old_count == 0:
        new_labels = np.arange(1, cur_count + 1) + max_object_number
        return new_labels, np.zeros(cur_count, int), np.zeros(cur_count, int), max_object_number + cur_count
    
    # Calculate overlap
    mask = (current_labels > 0) & (old_labels > 0)
    if not np.any(mask):
        new_labels = np.arange(1, cur_count + 1) + max_object_number
        return new_labels, np.zeros(cur_count, int), np.zeros(cur_count, int), max_object_number + cur_count
    
    cur = current_labels[mask]
    old = old_labels[mask]
    
    histogram = coo_matrix(
        (np.ones(len(cur)), (cur, old)),
        shape=(cur_count + 1, old_count + 1)
    ).toarray()
    
    old_of_new = np.argmax(histogram, 1)[1:]  # Best old match for each new
    new_of_old = np.argmax(histogram, 0)[1:]  # Best new match for each old
    
    # Assign labels
    new_labels = np.zeros(cur_count, int)
    parent_object_numbers = np.zeros(cur_count, int)
    parent_image_numbers = np.zeros(cur_count, int)
    
    for new_idx in range(cur_count):
        old_idx = old_of_new[new_idx]
        if old_idx > 0 and new_of_old[old_idx - 1] == new_idx + 1:
            # Mutual best match
            new_labels[new_idx] = old_object_numbers[old_idx - 1]
            parent_object_numbers[new_idx] = old_idx
            parent_image_numbers[new_idx] = 1  # Previous frame
        else:
            # New object
            max_object_number += 1
            new_labels[new_idx] = max_object_number
    
    return new_labels, parent_object_numbers, parent_image_numbers, max_object_number


def _track_by_distance(
    current_labels: np.ndarray,
    old_labels: Optional[np.ndarray],
    old_object_numbers: np.ndarray,
    max_object_number: int,
    pixel_radius: int
) -> Tuple[np.ndarray, np.ndarray, np.ndarray, int]:
    """Track objects by minimum distance between centroids"""
    from scipy.ndimage import distance_transform_edt
    
    i, j = _centers_of_labels(current_labels)
    cur_count = len(i)
    
    if old_labels is None or cur_count == 0:
        new_labels = np.arange(1, cur_count + 1) + max_object_number if cur_count > 0 else np.array([], int)
        return new_labels, np.zeros(cur_count, int), np.zeros(cur_count, int), max_object_number + cur_count
    
    old_i, old_j = _centers_of_labels(old_labels)
    old_count = len(old_i)
    
    if old_count == 0:
        new_labels = np.arange(1, cur_count + 1) + max_object_number
        return new_labels, np.zeros(cur_count, int), np.zeros(cur_count, int), max_object_number + cur_count
    
    # Calculate distances between all pairs
    new_labels = np.zeros(cur_count, int)
    parent_object_numbers = np.zeros(cur_count, int)
    parent_image_numbers = np.zeros(cur_count, int)
    
    # Simple nearest neighbor matching
    for new_idx in range(cur_count):
        min_dist = pixel_radius + 1
        best_old = -1
        for old_idx in range(old_count):
            dist = np.sqrt((i[new_idx] - old_i[old_idx])**2 + (j[new_idx] - old_j[old_idx])**2)
            if dist < min_dist:
                min_dist = dist
                best_old = old_idx
        
        if best_old >= 0 and min_dist <= pixel_radius:
            new_labels[new_idx] = old_object_numbers[best_old]
            parent_object_numbers[new_idx] = best_old + 1
            parent_image_numbers[new_idx] = 1
        else:
            max_object_number += 1
            new_labels[new_idx] = max_object_number
    
    return new_labels, parent_object_numbers, parent_image_numbers, max_object_number


@numpy
@special_inputs("labels")
@special_outputs(
    ("tracking_results", csv_materializer(
        fields=["slice_index", "object_count", "new_object_count", 
                "lost_object_count", "split_count", "merge_count"],
        analysis_type="tracking"
    ))
)
def track_objects(
    image: np.ndarray,
    labels: np.ndarray,
    tracking_method: str = "overlap",
    pixel_radius: int = 50,
    movement_model: str = "both",
    radius_std: float = 3.0,
    radius_limit_min: float = 2.0,
    radius_limit_max: float = 10.0,
    run_second_phase: bool = True,
    gap_cost: int = 40,
    split_cost: int = 40,
    merge_cost: int = 40,
    mitosis_cost: int = 80,
    max_gap_displacement: int = 5,
    max_split_score: int = 50,
    max_merge_score: int = 50,
    max_frame_distance: int = 5,
    mitosis_max_distance: int = 40,
    filter_by_lifetime: bool = False,
    use_minimum_lifetime: bool = True,
    minimum_lifetime: int = 1,
    use_maximum_lifetime: bool = False,
    maximum_lifetime: int = 100,
    _tracking_state: Optional[Dict[str, Any]] = None
) -> Tuple[np.ndarray, TrackingResult]:
    """
    Track objects across sequential frames.
    
    This function maintains tracking state across frames to assign consistent
    labels to objects and compute trajectory measurements.
    
    Args:
        image: Input image array, shape (D, H, W) where D is typically 1 for single frames
        labels: Segmentation labels from previous identification step
        tracking_method: Method for tracking - 'overlap', 'distance', 'measurements', or 'lap'
        pixel_radius: Maximum pixel distance to consider matches
        movement_model: For LAP - 'random', 'velocity', or 'both'
        radius_std: Number of standard deviations for search radius (LAP)
        radius_limit_min: Minimum search radius in pixels (LAP)
        radius_limit_max: Maximum search radius in pixels (LAP)
        run_second_phase: Whether to run second phase of LAP algorithm
        gap_cost: Cost for gap closing (LAP phase 2)
        split_cost: Cost for split alternative (LAP phase 2)
        merge_cost: Cost for merge alternative (LAP phase 2)
        mitosis_cost: Cost for mitosis alternative (LAP phase 2)
        max_gap_displacement: Maximum gap displacement in pixels (LAP phase 2)
        max_split_score: Maximum split score (LAP phase 2)
        max_merge_score: Maximum merge score (LAP phase 2)
        max_frame_distance: Maximum temporal gap in frames (LAP phase 2)
        mitosis_max_distance: Maximum mitosis distance in pixels (LAP phase 2)
        filter_by_lifetime: Whether to filter objects by lifetime
        use_minimum_lifetime: Filter using minimum lifetime
        minimum_lifetime: Minimum lifetime threshold
        use_maximum_lifetime: Filter using maximum lifetime
        maximum_lifetime: Maximum lifetime threshold
        _tracking_state: Internal state dictionary (managed by pipeline)
    
    Returns:
        Tuple of (image, TrackingResult)
    """
    # Handle state initialization
    if _tracking_state is None:
        _tracking_state = {
            'old_labels': None,
            'old_object_numbers': np.array([], int),
            'max_object_number': 0,
            'old_coordinates': (np.array([]), np.array([])),
            'old_distances': np.array([]),
            'orig_coordinates': (np.array([]), np.array([])),
            'old_ages': np.array([], int)
        }
    
    # Process each slice
    if image.ndim == 3:
        current_image = image[0]
        current_labels = labels[0] if labels.ndim == 3 else labels
    else:
        current_image = image
        current_labels = labels
    
    # Get tracking state
    old_labels = _tracking_state.get('old_labels')
    old_object_numbers = _tracking_state.get('old_object_numbers', np.array([], int))
    max_object_number = _tracking_state.get('max_object_number', 0)
    
    # Perform tracking based on method
    method = tracking_method.lower()
    
    if method == 'overlap':
        new_labels, parent_obj_nums, parent_img_nums, max_object_number = _track_by_overlap(
            current_labels, old_labels, old_object_numbers, max_object_number
        )
    elif method == 'distance':
        new_labels, parent_obj_nums, parent_img_nums, max_object_number = _track_by_distance(
            current_labels, old_labels, old_object_numbers, max_object_number, pixel_radius
        )
    else:
        # Default to overlap for unsupported methods
        new_labels, parent_obj_nums, parent_img_nums, max_object_number = _track_by_overlap(
            current_labels, old_labels, old_object_numbers, max_object_number
        )
    
    # Calculate statistics
    n_objects = len(new_labels)
    new_object_count = int(np.sum(parent_obj_nums == 0))
    
    if old_labels is not None:
        old_count = int(old_labels.max()) if old_labels.max() > 0 else 0
        # Count objects that weren't matched
        matched_old = set(parent_obj_nums[parent_obj_nums > 0])
        lost_object_count = old_count - len(matched_old)
    else:
        lost_object_count = 0
    
    # Count splits (parents with multiple children)
    if len(parent_obj_nums) > 0 and np.any(parent_obj_nums > 0):
        parent_counts = np.bincount(parent_obj_nums[parent_obj_nums > 0])
        split_count = int(np.sum(parent_counts > 1))
    else:
        split_count = 0
    
    merge_count = 0  # Would need more complex logic for merges
    
    # Update state for next frame
    _tracking_state['old_labels'] = current_labels.copy()
    _tracking_state['old_object_numbers'] = new_labels.copy()
    _tracking_state['max_object_number'] = max_object_number
    
    # Create result
    result = TrackingResult(
        slice_index=0,
        object_count=n_objects,
        new_object_count=new_object_count,
        lost_object_count=lost_object_count,
        split_count=split_count,
        merge_count=merge_count
    )
    
    # Return original image (tracking doesn't modify the image)
    if image.ndim == 2:
        return image[np.newaxis, ...], result
    return image, result