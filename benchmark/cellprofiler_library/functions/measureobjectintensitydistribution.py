"""Converted from CellProfiler: MeasureObjectIntensityDistribution"""

import numpy as np
from typing import Tuple, List, Optional
from dataclasses import dataclass, field
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_inputs, special_outputs
from openhcs.processing.materialization import csv_materializer


class CenterChoice(Enum):
    SELF = "self"
    CENTERS_OF_OTHER = "centers_of_other"
    EDGES_OF_OTHER = "edges_of_other"


class ZernikeMode(Enum):
    NONE = "none"
    MAGNITUDES = "magnitudes"
    MAGNITUDES_AND_PHASE = "magnitudes_and_phase"


@dataclass
class RadialDistributionMeasurement:
    """Measurements for radial intensity distribution."""
    object_label: int
    bin_index: int
    bin_count: int
    frac_at_d: float
    mean_frac: float
    radial_cv: float


@dataclass
class ZernikeMeasurement:
    """Zernike moment measurements."""
    object_label: int
    n: int
    m: int
    magnitude: float
    phase: Optional[float] = None


@numpy(contract=ProcessingContract.FLEXIBLE)
@special_inputs("labels")
@special_outputs(
    ("radial_measurements", csv_materializer(
        fields=["object_label", "bin_index", "bin_count", "frac_at_d", "mean_frac", "radial_cv"],
        analysis_type="radial_distribution"
    ))
)
def measure_object_intensity_distribution(
    image: np.ndarray,
    labels: np.ndarray,
    bin_count: int = 4,
    wants_scaled: bool = True,
    maximum_radius: int = 100,
    wants_zernikes: ZernikeMode = ZernikeMode.NONE,
    zernike_degree: int = 9,
    center_choice: CenterChoice = CenterChoice.SELF,
) -> Tuple[np.ndarray, List[RadialDistributionMeasurement]]:
    """
    Measure the spatial distribution of intensities within each object.
    
    Measures intensity distribution from each object's center to its boundary
    within a set of bins (rings).
    
    Args:
        image: Input grayscale image, shape (D, H, W) or (H, W)
        labels: Object labels, same spatial shape as image
        bin_count: Number of radial bins
        wants_scaled: If True, scale bins per-object; if False, use fixed radius
        maximum_radius: Maximum radius for unscaled bins (pixels)
        wants_zernikes: Whether to calculate Zernike moments
        zernike_degree: Maximum Zernike radial moment
        center_choice: How to determine object centers
    
    Returns:
        Tuple of (original image, list of measurements)
    """
    from scipy import ndimage as ndi
    from scipy import sparse
    from skimage.morphology import erosion, disk
    from skimage.measure import regionprops, label as sklabel
    
    # Handle dimensionality
    if image.ndim == 3:
        # Process first slice for now (2D module)
        img_2d = image[0]
        if labels.ndim == 3:
            labels_2d = labels[0]
        else:
            labels_2d = labels
    else:
        img_2d = image
        labels_2d = labels
    
    measurements = []
    
    nobjects = int(np.max(labels_2d))
    if nobjects == 0:
        # Return empty measurements
        return image, measurements
    
    # Compute distance to edge for each labeled pixel
    d_to_edge = _distance_to_edge(labels_2d)
    
    # Find centers (point farthest from edge in each object)
    centers_i, centers_j = _find_object_centers(labels_2d, d_to_edge, nobjects)
    
    # Compute distance from center for each pixel
    d_from_center, center_labels = _compute_distance_from_centers(
        labels_2d, centers_i, centers_j, nobjects
    )
    
    good_mask = labels_2d > 0
    
    # Compute normalized distance
    normalized_distance = np.zeros(labels_2d.shape, dtype=np.float64)
    if wants_scaled:
        total_distance = d_from_center + d_to_edge
        normalized_distance[good_mask] = d_from_center[good_mask] / (
            total_distance[good_mask] + 0.001
        )
    else:
        normalized_distance[good_mask] = d_from_center[good_mask] / maximum_radius
    
    # Assign pixels to bins
    bin_indexes = (normalized_distance * bin_count).astype(int)
    bin_indexes[bin_indexes > bin_count] = bin_count
    
    ngood_pixels = np.sum(good_mask)
    good_labels = labels_2d[good_mask]
    
    # Build sparse histogram of intensities per object per bin
    labels_and_bins = (good_labels - 1, bin_indexes[good_mask])
    
    histogram = sparse.coo_matrix(
        (img_2d[good_mask], labels_and_bins),
        shape=(nobjects, bin_count + 1)
    ).toarray()
    
    sum_by_object = np.sum(histogram, axis=1, keepdims=True)
    sum_by_object[sum_by_object == 0] = 1  # Avoid division by zero
    fraction_at_distance = histogram / sum_by_object
    
    # Count pixels per object per bin
    number_at_distance = sparse.coo_matrix(
        (np.ones(ngood_pixels), labels_and_bins),
        shape=(nobjects, bin_count + 1)
    ).toarray()
    
    object_mask = number_at_distance > 0
    
    sum_pixels_by_object = np.sum(number_at_distance, axis=1, keepdims=True)
    sum_pixels_by_object[sum_pixels_by_object == 0] = 1
    fraction_at_bin = number_at_distance / sum_pixels_by_object
    
    mean_pixel_fraction = fraction_at_distance / (fraction_at_bin + np.finfo(float).eps)
    
    # Compute radial CV (coefficient of variation across 8 wedges)
    i_grid, j_grid = np.mgrid[0:labels_2d.shape[0], 0:labels_2d.shape[1]]
    
    i_center_map = np.zeros(labels_2d.shape)
    j_center_map = np.zeros(labels_2d.shape)
    for obj_idx in range(nobjects):
        obj_mask = labels_2d == (obj_idx + 1)
        i_center_map[obj_mask] = centers_i[obj_idx]
        j_center_map[obj_mask] = centers_j[obj_idx]
    
    # Compute wedge index (8 wedges based on position relative to center)
    imask = (i_grid[good_mask] > i_center_map[good_mask]).astype(int)
    jmask = (j_grid[good_mask] > j_center_map[good_mask]).astype(int)
    absmask = (np.abs(i_grid[good_mask] - i_center_map[good_mask]) > 
               np.abs(j_grid[good_mask] - j_center_map[good_mask])).astype(int)
    radial_index = imask + jmask * 2 + absmask * 4
    
    # Compute measurements for each bin
    n_bins = bin_count if wants_scaled else bin_count + 1
    
    for bin_idx in range(n_bins):
        bin_mask = good_mask & (bin_indexes == bin_idx)
        bin_pixels = np.sum(bin_mask)
        
        if bin_pixels == 0:
            # Add zero measurements for all objects
            for obj_idx in range(nobjects):
                measurements.append(RadialDistributionMeasurement(
                    object_label=obj_idx + 1,
                    bin_index=bin_idx + 1,
                    bin_count=bin_count,
                    frac_at_d=0.0,
                    mean_frac=0.0,
                    radial_cv=0.0
                ))
            continue
        
        bin_labels = labels_2d[bin_mask]
        bin_radial_index = radial_index[bin_indexes[good_mask] == bin_idx]
        
        # Compute radial CV for this bin
        labels_and_radii = (bin_labels - 1, bin_radial_index)
        
        radial_values = sparse.coo_matrix(
            (img_2d[bin_mask], labels_and_radii),
            shape=(nobjects, 8)
        ).toarray()
        
        pixel_count = sparse.coo_matrix(
            (np.ones(bin_pixels), labels_and_radii),
            shape=(nobjects, 8)
        ).toarray()
        
        with np.errstate(divide='ignore', invalid='ignore'):
            radial_means = np.where(pixel_count > 0, radial_values / pixel_count, 0)
            radial_cv = np.std(radial_means, axis=1) / (np.mean(radial_means, axis=1) + np.finfo(float).eps)
            radial_cv[np.sum(pixel_count > 0, axis=1) == 0] = 0
        
        # Store measurements for each object
        for obj_idx in range(nobjects):
            measurements.append(RadialDistributionMeasurement(
                object_label=obj_idx + 1,
                bin_index=bin_idx + 1,
                bin_count=bin_count,
                frac_at_d=float(fraction_at_distance[obj_idx, bin_idx]),
                mean_frac=float(mean_pixel_fraction[obj_idx, bin_idx]),
                radial_cv=float(radial_cv[obj_idx])
            ))
    
    return image, measurements


def _distance_to_edge(labels: np.ndarray) -> np.ndarray:
    """Compute distance to edge for each labeled pixel."""
    from scipy import ndimage as ndi
    
    d_to_edge = np.zeros(labels.shape, dtype=np.float64)
    
    for obj_label in range(1, int(np.max(labels)) + 1):
        obj_mask = labels == obj_label
        if np.sum(obj_mask) == 0:
            continue
        # Distance transform from background
        dist = ndi.distance_transform_edt(obj_mask)
        d_to_edge[obj_mask] = dist[obj_mask]
    
    return d_to_edge


def _find_object_centers(labels: np.ndarray, d_to_edge: np.ndarray, nobjects: int):
    """Find the center of each object (point farthest from edge)."""
    centers_i = np.zeros(nobjects, dtype=np.float64)
    centers_j = np.zeros(nobjects, dtype=np.float64)
    
    for obj_idx in range(nobjects):
        obj_mask = labels == (obj_idx + 1)
        if np.sum(obj_mask) == 0:
            continue
        
        # Find point with maximum distance to edge
        obj_distances = d_to_edge.copy()
        obj_distances[~obj_mask] = -1
        max_idx = np.argmax(obj_distances)
        centers_i[obj_idx], centers_j[obj_idx] = np.unravel_index(max_idx, labels.shape)
    
    return centers_i, centers_j


def _compute_distance_from_centers(
    labels: np.ndarray,
    centers_i: np.ndarray,
    centers_j: np.ndarray,
    nobjects: int
) -> Tuple[np.ndarray, np.ndarray]:
    """Compute distance from center for each pixel."""
    from scipy import ndimage as ndi
    
    d_from_center = np.zeros(labels.shape, dtype=np.float64)
    center_labels = np.zeros(labels.shape, dtype=np.int32)
    
    i_grid, j_grid = np.mgrid[0:labels.shape[0], 0:labels.shape[1]]
    
    for obj_idx in range(nobjects):
        obj_mask = labels == (obj_idx + 1)
        if np.sum(obj_mask) == 0:
            continue
        
        ci, cj = centers_i[obj_idx], centers_j[obj_idx]
        
        # Euclidean distance from center
        dist = np.sqrt((i_grid - ci)**2 + (j_grid - cj)**2)
        d_from_center[obj_mask] = dist[obj_mask]
        center_labels[obj_mask] = obj_idx + 1
    
    return d_from_center, center_labels