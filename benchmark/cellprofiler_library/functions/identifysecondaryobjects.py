"""
Converted from CellProfiler: IdentifySecondaryObjects
Original: IdentifySecondaryObjects.run

Identifies secondary objects (e.g., cells) using primary objects (e.g., nuclei)
as seeds, expanding them based on intensity gradients or distance.
"""

import numpy as np
from typing import Tuple, Optional
from dataclasses import dataclass
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline.function_contracts import special_inputs, special_outputs
from openhcs.processing.materialization import csv_materializer
from openhcs.processing.backends.analysis.cell_counting_cpu import materialize_segmentation_masks


class SecondaryMethod(Enum):
    PROPAGATION = "propagation"
    WATERSHED_GRADIENT = "watershed_gradient"
    WATERSHED_IMAGE = "watershed_image"
    DISTANCE_N = "distance_n"
    DISTANCE_B = "distance_b"


class ThresholdMethod(Enum):
    OTSU = "otsu"
    LI = "li"
    MINIMUM = "minimum"
    TRIANGLE = "triangle"


@dataclass
class SecondaryObjectStats:
    slice_index: int
    object_count: int
    mean_area: float
    median_area: float
    total_area: int
    area_coverage_percent: float
    threshold_value: float


def _fill_labeled_holes(labels: np.ndarray) -> np.ndarray:
    """Fill holes in labeled objects."""
    CellProfiler Parameter Mapping:
    (CellProfiler setting -> Python parameter)
        'Select the input objects' -> (pipeline-handled)
        'Name the objects to be identified' -> (pipeline-handled)
        'Select the method to identify the secondary objects' -> method
        'Select the input image' -> (pipeline-handled)
        'Number of pixels by which to expand the primary objects' -> expansion_distance
        'Regularization factor' -> regularization
        'Discard secondary objects touching the border of the image?' -> exclude_border_objects
        'Discard the associated primary objects?' -> discard_primary
        'Name the new primary objects' -> (pipeline-handled)
        'Fill holes in identified objects?' -> fill_holes
        'Threshold setting version' -> (pipeline-handled)
        'Threshold strategy' -> threshold_strategy
        'Thresholding method' -> threshold_method
        'Threshold smoothing scale' -> threshold_smoothing_scale
        'Threshold correction factor' -> threshold_correction_factor

    CellProfiler Parameter Mapping:
    (CellProfiler setting -> Python parameter)
        'Select the input objects' -> (pipeline-handled)
        'Name the objects to be identified' -> (pipeline-handled)
        'Select the method to identify the secondary objects' -> method
        'Select the input image' -> (pipeline-handled)
        'Number of pixels by which to expand the primary objects' -> expansion_distance
        'Regularization factor' -> regularization
        'Discard secondary objects touching the border of the image?' -> exclude_border_objects
        'Discard the associated primary objects?' -> discard_primary
        'Name the new primary objects' -> (pipeline-handled)
        'Fill holes in identified objects?' -> fill_holes
        'Threshold setting version' -> (pipeline-handled)
        'Threshold strategy' -> threshold_strategy
        'Thresholding method' -> threshold_method
        'Threshold smoothing scale' -> threshold_smoothing_scale
        'Threshold correction factor' -> threshold_correction_factor

    CellProfiler Parameter Mapping:
    (CellProfiler setting -> Python parameter)
        'Select the input objects' -> (pipeline-handled)
        'Name the objects to be identified' -> (pipeline-handled)
        'Select the method to identify the secondary objects' -> method
        'Select the input image' -> (pipeline-handled)
        'Number of pixels by which to expand the primary objects' -> expansion_distance
        'Regularization factor' -> regularization
        'Discard secondary objects touching the border of the image?' -> exclude_border_objects
        'Discard the associated primary objects?' -> discard_primary
        'Name the new primary objects' -> (pipeline-handled)
        'Fill holes in identified objects?' -> fill_holes
        'Threshold setting version' -> (pipeline-handled)
        'Threshold strategy' -> threshold_strategy
        'Thresholding method' -> threshold_method
        'Threshold smoothing scale' -> threshold_smoothing_scale
        'Threshold correction factor' -> threshold_correction_factor

    from scipy.ndimage import binary_fill_holes
    
    filled = np.zeros_like(labels)
    for label_id in range(1, labels.max() + 1):
        mask = labels == label_id
        filled_mask = binary_fill_holes(mask)
        filled[filled_mask] = label_id
    return filled


def _propagate_labels(
    image: np.ndarray,
    labels: np.ndarray,
    mask: np.ndarray,
    regularization: float
) -> np.ndarray:
    """Propagate labels using intensity-weighted distance.
    
    This is a simplified implementation of the propagation algorithm.
    Uses watershed with modified distance metric.
    """
    from scipy.ndimage import distance_transform_edt
    from skimage.segmentation import watershed
    
    if labels.max() == 0:
        return labels.copy()
    
    # Compute gradient magnitude for edge detection
    from scipy.ndimage import sobel
    gradient = np.abs(sobel(image, axis=0)) + np.abs(sobel(image, axis=1))
    
    # Combine distance and gradient information
    # Higher regularization = more weight on distance
    distance = distance_transform_edt(labels == 0)
    
    if regularization > 0:
        # Combine gradient and distance
        combined = gradient + regularization * distance
    else:
        combined = gradient
    
    # Use watershed to propagate labels
    result = watershed(combined, markers=labels, mask=mask)
    
    return result


@numpy
@special_inputs("primary_labels")
@special_outputs(
    ("secondary_stats", csv_materializer(
        fields=["slice_index", "object_count", "mean_area", "median_area", 
                "total_area", "area_coverage_percent", "threshold_value"],
        analysis_type="secondary_objects"
    )),
    ("secondary_labels", materialize_segmentation_masks)
)
def identify_secondary_objects(
    image: np.ndarray,
    primary_labels: np.ndarray,
    method: SecondaryMethod = SecondaryMethod.PROPAGATION,
    threshold_method: ThresholdMethod = ThresholdMethod.OTSU,
    threshold_correction_factor: float = 1.0,
    threshold_min: float = 0.0,
    threshold_max: float = 1.0,
    distance_to_dilate: int = 10,
    regularization_factor: float = 0.05,
    fill_holes: bool = True,
    discard_edge_objects: bool = False,
) -> Tuple[np.ndarray, SecondaryObjectStats, np.ndarray]:
    """
    Identify secondary objects using primary objects as seeds.
    
    Args:
        image: Input intensity image, shape (2, H, W) where [0] is intensity, [1] is primary labels
               OR shape (H, W) if primary_labels provided separately
        primary_labels: Label image of primary objects (seeds)
        method: Method for identifying secondary objects
        threshold_method: Method for thresholding the image
        threshold_correction_factor: Factor to multiply threshold by
        threshold_min: Minimum threshold value
        threshold_max: Maximum threshold value  
        distance_to_dilate: Pixels to expand for distance methods
        regularization_factor: Lambda for propagation method (0=gradient only, higher=more distance)
        fill_holes: Whether to fill holes in identified objects
        discard_edge_objects: Whether to discard objects touching image border
        
    Returns:
        Tuple of (image, stats, secondary_labels)
    """
    from scipy.ndimage import distance_transform_edt, sobel, binary_erosion
    from skimage.segmentation import watershed
    from skimage.filters import threshold_otsu, threshold_li, threshold_minimum, threshold_triangle
    from skimage.measure import regionprops, label as relabel
    
    # Handle input - image should be intensity image
    if image.ndim == 3 and image.shape[0] == 2:
        # Stacked input: [intensity, primary_labels]
        img = image[0].astype(np.float64)
        labels_in = image[1].astype(np.int32)
    else:
        img = image.astype(np.float64)
        labels_in = primary_labels.astype(np.int32)
    
    # Normalize image to 0-1 range
    if img.max() > img.min():
        img = (img - img.min()) / (img.max() - img.min())
    
    H, W = img.shape
    
    # Calculate threshold for methods that need it
    threshold_value = 0.0
    if method != SecondaryMethod.DISTANCE_N:
        if threshold_method == ThresholdMethod.OTSU:
            threshold_value = threshold_otsu(img)
        elif threshold_method == ThresholdMethod.LI:
            threshold_value = threshold_li(img)
        elif threshold_method == ThresholdMethod.MINIMUM:
            try:
                threshold_value = threshold_minimum(img)
            except RuntimeError:
                threshold_value = threshold_otsu(img)
        elif threshold_method == ThresholdMethod.TRIANGLE:
            threshold_value = threshold_triangle(img)
        else:
            threshold_value = threshold_otsu(img)
        
        # Apply correction and bounds
        threshold_value = threshold_value * threshold_correction_factor
        threshold_value = max(threshold_min, min(threshold_max, threshold_value))
        
        thresholded = img > threshold_value
    else:
        thresholded = np.ones_like(img, dtype=bool)
    
    # Identify secondary objects based on method
    if method == SecondaryMethod.DISTANCE_N:
        # Pure distance expansion - no thresholding
        if labels_in.max() == 0:
            labels_out = np.zeros_like(labels_in)
        else:
            distances, indices = distance_transform_edt(
                labels_in == 0, return_indices=True
            )
            labels_out = np.zeros_like(labels_in)
            dilate_mask = distances <= distance_to_dilate
            labels_out[dilate_mask] = labels_in[
                indices[0][dilate_mask], 
                indices[1][dilate_mask]
            ]
    
    elif method == SecondaryMethod.DISTANCE_B:
        # Distance expansion with threshold masking
        if labels_in.max() == 0:
            labels_out = np.zeros_like(labels_in)
        else:
            # Create mask from threshold
            mask = thresholded | (labels_in > 0)
            
            # Propagate with distance limit
            labels_out = _propagate_labels(img, labels_in, mask, 1.0)
            
            # Apply distance limit
            distances = distance_transform_edt(labels_in == 0)
            labels_out[distances > distance_to_dilate] = 0
            
            # Ensure primary objects are preserved
            labels_out[labels_in > 0] = labels_in[labels_in > 0]
    
    elif method == SecondaryMethod.PROPAGATION:
        # Propagation method - combines distance and intensity
        if labels_in.max() == 0:
            labels_out = np.zeros_like(labels_in)
        else:
            mask = thresholded | (labels_in > 0)
            labels_out = _propagate_labels(
                img, labels_in, mask, regularization_factor
            )
    
    elif method == SecondaryMethod.WATERSHED_GRADIENT:
        # Watershed on gradient image
        if labels_in.max() == 0:
            labels_out = np.zeros_like(labels_in)
        else:
            sobel_image = np.abs(sobel(img, axis=0)) + np.abs(sobel(img, axis=1))
            mask = thresholded | (labels_in > 0)
            labels_out = watershed(
                sobel_image,
                markers=labels_in,
                mask=mask,
                connectivity=2
            )
    
    elif method == SecondaryMethod.WATERSHED_IMAGE:
        # Watershed on inverted intensity image
        if labels_in.max() == 0:
            labels_out = np.zeros_like(labels_in)
        else:
            inverted = 1.0 - img
            mask = thresholded | (labels_in > 0)
            labels_out = watershed(
                inverted,
                markers=labels_in,
                mask=mask,
                connectivity=2
            )
    else:
        labels_out = labels_in.copy()
    
    # Fill holes if requested
    if fill_holes and labels_out.max() > 0:
        labels_out = _fill_labeled_holes(labels_out)
    
    # Discard edge objects if requested
    if discard_edge_objects and labels_out.max() > 0:
        edge_labels = np.unique(np.concatenate([
            labels_out[0, :],
            labels_out[-1, :],
            labels_out[:, 0],
            labels_out[:, -1]
        ]))
        for edge_label in edge_labels:
            if edge_label > 0:
                labels_out[labels_out == edge_label] = 0
        
        # Relabel to ensure consecutive labels
        if labels_out.max() > 0:
            labels_out = relabel(labels_out > 0) * (labels_out > 0).astype(np.int32)
            # Preserve original label mapping where possible
            unique_labels = np.unique(labels_out)
            unique_labels = unique_labels[unique_labels > 0]
            new_labels = np.zeros_like(labels_out)
            for i, lbl in enumerate(unique_labels, 1):
                new_labels[labels_out == lbl] = i
            labels_out = new_labels
    
    # Compute statistics
    labels_out = labels_out.astype(np.int32)
    object_count = int(labels_out.max())
    
    if object_count > 0:
        props = regionprops(labels_out)
        areas = [p.area for p in props]
        mean_area = float(np.mean(areas))
        median_area = float(np.median(areas))
        total_area = int(np.sum(areas))
    else:
        mean_area = 0.0
        median_area = 0.0
        total_area = 0
    
    area_coverage = 100.0 * total_area / (H * W) if (H * W) > 0 else 0.0
    
    stats = SecondaryObjectStats(
        slice_index=0,
        object_count=object_count,
        mean_area=mean_area,
        median_area=median_area,
        total_area=total_area,
        area_coverage_percent=area_coverage,
        threshold_value=float(threshold_value)
    )
    
    return img.astype(np.float32), stats, labels_out