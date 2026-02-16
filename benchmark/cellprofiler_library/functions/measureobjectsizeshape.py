"""
Converted from CellProfiler: MeasureObjectSizeShape
Original: measureobjectsizeshape
"""

import numpy as np
from typing import Tuple, List, Dict, Any, Optional
from dataclasses import dataclass, field
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline.function_contracts import special_inputs, special_outputs
from openhcs.processing.materialization import csv_materializer


@dataclass
class ObjectSizeShapeMeasurement:
    """Measurements for object size and shape features."""
    slice_index: int
    object_label: int
    area: float
    perimeter: float
    major_axis_length: float
    minor_axis_length: float
    eccentricity: float
    orientation: float
    solidity: float
    extent: float
    equivalent_diameter: float
    euler_number: int
    compactness: float
    form_factor: float
    centroid_y: float
    centroid_x: float
    bbox_min_row: int
    bbox_min_col: int
    bbox_max_row: int
    bbox_max_col: int


@dataclass
class ObjectSizeShapeResults:
    """Collection of measurements for all objects in a slice."""
    slice_index: int
    object_count: int
    measurements: List[Dict[str, Any]] = field(default_factory=list)


def _get_zernike_indexes(n_max: int) -> List[Tuple[int, int]]:
    """Get Zernike polynomial indexes up to order n_max."""
    CellProfiler Parameter Mapping:
    (CellProfiler setting -> Python parameter)
        'Select object sets to measure' -> (pipeline-handled)
        'Calculate the Zernike features?' -> calculate_zernikes
        'Calculate the advanced features?' -> calculate_advanced
        'Calculate 3D measurements?' -> volumetric
        'Object spacing' -> spacing

    CellProfiler Parameter Mapping:
    (CellProfiler setting -> Python parameter)
        'Select object sets to measure' -> (pipeline-handled)
        'Calculate the Zernike features?' -> calculate_zernikes
        'Calculate the advanced features?' -> calculate_advanced
        'Calculate 3D measurements?' -> volumetric
        'Object spacing' -> spacing

    CellProfiler Parameter Mapping:
    (CellProfiler setting -> Python parameter)
        'Select object sets to measure' -> (pipeline-handled)
        'Calculate the Zernike features?' -> calculate_zernikes
        'Calculate the advanced features?' -> calculate_advanced
        'Calculate 3D measurements?' -> volumetric
        'Object spacing' -> spacing

    indexes = []
    for n in range(n_max + 1):
        for m in range(-n, n + 1, 2):
            indexes.append((n, abs(m)))
    return indexes


def _compute_zernike_moments(image: np.ndarray, n_max: int = 9) -> Dict[str, float]:
    """Compute Zernike moments for a binary object image."""
    from scipy.ndimage import center_of_mass
    
    zernike_features = {}
    indexes = _get_zernike_indexes(n_max)
    
    if image.sum() == 0:
        for n, m in indexes:
            zernike_features[f"Zernike_{n}_{m}"] = 0.0
        return zernike_features
    
    # Normalize image to unit disk
    y, x = np.ogrid[:image.shape[0], :image.shape[1]]
    cy, cx = center_of_mass(image)
    
    # Radius to normalize
    radius = max(image.shape) / 2
    if radius == 0:
        radius = 1
    
    # Normalized coordinates
    y_norm = (y - cy) / radius
    x_norm = (x - cx) / radius
    
    rho = np.sqrt(x_norm**2 + y_norm**2)
    theta = np.arctan2(y_norm, x_norm)
    
    # Mask for unit disk
    mask = (rho <= 1) & (image > 0)
    
    for n, m in indexes:
        # Simplified Zernike computation
        if mask.sum() > 0:
            # Radial polynomial (simplified)
            r_nm = rho ** n
            if m == 0:
                z_nm = r_nm
            else:
                z_nm = r_nm * np.cos(m * theta)
            
            moment = np.abs(np.sum(image[mask] * z_nm[mask])) / mask.sum()
            zernike_features[f"Zernike_{n}_{m}"] = float(moment)
        else:
            zernike_features[f"Zernike_{n}_{m}"] = 0.0
    
    return zernike_features


@numpy(contract=ProcessingContract.PURE_2D)
@special_inputs("labels")
@special_outputs(("size_shape_measurements", csv_materializer(
    fields=["slice_index", "object_label", "area", "perimeter", 
            "major_axis_length", "minor_axis_length", "eccentricity",
            "orientation", "solidity", "extent", "equivalent_diameter",
            "euler_number", "compactness", "form_factor",
            "centroid_y", "centroid_x", "bbox_min_row", "bbox_min_col",
            "bbox_max_row", "bbox_max_col"],
    analysis_type="object_size_shape"
)))
def measure_object_size_shape(
    image: np.ndarray,
    labels: np.ndarray,
    calculate_advanced: bool = True,
    calculate_zernikes: bool = True,
) -> Tuple[np.ndarray, List[ObjectSizeShapeMeasurement]]:
    """
    Measure size and shape features of labeled objects.
    
    Args:
        image: Input intensity image (H, W)
        labels: Label image where each object has unique integer label (H, W)
        calculate_advanced: Whether to calculate advanced features like moments
        calculate_zernikes: Whether to calculate Zernike moments
    
    Returns:
        Tuple of (original image, list of measurements per object)
    """
    from skimage.measure import regionprops, label as relabel
    
    measurements = []
    
    # Handle empty labels
    if labels.max() == 0:
        return image, measurements
    
    # Ensure labels are properly formatted
    labels_int = labels.astype(np.int32)
    
    # Get region properties
    props = regionprops(labels_int, intensity_image=image)
    
    for prop in props:
        # Basic measurements
        area = float(prop.area)
        perimeter = float(prop.perimeter) if hasattr(prop, 'perimeter') else 0.0
        
        # Axis lengths
        major_axis = float(prop.major_axis_length) if prop.major_axis_length else 0.0
        minor_axis = float(prop.minor_axis_length) if prop.minor_axis_length else 0.0
        
        # Shape descriptors
        eccentricity = float(prop.eccentricity) if hasattr(prop, 'eccentricity') else 0.0
        orientation = float(prop.orientation) if hasattr(prop, 'orientation') else 0.0
        solidity = float(prop.solidity) if hasattr(prop, 'solidity') else 0.0
        extent = float(prop.extent) if hasattr(prop, 'extent') else 0.0
        equivalent_diameter = float(prop.equivalent_diameter) if hasattr(prop, 'equivalent_diameter') else 0.0
        euler_number = int(prop.euler_number) if hasattr(prop, 'euler_number') else 0
        
        # Derived features
        # Compactness = perimeter^2 / (4 * pi * area)
        if area > 0:
            compactness = (perimeter ** 2) / (4 * np.pi * area)
        else:
            compactness = 0.0
        
        # Form factor = 4 * pi * area / perimeter^2
        if perimeter > 0:
            form_factor = (4 * np.pi * area) / (perimeter ** 2)
        else:
            form_factor = 0.0
        
        # Centroid
        centroid = prop.centroid
        centroid_y = float(centroid[0])
        centroid_x = float(centroid[1])
        
        # Bounding box
        bbox = prop.bbox
        bbox_min_row = int(bbox[0])
        bbox_min_col = int(bbox[1])
        bbox_max_row = int(bbox[2])
        bbox_max_col = int(bbox[3])
        
        measurement = ObjectSizeShapeMeasurement(
            slice_index=0,
            object_label=int(prop.label),
            area=area,
            perimeter=perimeter,
            major_axis_length=major_axis,
            minor_axis_length=minor_axis,
            eccentricity=eccentricity,
            orientation=orientation,
            solidity=solidity,
            extent=extent,
            equivalent_diameter=equivalent_diameter,
            euler_number=euler_number,
            compactness=compactness,
            form_factor=form_factor,
            centroid_y=centroid_y,
            centroid_x=centroid_x,
            bbox_min_row=bbox_min_row,
            bbox_min_col=bbox_min_col,
            bbox_max_row=bbox_max_row,
            bbox_max_col=bbox_max_col,
        )
        
        measurements.append(measurement)
    
    return image, measurements