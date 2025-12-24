"""
Converted from CellProfiler: MeasureObjectSizeShape
Original: measureobjectsizeshape
"""

import numpy as np
from typing import Tuple, List, Optional, Dict, Any
from dataclasses import dataclass, fields
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_inputs, special_outputs
from openhcs.processing.materialization import csv_materializer

@dataclass
class ObjectSizeShapeMeasurements:
    label: np.ndarray
    area: np.ndarray
    perimeter: np.ndarray
    major_axis_length: np.ndarray
    minor_axis_length: np.ndarray
    eccentricity: np.ndarray
    orientation: np.ndarray
    solidity: np.ndarray
    extent: np.ndarray
    equivalent_diameter: np.ndarray
    centroid_0: np.ndarray
    centroid_1: np.ndarray

@numpy(contract=ProcessingContract.PURE_2D)
@special_inputs("labels")
@special_outputs(("object_measurements", csv_materializer(
    fields=[
        "label", "area", "perimeter", "major_axis_length", 
        "minor_axis_length", "eccentricity", "orientation", 
        "solidity", "extent", "equivalent_diameter", 
        "centroid_0", "centroid_1"
    ],
    analysis_type="object_features"
)))
def measure_object_size_shape(
    image: np.ndarray,
    labels: np.ndarray,
    calculate_advanced: bool = False,
    calculate_zernikes: bool = False
) -> Tuple[np.ndarray, ObjectSizeShapeMeasurements]:
    """
    Measure size and shape features from a label image.
    
    Args:
        image: The original intensity image (unused for shape, but required by signature)
        labels: The label image containing objects to measure
        calculate_advanced: Whether to calculate complex moments (not implemented in this shim)
        calculate_zernikes: Whether to calculate Zernike polynomials (not implemented in this shim)
        
    Returns:
        Original image and a dataclass containing arrays of measurements for each object.
    """
    from skimage.measure import regionprops
    
    # Ensure labels are integers
    labels_int = labels.astype(np.int32)
    
    props = regionprops(labels_int)
    
    if len(props) == 0:
        # Return empty arrays if no objects found
        return image, ObjectSizeShapeMeasurements(
            label=np.array([], dtype=np.int32),
            area=np.array([], dtype=np.float32),
            perimeter=np.array([], dtype=np.float32),
            major_axis_length=np.array([], dtype=np.float32),
            minor_axis_length=np.array([], dtype=np.float32),
            eccentricity=np.array([], dtype=np.float32),
            orientation=np.array([], dtype=np.float32),
            solidity=np.array([], dtype=np.float32),
            extent=np.array([], dtype=np.float32),
            equivalent_diameter=np.array([], dtype=np.float32),
            centroid_0=np.array([], dtype=np.float32),
            centroid_1=np.array([], dtype=np.float32)
        )

    # Extract standard features
    # Note: OpenHCS handles the iteration over D, so we process one 2D slice at a time
    measurements = ObjectSizeShapeMeasurements(
        label=np.array([p.label for p in props], dtype=np.int32),
        area=np.array([p.area for p in props], dtype=np.float32),
        perimeter=np.array([p.perimeter for p in props], dtype=np.float32),
        major_axis_length=np.array([p.major_axis_length for p in props], dtype=np.float32),
        minor_axis_length=np.array([p.minor_axis_length for p in props], dtype=np.float32),
        eccentricity=np.array([p.eccentricity for p in props], dtype=np.float32),
        orientation=np.array([p.orientation for p in props], dtype=np.float32),
        solidity=np.array([p.solidity for p in props], dtype=np.float32),
        extent=np.array([p.extent for p in props], dtype=np.float32),
        equivalent_diameter=np.array([p.equivalent_diameter for p in props], dtype=np.float32),
        centroid_0=np.array([p.centroid[0] for p in props], dtype=np.float32),
        centroid_1=np.array([p.centroid[1] for p in props], dtype=np.float32)
    )

    return image, measurements