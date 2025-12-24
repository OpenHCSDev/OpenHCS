"""Converted from CellProfiler: MakeProjection

MakeProjection combines two or more two-dimensional images of the same
field of view into a single two-dimensional image by performing a
mathematical operation at each pixel position.
"""

import numpy as np
from typing import Tuple
from dataclasses import dataclass
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_outputs
from openhcs.processing.materialization import csv_materializer


class ProjectionType(Enum):
    AVERAGE = "average"
    MAXIMUM = "maximum"
    MINIMUM = "minimum"
    SUM = "sum"
    VARIANCE = "variance"
    POWER = "power"
    BRIGHTFIELD = "brightfield"
    MASK = "mask"


@dataclass
class ProjectionStats:
    projection_type: str
    input_slices: int
    output_min: float
    output_max: float
    output_mean: float


@numpy(contract=ProcessingContract.VOLUMETRIC_TO_SLICE)
@special_outputs(("projection_stats", csv_materializer(
    fields=["projection_type", "input_slices", "output_min", "output_max", "output_mean"],
    analysis_type="projection"
)))
def make_projection(
    image: np.ndarray,
    projection_type: ProjectionType = ProjectionType.AVERAGE,
    frequency: float = 6.0,
) -> Tuple[np.ndarray, ProjectionStats]:
    """
    Combine a stack of 2D images into a single 2D projection image.
    
    Args:
        image: Input image stack with shape (D, H, W) where D is the number
               of slices/frames to combine.
        projection_type: Method for combining images:
            - AVERAGE: Mean pixel intensity across stack
            - MAXIMUM: Maximum pixel value (max intensity projection)
            - MINIMUM: Minimum pixel value
            - SUM: Sum of all pixel values
            - VARIANCE: Variance at each pixel position
            - POWER: Power at given frequency (experimental)
            - BRIGHTFIELD: Brightfield projection for dust artifact removal
            - MASK: Binary image of pixels masked in any input
        frequency: For POWER projection, the frequency in Z-stack steps.
                   Pixels cycling every N slices score highest at frequency=N.
    
    Returns:
        Tuple of (projected_image, projection_stats)
        projected_image: 2D array (H, W) with the projection result
        projection_stats: Statistics about the projection
    """
    # Handle edge case of single slice
    if image.ndim == 2:
        image = image[np.newaxis, :, :]
    
    d, h, w = image.shape
    
    if projection_type == ProjectionType.AVERAGE:
        result = np.mean(image, axis=0).astype(np.float32)
        
    elif projection_type == ProjectionType.MAXIMUM:
        result = np.max(image, axis=0).astype(np.float32)
        
    elif projection_type == ProjectionType.MINIMUM:
        result = np.min(image, axis=0).astype(np.float32)
        
    elif projection_type == ProjectionType.SUM:
        result = np.sum(image, axis=0).astype(np.float32)
        
    elif projection_type == ProjectionType.VARIANCE:
        # Variance method from Selinummi et al (2009)
        # Background pixels have uniform illumination, cytoplasm has higher variance
        result = np.var(image.astype(np.float64), axis=0).astype(np.float32)
        
    elif projection_type == ProjectionType.POWER:
        # Compute power at given frequency through Z-stack
        # Uses Fourier analysis to find pixels varying at specific frequency
        image_float = image.astype(np.float64)
        vsum = np.sum(image_float, axis=0)
        
        # Compute complex power image
        power_image = np.zeros((h, w), dtype=np.complex128)
        power_mask = np.zeros((h, w), dtype=np.complex128)
        
        for i in range(d):
            multiplier = np.exp(2j * np.pi * float(i) / frequency)
            power_image += multiplier * image_float[i]
            power_mask += multiplier
        
        # Subtract DC component and compute power
        power_image -= vsum * power_mask / d
        result = (power_image * np.conj(power_image)).real.astype(np.float32)
        
    elif projection_type == ProjectionType.BRIGHTFIELD:
        # Brightfield projection for dust artifact removal
        # Normalize each slice to first slice's mean
        image_float = image.astype(np.float64)
        norm0 = np.mean(image_float[0])
        
        bright_max = image_float[0].copy()
        bright_min = image_float[0].copy()
        
        for i in range(1, d):
            norm = np.mean(image_float[i])
            if norm > 0:
                normalized = image_float[i] * norm0 / norm
            else:
                normalized = image_float[i]
            
            # Update max and min, resetting min when max changes
            max_mask = bright_max < normalized
            min_mask = bright_min > normalized
            
            bright_min[min_mask] = normalized[min_mask]
            bright_max[max_mask] = normalized[max_mask]
            bright_min[max_mask] = bright_max[max_mask]
        
        result = (bright_max - bright_min).astype(np.float32)
        
    elif projection_type == ProjectionType.MASK:
        # Binary image: 1 where all images are valid, 0 where any is masked
        # Since we don't have explicit masks, treat zeros as masked
        mask = np.all(image > 0, axis=0)
        result = mask.astype(np.float32)
        
    else:
        raise ValueError(f"Unknown projection type: {projection_type}")
    
    # Compute statistics
    stats = ProjectionStats(
        projection_type=projection_type.value,
        input_slices=d,
        output_min=float(np.min(result)),
        output_max=float(np.max(result)),
        output_mean=float(np.mean(result))
    )
    
    return result, stats