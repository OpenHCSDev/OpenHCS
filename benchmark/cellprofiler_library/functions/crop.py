"""
Converted from CellProfiler: Crop
Original: crop
"""

import numpy as np
from typing import Tuple, Optional
from dataclasses import dataclass
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_inputs, special_outputs
from openhcs.processing.materialization import csv_materializer

class RemovalMethod(Enum):
    RECTANGLE = "Rectangle"
    SHAPE = "Shape"

@dataclass
class CropMeasurements:
    original_area: int
    area_retained: int

@numpy(contract=ProcessingContract.FLEXIBLE)
@special_inputs("cropping_mask")
@special_outputs(
    ("cropped_mask",),
    ("crop_measurements", csv_materializer(fields=["original_area", "area_retained"]))
)
def crop(
    image: np.ndarray,
    cropping_mask: np.ndarray,
    removal_method: RemovalMethod = RemovalMethod.RECTANGLE,
) -> Tuple[np.ndarray, np.ndarray, CropMeasurements]:
    """
    Crops an image based on a provided cropping mask.
    
    Args:
        image: Input image (D, H, W)
        cropping_mask: Mask defining the region to keep (1, H, W) or (D, H, W)
        removal_method: How to treat the area outside the crop (Rectangle or Shape)
        
    Returns:
        cropped_image: The image with pixels outside the mask removed/zeroed
        cropped_mask: The mask used for cropping
        measurements: Area statistics
    """
    # Ensure cropping_mask is boolean
    mask = cropping_mask.astype(bool)
    
    # Handle potential dimension mismatch (e.g., single mask for all channels)
    if mask.shape[0] == 1 and image.shape[0] > 1:
        mask = np.repeat(mask, image.shape[0], axis=0)

    # Calculate measurements before modification
    # Note: We use the first slice for area calculations to represent the spatial footprint
    original_area = image.shape[1] * image.shape[2]
    area_retained = int(np.sum(mask[0]))

    # Implementation of cropping logic
    if removal_method == RemovalMethod.RECTANGLE:
        # Find the bounding box of the mask
        coords = np.argwhere(mask)
        if coords.size > 0:
            # Get min/max for H and W (indices 1 and 2)
            y_min, x_min = coords[:, 1].min(), coords[:, 2].min()
            y_max, x_max = coords[:, 1].max(), coords[:, 2].max()
            
            # Create a rectangular mask based on the bounding box
            rect_mask = np.zeros_like(mask)
            rect_mask[:, y_min:y_max+1, x_min:x_max+1] = True
            
            # Apply rectangular mask
            cropped_pixel_data = np.where(rect_mask, image, 0)
            final_mask = rect_mask.astype(np.uint8)
        else:
            cropped_pixel_data = np.zeros_like(image)
            final_mask = np.zeros_like(mask, dtype=np.uint8)
            
    else: # RemovalMethod.SHAPE
        # Apply the exact shape of the mask
        cropped_pixel_data = np.where(mask, image, 0)
        final_mask = mask.astype(np.uint8)

    measurements = CropMeasurements(
        original_area=original_area,
        area_retained=area_retained
    )

    return cropped_pixel_data, final_mask, measurements