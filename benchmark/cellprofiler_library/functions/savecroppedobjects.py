"""
Converted from CellProfiler: SaveCroppedObjects
Original: savecroppedobjects
"""

import numpy as np
import os
from typing import Tuple, Optional
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_inputs

class ExportFormat(Enum):
    MASKS = "masks"
    IMAGE = "image"

class FileFormat(Enum):
    TIFF8 = "tiff8"
    TIFF16 = "tiff16"
    PNG = "png"

@numpy(contract=ProcessingContract.FLEXIBLE)
@special_inputs("labels")
def save_cropped_objects(
    image: np.ndarray,
    labels: np.ndarray,
    save_dir: str = "crops",
    export_as: ExportFormat = ExportFormat.MASKS,
    file_format: FileFormat = FileFormat.TIFF8,
    nested_save: bool = False,
    image_name: str = "input_image",
    objects_name: str = "input_objects"
) -> np.ndarray:
    """
    Saves cropped images or masks for each object identified in the labels.
    
    Args:
        image: Shape (D, H, W) - The intensity image.
        labels: Shape (D, H, W) - The label matrix (injected via @special_inputs).
        save_dir: Directory to save crops.
        export_as: Whether to save intensity 'image' crops or binary 'masks'.
        file_format: Output file format.
        nested_save: If True, creates subdirectories per image.
        image_name: Base name for the image file.
        objects_name: Base name for the objects.
        
    Returns:
        The original image (passthrough).
    """
    from skimage.measure import regionprops
    import cv2

    if not os.path.exists(save_dir):
        os.makedirs(save_dir, exist_ok=True)

    # OpenHCS handles D as the iteration axis. 
    # We iterate through slices to find objects.
    for d in range(image.shape[0]):
        slice_img = image[d]
        slice_labels = labels[d].astype(np.int32)
        
        props = regionprops(slice_labels)
        
        for prop in props:
            label_id = prop.label
            minr, minc, maxr, maxc = prop.bbox
            
            # Extract crop
            if export_as == ExportFormat.IMAGE:
                crop = slice_img[minr:maxr, minc:maxc]
            else:
                # Create a binary mask for the specific object
                crop = (slice_labels[minr:maxr, minc:maxc] == label_id).astype(np.uint8) * 255

            # Handle bit depth
            if file_format == FileFormat.TIFF16:
                crop_to_save = (crop * 65535).astype(np.uint16) if crop.dtype != np.uint16 else crop
            else:
                crop_to_save = (crop * 255).astype(np.uint8) if crop.dtype != np.uint8 else crop

            # Construct filename
            sub_path = os.path.join(save_dir, f"slice_{d}") if nested_save else save_dir
            if nested_save and not os.path.exists(sub_path):
                os.makedirs(sub_path, exist_ok=True)
                
            filename = f"{objects_name}_{label_id}_slice{d}.{file_format.value.replace('tiff8', 'tif').replace('tiff16', 'tif')}"
            full_path = os.path.join(sub_path, filename)
            
            # Save using OpenCV
            cv2.imwrite(full_path, crop_to_save)

    return image