"""
Converted from CellProfiler: OverlayObjects
Original: overlayobjects
"""

import numpy as np
from typing import Tuple, Optional
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_inputs

@numpy(contract=ProcessingContract.FLEXIBLE)
@special_inputs("labels")
def overlay_objects(
    image: np.ndarray,
    labels: np.ndarray,
    opacity: float = 0.3,
    max_label: Optional[int] = None,
    seed: Optional[int] = None,
    colormap: str = "jet"
) -> np.ndarray:
    """
    Overlay object labels onto a grayscale or RGB image using a colormap.
    
    Args:
        image: The intensity image. Shape (1, H, W) or (3, H, W).
        labels: The label image (from special_inputs). Shape (1, H, W).
        opacity: Opacity of the overlay (0 to 1).
        max_label: Maximum label value for colormap scaling.
        seed: Random seed for color shuffling.
        colormap: Matplotlib colormap name.
        
    Returns:
        RGB image with overlay. Shape (3, H, W).
    """
    from skimage.color import label2rgb
    
    # OpenHCS inputs are (D, H, W). 
    # For PURE_2D logic within FLEXIBLE, we handle the first slice.
    img_2d = image[0] if image.shape[0] == 1 else np.moveaxis(image, 0, -1)
    lbl_2d = labels[0]
    
    # label2rgb expects (H, W) or (H, W, 3)
    # It returns (H, W, 3)
    overlay = label2rgb(
        lbl_2d, 
        image=img_2d if image.shape[0] == 1 else None, # Use image as background if grayscale
        alpha=opacity, 
        bg_label=0, 
        kind='overlay'
    )
    
    # If the original image was RGB, we manually blend to respect the 'image' input
    if image.shape[0] == 3:
        # Convert image to HWC for blending
        img_hwc = np.moveaxis(image, 0, -1)
        # Simple alpha blend where labels exist
        mask = (lbl_2d > 0)[..., np.newaxis]
        rgb_labels = label2rgb(lbl_2d, colors=None, alpha=1.0, bg_label=0)
        combined = np.where(mask, (1 - opacity) * img_hwc + opacity * rgb_labels, img_hwc)
        result = np.moveaxis(combined, -1, 0)
    else:
        # Convert HWC back to CHW (3, H, W)
        result = np.moveaxis(overlay, -1, 0)
        
    return result.astype(np.float32)