"""
Converted from CellProfiler: Watershed
Original: watershed
"""

import numpy as np
from typing import Tuple, Literal, Optional
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_inputs, special_outputs

@numpy(contract=ProcessingContract.FLEXIBLE)
@special_inputs("mask", "intensity_image", "markers_image")
@special_outputs("labels")
def watershed(
    image: np.ndarray,
    mask: Optional[np.ndarray] = None,
    intensity_image: Optional[np.ndarray] = None,
    markers_image: Optional[np.ndarray] = None,
    watershed_method: Literal["distance", "intensity", "markers"] = "distance",
    declump_method: Literal["shape", "intensity"] = "shape",
    seed_method: Literal["local", "regional"] = "local",
    max_seeds: int = -1,
    downsample: int = 1,
    min_distance: int = 1,
    min_intensity: float = 0.0,
    footprint: int = 8,
    connectivity: int = 1,
    compactness: float = 0.0,
    exclude_border: bool = False,
    watershed_line: bool = False,
    gaussian_sigma: float = 0.0,
    structuring_element: Literal[
        "ball", "cube", "diamond", "disk", "octahedron", "square", "star"
    ] = "disk",
    structuring_element_size: int = 1,
) -> Tuple[np.ndarray, np.ndarray]:
    """
    Perform watershed segmentation on an image.
    
    Args:
        image: The primary input image (D, H, W).
        mask: Optional binary mask.
        intensity_image: Optional intensity image for 'intensity' method.
        markers_image: Optional markers for 'markers' method.
    """
    from skimage.segmentation import watershed as sk_watershed
    from skimage.feature import peak_local_max
    from skimage.filters import gaussian
    from skimage.measure import label
    from scipy import ndimage as ndi

    # OpenHCS handles D, H, W. We process slice by slice if D > 1
    def process_slice(img, msk, int_img, mrk_img):
        if gaussian_sigma > 0:
            img = gaussian(img, sigma=gaussian_sigma)

        if watershed_method == "distance":
            # Distance transform watershed
            distance = ndi.distance_transform_edt(img > 0)
            if downsample > 1:
                distance = distance[::downsample, ::downsample]
            
            coords = peak_local_max(
                distance, 
                min_distance=min_distance, 
                threshold_abs=min_intensity,
                num_peaks=max_seeds if max_seeds > 0 else None,
                labels=msk
            )
            local_markers = np.zeros(distance.shape, dtype=bool)
            local_markers[tuple(coords.T)] = True
            markers = label(local_markers)
            algo_input = -distance
        
        elif watershed_method == "markers":
            markers = mrk_img
            algo_input = img
            
        else: # intensity
            target = int_img if int_img is not None else img
            if seed_method == "local":
                coords = peak_local_max(
                    target, 
                    min_distance=min_distance,
                    num_peaks=max_seeds if max_seeds > 0 else None,
                    labels=msk
                )
                local_markers = np.zeros(target.shape, dtype=bool)
                local_markers[tuple(coords.T)] = True
                markers = label(local_markers)
            else:
                markers = label(target > min_intensity)
            algo_input = target

        labels = sk_watershed(
            algo_input,
            markers,
            mask=msk,
            connectivity=connectivity,
            compactness=compactness,
            watershed_line=watershed_line
        )
        
        if exclude_border:
            # Simple border clearing
            border_mask = np.ones(labels.shape, dtype=bool)
            border_mask[1:-1, 1:-1] = False
            border_labels = np.unique(labels[border_mask])
            for bl in border_labels:
                if bl != 0:
                    labels[labels == bl] = 0
                    
        return labels

    # Handle dimensional iteration
    depth = image.shape[0]
    out_labels = np.zeros_like(image, dtype=np.int32)
    
    for d in range(depth):
        s_img = image[d]
        s_msk = mask[d] if mask is not None else None
        s_int = intensity_image[d] if intensity_image is not None else None
        s_mrk = markers_image[d] if markers_image is not None else None
        
        out_labels[d] = process_slice(s_img, s_msk, s_int, s_mrk)

    return image, out_labels