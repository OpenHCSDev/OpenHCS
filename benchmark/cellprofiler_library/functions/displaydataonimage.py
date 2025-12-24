"""Converted from CellProfiler: DisplayDataOnImage"""

import numpy as np
from typing import Tuple, Optional
from dataclasses import dataclass
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_inputs


class DisplayMode(Enum):
    TEXT = "text"
    COLOR = "color"


class ObjectsOrImage(Enum):
    OBJECTS = "objects"
    IMAGE = "image"


class ColorMapScale(Enum):
    USE_MEASUREMENT_RANGE = "use_measurement_range"
    MANUAL = "manual"


class SavedImageContents(Enum):
    IMAGE = "image"
    AXES = "axes"
    FIGURE = "figure"


@numpy(contract=ProcessingContract.FLEXIBLE)
@special_inputs("labels", "measurements")
def display_data_on_image(
    image: np.ndarray,
    labels: Optional[np.ndarray] = None,
    measurements: Optional[np.ndarray] = None,
    objects_or_image: ObjectsOrImage = ObjectsOrImage.OBJECTS,
    display_mode: DisplayMode = DisplayMode.TEXT,
    wants_background_image: bool = True,
    text_color: Tuple[float, float, float] = (1.0, 0.0, 0.0),
    font_size: int = 10,
    decimals: int = 2,
    offset: int = 0,
    colormap: str = "viridis",
    color_map_scale_choice: ColorMapScale = ColorMapScale.USE_MEASUREMENT_RANGE,
    color_map_scale_min: float = 0.0,
    color_map_scale_max: float = 1.0,
    use_scientific_notation: bool = False,
    image_measurement_value: Optional[float] = None,
    center_x: Optional[np.ndarray] = None,
    center_y: Optional[np.ndarray] = None,
) -> np.ndarray:
    """
    Display measurement data on top of an image.
    
    This function overlays measurement values on an image, either as text
    annotations at object centers or as a color map applied to object regions.
    
    Args:
        image: Input image, shape (D, H, W) or (H, W)
        labels: Optional label image for objects, shape matching image
        measurements: Optional array of measurement values per object
        objects_or_image: Whether displaying object or image measurements
        display_mode: TEXT for numeric values, COLOR for colormap overlay
        wants_background_image: Whether to show background image or black
        text_color: RGB tuple for text color (0-1 range)
        font_size: Font size in points
        decimals: Number of decimal places to display
        offset: Pixel offset for text placement
        colormap: Name of matplotlib colormap
        color_map_scale_choice: Use measurement range or manual scale
        color_map_scale_min: Manual minimum for color scale
        color_map_scale_max: Manual maximum for color scale
        use_scientific_notation: Display values in scientific notation
        image_measurement_value: Single value for image-level measurement
        center_x: X coordinates of object centers
        center_y: Y coordinates of object centers
    
    Returns:
        RGB image with measurements displayed, shape (D, H, W, 3) or (H, W, 3)
    """
    from skimage.measure import regionprops
    from scipy.ndimage import map_coordinates
    import cv2
    
    # Handle dimensionality
    if image.ndim == 3:
        # Process each slice
        results = []
        for i in range(image.shape[0]):
            slice_img = image[i]
            slice_labels = labels[i] if labels is not None and labels.ndim == 3 else labels
            result = _display_data_on_slice(
                slice_img, slice_labels, measurements, objects_or_image,
                display_mode, wants_background_image, text_color, font_size,
                decimals, offset, colormap, color_map_scale_choice,
                color_map_scale_min, color_map_scale_max, use_scientific_notation,
                image_measurement_value, center_x, center_y
            )
            results.append(result)
        return np.stack(results, axis=0)
    else:
        return _display_data_on_slice(
            image, labels, measurements, objects_or_image,
            display_mode, wants_background_image, text_color, font_size,
            decimals, offset, colormap, color_map_scale_choice,
            color_map_scale_min, color_map_scale_max, use_scientific_notation,
            image_measurement_value, center_x, center_y
        )


def _display_data_on_slice(
    image: np.ndarray,
    labels: Optional[np.ndarray],
    measurements: Optional[np.ndarray],
    objects_or_image: ObjectsOrImage,
    display_mode: DisplayMode,
    wants_background_image: bool,
    text_color: Tuple[float, float, float],
    font_size: int,
    decimals: int,
    offset: int,
    colormap: str,
    color_map_scale_choice: ColorMapScale,
    color_map_scale_min: float,
    color_map_scale_max: float,
    use_scientific_notation: bool,
    image_measurement_value: Optional[float],
    center_x: Optional[np.ndarray],
    center_y: Optional[np.ndarray],
) -> np.ndarray:
    """Process a single 2D slice."""
    from skimage.measure import regionprops
    import cv2
    
    h, w = image.shape[:2]
    
    # Prepare background
    if wants_background_image:
        if image.ndim == 2:
            # Grayscale to RGB
            background = np.stack([image, image, image], axis=-1)
        else:
            background = image.copy()
    else:
        background = np.zeros((h, w, 3), dtype=np.float32)
    
    # Normalize to 0-1 range if needed
    if background.max() > 1.0:
        background = background / 255.0
    background = background.astype(np.float32)
    
    if objects_or_image == ObjectsOrImage.IMAGE:
        # Display single image measurement at center
        if image_measurement_value is not None:
            x = w // 2
            y = h // 2
            x_offset = np.random.uniform(-1.0, 1.0)
            y_offset = np.sqrt(1 - x_offset ** 2)
            x = int(x + offset * x_offset)
            y = int(y + offset * y_offset)
            
            if use_scientific_notation:
                text = f"{image_measurement_value:.{decimals}e}"
            else:
                text = f"{image_measurement_value:.{decimals}f}"
            
            # Convert to uint8 for cv2
            output = (background * 255).astype(np.uint8)
            color_bgr = (int(text_color[2] * 255), int(text_color[1] * 255), int(text_color[0] * 255))
            font_scale = font_size / 20.0
            cv2.putText(output, text, (x, y), cv2.FONT_HERSHEY_SIMPLEX, 
                       font_scale, color_bgr, 1, cv2.LINE_AA)
            return output.astype(np.float32) / 255.0
    
    elif objects_or_image == ObjectsOrImage.OBJECTS and labels is not None:
        if display_mode == DisplayMode.COLOR and measurements is not None:
            # Color map mode
            from matplotlib import cm
            
            # Get colormap
            cmap = cm.get_cmap(colormap)
            
            # Determine scale
            valid_measurements = measurements[~np.isnan(measurements)] if len(measurements) > 0 else np.array([0, 1])
            if color_map_scale_choice == ColorMapScale.MANUAL:
                vmin, vmax = color_map_scale_min, color_map_scale_max
            else:
                vmin = valid_measurements.min() if len(valid_measurements) > 0 else 0
                vmax = valid_measurements.max() if len(valid_measurements) > 0 else 1
            
            if vmax == vmin:
                vmax = vmin + 1
            
            # Normalize measurements
            normalized = (measurements - vmin) / (vmax - vmin)
            normalized = np.clip(normalized, 0, 1)
            
            # Create colored output
            output = background.copy()
            if output.ndim == 2:
                output = np.stack([output, output, output], axis=-1)
            
            # Apply colors to each labeled region
            for i, val in enumerate(normalized):
                if not np.isnan(val):
                    color = cmap(val)[:3]
                    mask = labels == (i + 1)
                    for c in range(3):
                        output[:, :, c] = np.where(mask, 
                            output[:, :, c] * 0.5 + color[c] * 0.5,
                            output[:, :, c])
            
            return output
        
        else:
            # Text mode
            # Get object centers
            if center_x is None or center_y is None:
                props = regionprops(labels.astype(np.int32))
                centers = [(p.centroid[1], p.centroid[0]) for p in props]
            else:
                centers = list(zip(center_x, center_y))
            
            # Convert to uint8 for cv2
            output = (background * 255).astype(np.uint8)
            color_bgr = (int(text_color[2] * 255), int(text_color[1] * 255), int(text_color[0] * 255))
            font_scale = font_size / 20.0
            
            if measurements is not None:
                for idx, (cx, cy) in enumerate(centers):
                    if idx < len(measurements):
                        val = measurements[idx]
                        if np.isnan(val):
                            continue
                        
                        # Apply offset
                        x_off = np.random.uniform(-1.0, 1.0)
                        y_off = np.sqrt(1 - x_off ** 2)
                        x = int(cx + offset * x_off)
                        y = int(cy + offset * y_off)
                        
                        if use_scientific_notation:
                            text = f"{val:.{decimals}e}"
                        else:
                            text = f"{val:.{decimals}f}"
                        
                        cv2.putText(output, text, (x, y), cv2.FONT_HERSHEY_SIMPLEX,
                                   font_scale, color_bgr, 1, cv2.LINE_AA)
            
            return output.astype(np.float32) / 255.0
    
    return background