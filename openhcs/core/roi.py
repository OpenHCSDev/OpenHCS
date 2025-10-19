"""
Generic ROI (Region of Interest) system for OpenHCS.

This module provides backend-agnostic ROI extraction and representation.
ROIs are extracted from labeled segmentation masks and can be materialized
to various backends (OMERO, disk, Napari, Fiji).

Doctrinal Clauses:
- Clause 66 — Immutability After Construction
- Clause 88 — No Inferred Capabilities
"""

import logging
import numpy as np
from dataclasses import dataclass, field
from typing import List, Dict, Any, Optional, Tuple
from pathlib import Path
from enum import Enum

logger = logging.getLogger(__name__)


class ShapeType(Enum):
    """ROI shape types."""
    POLYGON = "polygon"
    MASK = "mask"
    POINT = "point"
    ELLIPSE = "ellipse"


@dataclass(frozen=True)
class PolygonShape:
    """Polygon ROI shape defined by vertex coordinates.

    Attributes:
        coordinates: Nx2 array of (y, x) coordinates
        shape_type: Always ShapeType.POLYGON
    """
    coordinates: np.ndarray  # Nx2 array of (y, x) coordinates
    shape_type: ShapeType = field(default=ShapeType.POLYGON, init=False)

    def __post_init__(self):
        """Validate polygon coordinates."""
        if self.coordinates.ndim != 2 or self.coordinates.shape[1] != 2:
            raise ValueError(f"Polygon coordinates must be Nx2 array, got shape {self.coordinates.shape}")
        if len(self.coordinates) < 3:
            raise ValueError(f"Polygon must have at least 3 vertices, got {len(self.coordinates)}")


@dataclass(frozen=True)
class MaskShape:
    """Binary mask ROI shape.

    Attributes:
        mask: 2D boolean array
        bbox: Bounding box (min_y, min_x, max_y, max_x)
        shape_type: Always ShapeType.MASK
    """
    mask: np.ndarray  # 2D boolean array
    bbox: Tuple[int, int, int, int]  # (min_y, min_x, max_y, max_x)
    shape_type: ShapeType = field(default=ShapeType.MASK, init=False)

    def __post_init__(self):
        """Validate mask."""
        if self.mask.ndim != 2:
            raise ValueError(f"Mask must be 2D array, got shape {self.mask.shape}")
        if self.mask.dtype != bool:
            raise ValueError(f"Mask must be boolean array, got dtype {self.mask.dtype}")


@dataclass(frozen=True)
class PointShape:
    """Point ROI shape.

    Attributes:
        y: Y coordinate
        x: X coordinate
        shape_type: Always ShapeType.POINT
    """
    y: float
    x: float
    shape_type: ShapeType = field(default=ShapeType.POINT, init=False)


@dataclass(frozen=True)
class EllipseShape:
    """Ellipse ROI shape.

    Attributes:
        center_y: Y coordinate of center
        center_x: X coordinate of center
        radius_y: Radius along Y axis
        radius_x: Radius along X axis
        shape_type: Always ShapeType.ELLIPSE
    """
    center_y: float
    center_x: float
    radius_y: float
    radius_x: float
    shape_type: ShapeType = field(default=ShapeType.ELLIPSE, init=False)


@dataclass(frozen=True)
class ROI:
    """Region of Interest with metadata.

    Attributes:
        shapes: List of shape objects (PolygonShape, MaskShape, etc.)
        metadata: Dictionary of ROI metadata (label, area, perimeter, etc.)
    """
    shapes: List[Any]  # List of shape objects
    metadata: Dict[str, Any] = field(default_factory=dict)

    def __post_init__(self):
        """Validate ROI."""
        if not self.shapes:
            raise ValueError("ROI must have at least one shape")

        # Validate all shapes have shape_type attribute
        for shape in self.shapes:
            if not hasattr(shape, 'shape_type'):
                raise ValueError(f"Shape {shape} must have shape_type attribute")


def extract_rois_from_labeled_mask(
    labeled_mask: np.ndarray,
    min_area: int = 10,
    extract_contours: bool = True
) -> List[ROI]:
    """Extract ROIs from a labeled segmentation mask.

    Args:
        labeled_mask: 2D integer array where each unique value (except 0) represents a cell/object
        min_area: Minimum area (in pixels) for an ROI to be included
        extract_contours: If True, extract polygon contours; if False, use binary masks

    Returns:
        List of ROI objects with shapes and metadata
    """
    from skimage import measure
    from skimage.measure import regionprops

    if labeled_mask.ndim != 2:
        raise ValueError(f"Labeled mask must be 2D, got shape {labeled_mask.shape}")

    # Convert to integer type if needed (regionprops requires integer labels)
    if not np.issubdtype(labeled_mask.dtype, np.integer):
        labeled_mask = labeled_mask.astype(np.int32)

    # Get region properties
    regions = regionprops(labeled_mask)

    rois = []
    for region in regions:
        # Filter by area
        if region.area < min_area:
            continue

        # Extract metadata
        metadata = {
            'label': int(region.label),
            'area': float(region.area),
            'perimeter': float(region.perimeter),
            'centroid': tuple(float(c) for c in region.centroid),  # (y, x)
            'bbox': tuple(int(b) for b in region.bbox),  # (min_y, min_x, max_y, max_x)
        }

        # Extract shapes
        shapes = []

        if extract_contours:
            # Find contours for this region
            # Create binary mask for this label
            binary_mask = (labeled_mask == region.label)

            # Find contours
            contours = measure.find_contours(binary_mask.astype(float), level=0.5)

            # Convert contours to polygon shapes
            for contour in contours:
                if len(contour) >= 3:  # Valid polygon
                    # Contour is already in (y, x) format
                    shapes.append(PolygonShape(coordinates=contour))
        else:
            # Use binary mask
            binary_mask = (labeled_mask == region.label)
            shapes.append(MaskShape(mask=binary_mask, bbox=region.bbox))

        # Create ROI if we have shapes
        if shapes:
            rois.append(ROI(shapes=shapes, metadata=metadata))

    logger.info(f"Extracted {len(rois)} ROIs from labeled mask")
    return rois


def materialize_rois(
    rois: List[ROI],
    output_path: str,
    filemanager,
    backend: str
) -> str:
    """Materialize ROIs to backend-specific format.

    This is the generic materialization function that dispatches to
    backend-specific implementations.

    Args:
        rois: List of ROI objects to materialize
        output_path: Output path (backend-specific format)
        filemanager: FileManager instance (used to get backend and extract images_dir)
        backend: Backend name (disk, omero_local, napari_stream, fiji_stream)

    Returns:
        Path where ROIs were saved
    """
    from openhcs.constants.constants import Backend

    # Get backend instance from filemanager
    backend_obj = filemanager.get_backend(backend)

    # Extract images_dir from filemanager's materialization context
    images_dir = None
    if hasattr(filemanager, '_materialization_context'):
        images_dir = filemanager._materialization_context.get('images_dir')

    # Dispatch to backend-specific method with explicit images_dir parameter
    if hasattr(backend_obj, '_save_rois'):
        return backend_obj._save_rois(rois, Path(output_path), images_dir=images_dir)
    else:
        raise NotImplementedError(f"Backend {backend} does not support ROI saving")


def load_rois_from_json(json_path: Path) -> List[ROI]:
    """Load ROIs from JSON file.

    Deserializes ROI JSON files created by the disk backend back into ROI objects.
    This allows ROIs to be loaded and re-streamed to viewers.

    Args:
        json_path: Path to ROI JSON file

    Returns:
        List of ROI objects

    Raises:
        FileNotFoundError: If JSON file doesn't exist
        ValueError: If JSON format is invalid
    """
    import json

    if not json_path.exists():
        raise FileNotFoundError(f"ROI JSON file not found: {json_path}")

    with open(json_path, 'r') as f:
        rois_data = json.load(f)

    if not isinstance(rois_data, list):
        raise ValueError(f"Invalid ROI JSON format: expected list, got {type(rois_data)}")

    rois = []
    for roi_dict in rois_data:
        # Extract metadata
        metadata = roi_dict.get('metadata', {})

        # Deserialize shapes
        shapes = []
        for shape_dict in roi_dict.get('shapes', []):
            shape_type = shape_dict.get('type')

            if shape_type == 'polygon':
                coordinates = np.array(shape_dict['coordinates'])
                shapes.append(PolygonShape(coordinates=coordinates))

            elif shape_type == 'mask':
                mask = np.array(shape_dict['mask'], dtype=bool)
                bbox = tuple(shape_dict['bbox'])
                shapes.append(MaskShape(mask=mask, bbox=bbox))

            elif shape_type == 'point':
                shapes.append(PointShape(y=shape_dict['y'], x=shape_dict['x']))

            elif shape_type == 'ellipse':
                shapes.append(EllipseShape(
                    center_y=shape_dict['center_y'],
                    center_x=shape_dict['center_x'],
                    radius_y=shape_dict['radius_y'],
                    radius_x=shape_dict['radius_x']
                ))
            else:
                logger.warning(f"Unknown shape type: {shape_type}, skipping")

        # Create ROI if we have shapes
        if shapes:
            rois.append(ROI(shapes=shapes, metadata=metadata))

    logger.info(f"Loaded {len(rois)} ROIs from {json_path}")
    return rois


def load_rois_from_zip(zip_path: Path) -> List[ROI]:
    """Load ROIs from .roi.zip archive (ImageJ standard format).

    Deserializes .roi.zip files created by the disk backend back into ROI objects.
    This allows ROIs to be loaded and re-streamed to viewers.

    Args:
        zip_path: Path to .roi.zip archive

    Returns:
        List of ROI objects

    Raises:
        FileNotFoundError: If zip file doesn't exist
        ValueError: If zip format is invalid or contains no valid ROIs
        ImportError: If roifile library is not available
    """
    import zipfile

    if not zip_path.exists():
        raise FileNotFoundError(f"ROI zip file not found: {zip_path}")

    try:
        from roifile import ImagejRoi
    except ImportError:
        raise ImportError("roifile library required for loading .roi.zip files. Install with: pip install roifile")

    rois = []

    with zipfile.ZipFile(zip_path, 'r') as zf:
        for filename in zf.namelist():
            if filename.endswith('.roi'):
                try:
                    roi_bytes = zf.read(filename)
                    ij_roi = ImagejRoi.frombytes(roi_bytes)

                    # Convert ImageJ ROI to OpenHCS ROI
                    # ImageJ uses (x, y), OpenHCS uses (y, x)
                    coords = ij_roi.coordinates()
                    if coords is not None and len(coords) > 0:
                        coords_yx = coords[:, [1, 0]]  # Swap to (y, x)

                        shape = PolygonShape(coordinates=coords_yx)
                        roi = ROI(
                            shapes=[shape],
                            metadata={'label': ij_roi.name or filename.replace('.roi', '')}
                        )
                        rois.append(roi)
                except Exception as e:
                    logger.warning(f"Failed to load ROI from {filename}: {e}")
                    continue

    if not rois:
        raise ValueError(f"No valid ROIs found in {zip_path}")

    logger.info(f"Loaded {len(rois)} ROIs from {zip_path}")
    return rois

