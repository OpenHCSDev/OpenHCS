"""
ROI conversion utilities for streaming backends and viewer servers.

Provides single source of truth for converting OpenHCS ROI objects to:
- Napari shapes format (for NapariStreamingBackend and NapariViewerServer)
- ImageJ ROI format (for FijiStreamingBackend and FijiViewerServer)
"""

import logging
from typing import List, Dict, Any, Tuple
import numpy as np

logger = logging.getLogger(__name__)


class NapariROIConverter:
    """Convert OpenHCS ROIs to Napari shapes format."""

    # Registry of shape type handlers for adding dimensions
    _SHAPE_DIMENSION_HANDLERS = {
        'polygon': lambda shape_dict, prepend_dims: np.hstack([
            np.tile(prepend_dims, (len(shape_dict['coordinates']), 1)),
            np.array(shape_dict['coordinates'])
        ]),
        'ellipse': lambda shape_dict, prepend_dims: np.hstack([
            np.tile(prepend_dims, (4, 1)),
            np.array([
                [shape_dict['center'][0] - shape_dict['radii'][0], shape_dict['center'][1] - shape_dict['radii'][1]],
                [shape_dict['center'][0] - shape_dict['radii'][0], shape_dict['center'][1] + shape_dict['radii'][1]],
                [shape_dict['center'][0] + shape_dict['radii'][0], shape_dict['center'][1] + shape_dict['radii'][1]],
                [shape_dict['center'][0] + shape_dict['radii'][0], shape_dict['center'][1] - shape_dict['radii'][1]],
            ])
        ]),
        'point': lambda shape_dict, prepend_dims: np.concatenate([
            prepend_dims,
            shape_dict['coordinates']
        ]).reshape(1, -1)
    }

    @staticmethod
    def add_dimensions_to_shape(shape_dict: Dict[str, Any], prepend_dims: List[float]) -> np.ndarray:
        """
        Add dimensions to a 2D shape to make it nD.

        Args:
            shape_dict: Shape dict with 'type', 'coordinates', etc.
            prepend_dims: List of dimension values to prepend (e.g., [z_value, t_value])

        Returns:
            np.ndarray: Shape coordinates with prepended dimensions
        """
        from openhcs.constants.streaming import NapariShapeType

        shape_type = shape_dict['type']
        # Convert string to enum if needed
        if isinstance(shape_type, str):
            shape_type_enum = NapariShapeType(shape_type)
        else:
            shape_type_enum = shape_type

        # Use registry to get handler
        handler = NapariROIConverter._SHAPE_DIMENSION_HANDLERS.get(shape_type_enum.value)
        if handler is None:
            raise ValueError(f"Unsupported shape type: {shape_type}")

        return handler(shape_dict, np.array(prepend_dims))

    @staticmethod
    def rois_to_shapes(rois: List) -> List[Dict[str, Any]]:
        """Convert ROI objects to Napari shapes data.
        
        Args:
            rois: List of ROI objects
            
        Returns:
            List of shape dicts with 'type', 'coordinates', 'metadata'
        """
        from openhcs.core.roi import PolygonShape, EllipseShape, PointShape
        
        shapes_data = []
        for roi in rois:
            for shape in roi.shapes:
                if isinstance(shape, PolygonShape):
                    # Napari expects (y, x) coordinates - same as OpenHCS
                    shapes_data.append({
                        'type': 'polygon',
                        'coordinates': shape.coordinates.tolist(),
                        'metadata': roi.metadata
                    })
                elif isinstance(shape, EllipseShape):
                    # Napari ellipse format: center (y, x) and radii (ry, rx)
                    shapes_data.append({
                        'type': 'ellipse',
                        'center': [shape.center_y, shape.center_x],
                        'radii': [shape.radius_y, shape.radius_x],
                        'metadata': roi.metadata
                    })
                elif isinstance(shape, PointShape):
                    # Napari point format: (y, x)
                    shapes_data.append({
                        'type': 'point',
                        'coordinates': [shape.y, shape.x],
                        'metadata': roi.metadata
                    })
        
        return shapes_data
    
    @staticmethod
    def shapes_to_napari_format(shapes_data: List[Dict]) -> Tuple[List[np.ndarray], List[str], Dict]:
        """Convert shape dicts to Napari layer format.

        Args:
            shapes_data: List of shape dicts from rois_to_shapes()

        Returns:
            Tuple of (napari_shapes, shape_types, properties)
        """
        napari_shapes = []
        shape_types = []
        properties = {'label': [], 'area': [], 'centroid_y': [], 'centroid_x': []}

        for shape_dict in shapes_data:
            shape_type = shape_dict.get('type')
            metadata = shape_dict.get('metadata', {})

            if shape_type == 'polygon':
                # Polygon coordinates are already in (y, x) format
                coords = np.array(shape_dict['coordinates'])
                napari_shapes.append(coords)
                shape_types.append('polygon')

                # Extract properties from metadata (split centroid into y and x for Napari)
                centroid = metadata.get('centroid', (0, 0))
                properties['label'].append(metadata.get('label', ''))
                properties['area'].append(metadata.get('area', 0))
                properties['centroid_y'].append(centroid[0])
                properties['centroid_x'].append(centroid[1])

            elif shape_type == 'ellipse':
                # Napari ellipse: 4 corner points of bounding box
                center = np.array(shape_dict['center'])
                radii = np.array(shape_dict['radii'])

                # Create bounding box corners
                corners = np.array([
                    center - radii,
                    center + radii
                ])
                napari_shapes.append(corners)
                shape_types.append('ellipse')

                centroid = metadata.get('centroid', (0, 0))
                properties['label'].append(metadata.get('label', ''))
                properties['area'].append(metadata.get('area', 0))
                properties['centroid_y'].append(centroid[0])
                properties['centroid_x'].append(centroid[1])

            elif shape_type == 'point':
                # Point coordinates
                coords = np.array([shape_dict['coordinates']])
                napari_shapes.append(coords)
                shape_types.append('point')

                point_coords = shape_dict['coordinates']
                properties['label'].append(metadata.get('label', ''))
                properties['area'].append(0)
                properties['centroid_y'].append(point_coords[0])
                properties['centroid_x'].append(point_coords[1])

        return napari_shapes, shape_types, properties


class FijiROIConverter:
    """Convert OpenHCS ROIs to ImageJ ROI format."""
    
    @staticmethod
    def rois_to_imagej_bytes(rois: List, roi_prefix: str = "") -> List[bytes]:
        """Convert ROI objects to ImageJ ROI bytes.
        
        Args:
            rois: List of ROI objects
            roi_prefix: Prefix for ROI names (e.g., "A01_s001_w1_rois_step7")
            
        Returns:
            List of ROI bytes (not base64 encoded)
        """
        from openhcs.core.roi import PolygonShape, EllipseShape, PointShape
        
        try:
            from roifile import ImagejRoi
        except ImportError:
            raise ImportError("roifile library required for ImageJ ROI conversion. Install with: pip install roifile")
        
        roi_bytes_list = []
        
        for roi in rois:
            for shape in roi.shapes:
                if isinstance(shape, PolygonShape):
                    # ImageJ expects (x, y) coordinates, OpenHCS has (y, x)
                    coords_xy = shape.coordinates[:, [1, 0]]  # Swap columns
                    ij_roi = ImagejRoi.frompoints(coords_xy)
                    
                    # Set ROI name with descriptive prefix
                    if 'label' in roi.metadata:
                        ij_roi.name = f"{roi_prefix}_ROI_{roi.metadata['label']}"
                    else:
                        ij_roi.name = f"{roi_prefix}_ROI"
                    
                    roi_bytes_list.append(ij_roi.tobytes())
                    
                elif isinstance(shape, EllipseShape):
                    # ImageJ ellipse ROI
                    # Convert center (y, x) to (x, y) and radii (ry, rx) to (rx, ry)
                    center_x = shape.center_x
                    center_y = shape.center_y
                    radius_x = shape.radius_x
                    radius_y = shape.radius_y
                    
                    # Create ellipse from bounding box
                    left = center_x - radius_x
                    top = center_y - radius_y
                    width = 2 * radius_x
                    height = 2 * radius_y
                    
                    ij_roi = ImagejRoi.frompoints(
                        np.array([[left, top], [left + width, top + height]])
                    )
                    ij_roi.roitype = ImagejRoi.OVAL
                    
                    if 'label' in roi.metadata:
                        ij_roi.name = f"{roi_prefix}_ROI_{roi.metadata['label']}"
                    else:
                        ij_roi.name = f"{roi_prefix}_ROI"
                    
                    roi_bytes_list.append(ij_roi.tobytes())
                    
                elif isinstance(shape, PointShape):
                    # ImageJ point ROI (x, y)
                    ij_roi = ImagejRoi.frompoints(np.array([[shape.x, shape.y]]))
                    
                    if 'label' in roi.metadata:
                        ij_roi.name = f"{roi_prefix}_ROI_{roi.metadata['label']}"
                    else:
                        ij_roi.name = f"{roi_prefix}_ROI"
                    
                    roi_bytes_list.append(ij_roi.tobytes())
        
        return roi_bytes_list
    
    @staticmethod
    def encode_rois_for_transmission(roi_bytes_list: List[bytes]) -> List[str]:
        """Base64 encode ROI bytes for JSON transmission.
        
        Args:
            roi_bytes_list: List of ROI bytes from rois_to_imagej_bytes()
            
        Returns:
            List of base64-encoded strings
        """
        import base64
        return [base64.b64encode(roi_bytes).decode('utf-8') for roi_bytes in roi_bytes_list]
    
    @staticmethod
    def decode_rois_from_transmission(encoded_rois: List[str]) -> List[bytes]:
        """Decode base64-encoded ROI bytes.
        
        Args:
            encoded_rois: List of base64-encoded strings
            
        Returns:
            List of ROI bytes
        """
        import base64
        return [base64.b64decode(roi_encoded) for roi_encoded in encoded_rois]
    
    @staticmethod
    def bytes_to_java_roi(roi_bytes: bytes, scyjava_module) -> Any:
        """Convert ROI bytes to Java ROI object via temporary file.
        
        Args:
            roi_bytes: ImageJ ROI bytes
            scyjava_module: scyjava module (for jimport)
            
        Returns:
            Java Roi object
        """
        import tempfile
        import os
        
        # Import ImageJ classes
        RoiDecoder = scyjava_module.jimport('ij.io.RoiDecoder')
        
        # Create temporary file with ROI bytes
        with tempfile.NamedTemporaryFile(suffix='.roi', delete=False) as tmp:
            tmp.write(roi_bytes)
            tmp_path = tmp.name
        
        try:
            # Load ROI using ImageJ's RoiDecoder
            roi_decoder = RoiDecoder(tmp_path)
            java_roi = roi_decoder.getRoi()
            return java_roi
        finally:
            # Clean up temp file
            os.unlink(tmp_path)

