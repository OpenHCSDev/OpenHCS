"""
Enums for streaming backends and visualizers.

This module provides type-safe enums for data types and shape types
used in streaming backends and visualizers.
"""

from enum import Enum


class StreamingDataType(Enum):
    """Types of data that can be streamed to viewers."""
    IMAGE = 'image'
    SHAPES = 'shapes'  # For Napari shapes layer
    POINTS = 'points'  # For Napari points layer (e.g., skeleton tracings)
    ROIS = 'rois'      # For Fiji


class NapariShapeType(Enum):
    """Napari shape types for ROI visualization."""
    POLYGON = 'polygon'
    ELLIPSE = 'ellipse'
    POINT = 'point'
    LINE = 'line'
    PATH = 'path'
    RECTANGLE = 'rectangle'

