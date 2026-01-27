"""
Typed materialization options - single source of truth for configuration.

This module defines all option dataclasses used by materialization handlers.
Each handler has a corresponding options type that provides:
- Type safety (compile-time + runtime)
- IDE autocomplete
- Validation at construction time
- Single source of truth for option schemas
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Protocol,
    Tuple,
    Union,
)
from enum import Enum


# ===== Base Protocol =====

class BaseOptions(Protocol):
    """Base protocol for all materialization options.

    All option types must be compatible with this protocol.
    """
    pass


# ===== Tabular Output Options =====

@dataclass
class TabularOptions:
    """Options for handlers that produce tabular output (CSV/JSON).

    Attributes:
        fields: List of field names to extract from data items. If None (default), extracts all fields.
            Only specify this when you need to control column ordering or select a subset.
        summary_fields: Fields to include in JSON summary. If None (default), uses all fields.
        include_metadata: Whether to include metadata in output.
        output_format: Output format - "csv", "json", or "dual" for both (default: "csv")
    """
    fields: Optional[List[str]] = None
    summary_fields: Optional[List[str]] = None
    include_metadata: bool = True
    output_format: str = "csv"  # "csv", "json", or "dual"


# ===== Array Expansion Options =====

@dataclass
class ArrayExpansionOptions(TabularOptions):
    """Options for handlers that expand array fields into multiple rows.

    This extends TabularOptions with array expansion capabilities for handling
    cases like cell_positions: [(x,y), (x,y), ...] where each array element
    becomes a separate row in the output.

    Attributes:
        row_field: Name of the array field to expand into rows (e.g., "cell_positions").
        row_columns: Dict mapping array indices to column names.
            Example: {"0": "x_position", "1": "y_position"}
            For simple tuple/list indexing, maps "0", "1", etc. to output column names.
        row_unpacker: Optional custom function for complex unpacking.
            If provided, this takes precedence over row_field + row_columns.
            Signature: (result_item: Any) -> List[Dict[str, Any]]
            Example: lambda r: [{"x": p[0], "y": p[1]} for p in r.cell_positions]
        aggregations: Dict mapping field names to aggregation specifications.
            Can be string (built-in) or callable (custom).
            Built-in options: "sum", "mean", "median", "max", "min", "count", "std", "var"
            Example: {"cell_count": "sum", "cell_area": "mean"}
            Custom example: {"custom": lambda vals: complex_calc(vals)}
    """
    row_field: Optional[str] = None
    row_columns: Dict[str, str] = field(default_factory=dict)
    row_unpacker: Optional[Callable[[Any], List[Dict[str, Any]]]] = None
    aggregations: Dict[str, Union[str, Callable[[List[Any]], Any]]] = field(default_factory=dict)


# ===== File Output Options =====

@dataclass
class FileOutputOptions:
    """Options for file output configuration.

    Attributes:
        filename_suffix: Suffix to append to output filename (e.g., ".csv", ".json").
            Default: "" (empty string - some subclasses use their own suffixes)
        strip_roi_suffix: Whether to strip ".roi" suffix from input path before adding suffix.
        strip_pkl: Whether to strip ".pkl" suffix from input path before adding suffix.
    """
    filename_suffix: str = ""
    strip_roi_suffix: bool = False
    strip_pkl: bool = True


# ===== ROI Processing Options =====

@dataclass
class ROIOptions(FileOutputOptions):
    """Options for ROI extraction handlers.

    Attributes:
        min_area: Minimum area threshold for ROI extraction (in pixels).
        extract_contours: Whether to extract polygon contours for ROIs.
        roi_suffix: Suffix for ROI output file (default: "_rois.roi.zip").
        summary_suffix: Suffix for summary text file (default: "_segmentation_summary.txt").
    """
    min_area: int = 10
    extract_contours: bool = True
    roi_suffix: str = "_rois.roi.zip"
    summary_suffix: str = "_segmentation_summary.txt"


# ===== Region Props Options =====

@dataclass
class RegionPropsOptions(FileOutputOptions):
    """Options for region properties computation from labeled masks.

    Attributes:
        properties: List of skimage regionprops to compute.
            Default: ["label", "area", "perimeter", "centroid", "bbox"]
        intensity_properties: List of intensity-based properties to compute.
            Default: ["mean_intensity"]
        require_intensity: Whether intensity input is required.
        min_area: Minimum area threshold for filtering regions (in pixels).
        extract_contours: Whether to extract polygon contours for ROIs.
        roi_suffix: Suffix for ROI output file.
        details_suffix: Suffix for CSV details file.
        json_suffix: Suffix for JSON summary file.
    """
    properties: Optional[List[str]] = None
    intensity_properties: Optional[List[str]] = None
    require_intensity: bool = False
    min_area: int = 10
    extract_contours: bool = True
    roi_suffix: str = "_rois.roi.zip"
    details_suffix: str = "_details.csv"
    json_suffix: str = ".json"


# ===== TIFF Stack Options =====

@dataclass
class TiffStackOptions(FileOutputOptions):
    """Options for TIFF stack output from image arrays.

    Attributes:
        normalize_uint8: Whether to normalize images to uint8 range [0, 255].
        summary_suffix: Suffix for summary text file.
        empty_summary: Content to write to summary file when no images generated.
    """
    normalize_uint8: bool = False
    summary_suffix: str = "_summary.txt"
    empty_summary: str = "No images generated (empty data)\n"


# ===== Built-in Aggregation Functions =====

class BuiltinAggregations:
    """Built-in aggregation functions for summary statistics.

    These are string-based aggregations that can be used in ArrayExpansionOptions.aggregations.
    """

    _FUNCS: Dict[str, Callable[[List[Any]], Any]] = {
        "sum": sum,
        "mean": lambda vals: sum(vals) / len(vals) if vals else 0,
        "median": lambda vals: sorted(vals)[len(vals) // 2] if vals else None,
        "max": max,
        "min": min,
        "count": len,
        "first": lambda vals: vals[0] if vals else None,
        "last": lambda vals: vals[-1] if vals else None,
    }

    @classmethod
    def get(cls, name: str) -> Optional[Callable[[List[Any]], Any]]:
        """Get aggregation function by name."""
        return cls._FUNCS.get(name)

    @classmethod
    def register(cls, name: str, func: Callable[[List[Any]], Any]) -> None:
        """Register a custom aggregation function."""
        cls._FUNCS[name] = func

    @classmethod
    def is_builtin(cls, name: str) -> bool:
        """Check if aggregation name is a built-in."""
        return name in cls._FUNCS


# ===== Union Type =====

MaterializationOptions = Union[
    TabularOptions,
    ArrayExpansionOptions,
    FileOutputOptions,
    ROIOptions,
    RegionPropsOptions,
    TiffStackOptions,
]


# ===== Type Validation =====

def validate_options_for_handler(
    handler: str,
    options: MaterializationOptions,
    handler_option_types: Dict[str, type]
) -> None:
    """Validate that options type matches expected type for handler.

    Args:
        handler: Handler name to validate against.
        options: Options instance to validate.
        handler_option_types: Dict mapping handler names to expected option types.

    Raises:
        ValueError: If handler not registered.
        TypeError: If options type doesn't match expected type.
    """
    if handler not in handler_option_types:
        raise ValueError(
            f"Unknown materialization handler: '{handler}'. "
            f"Available handlers: {list(handler_option_types.keys())}"
        )

    expected_type = handler_option_types[handler]

    # Check if options is instance of expected type or None
    if options is None or not isinstance(options, expected_type):
        actual_type = type(options).__name__ if options is not None else "None"
        raise TypeError(
            f"Handler '{handler}' expects {expected_type.__name__}, "
            f"got {actual_type}. "
            f"Use: {expected_type.__name__}(...) instead."
        )


# ===== Helper: Combine Option Types =====

def combine_options(*options: BaseOptions) -> Dict[str, Any]:
    """Combine multiple option types into a single dict (for legacy compatibility).

    This helper is provided for transitioning from dict-based options to typed options.
    It extracts all fields from provided option instances and merges them.

    Args:
        *options: One or more option instances to combine.

    Returns:
        Dict with all option keys and values.

    Example:
        >>> tabular = TabularOptions(fields=["x", "y"])
        >>> file_out = FileOutputOptions(filename_suffix=".csv")
        >>> combined = combine_options(tabular, file_out)
        >>> # {"fields": ["x", "y"], "filename_suffix": ".csv", ...}
    """
    from dataclasses import fields

    combined = {}
    for opt in options:
        if opt is None:
            continue
        if not hasattr(opt, '__dataclass_fields__'):
            raise TypeError(f"Expected dataclass, got {type(opt)}")
        for f in fields(opt):
            value = getattr(opt, f.name)
            if value is not None:
                combined[f.name] = value
    return combined
