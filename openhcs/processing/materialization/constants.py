"""
Constants for materialization system.

Provides handler names, file extensions, and error templates as single source of truth.
"""

from enum import Enum


class HandlerNames(str, Enum):
    """Materialization handler names (registry keys)."""

    # Tabular handlers
    CSV = "csv"
    JSON = "json"
    DUAL = "dual"
    TABULAR = "tabular"  # Generic tabular handler with array expansion

    # Image handlers
    TIFF_STACK = "tiff_stack"

    # ROI handlers
    ROI_ZIP = "roi_zip"
    REGIONPROPS = "regionprops"

    # Deprecated (will be removed)
    CELL_COUNTS = "cell_counts"  # Use TABULAR instead


class FileExtensions(str, Enum):
    """File extensions for materialization outputs."""

    # Output formats
    CSV = ".csv"
    JSON = ".json"
    TIF = ".tif"
    TXT = ".txt"

    # Compound extensions
    ROI_ZIP = ".roi.zip"

    # Suffixes
    DETAILS = "_details.csv"
    SUMMARY = "_summary.txt"
    SEGMENTATION_SUMMARY = "_segmentation_summary.txt"


class OptionKeys(str, Enum):
    """Option keys used in spec.options (for validation/docs).

    NOTE: With typed options, these are for reference only.
    Actual validation is done by dataclass types.
    """

    # Tabular options
    FIELDS = "fields"
    SUMMARY_FIELDS = "summary_fields"
    ANALYSIS_TYPE = "analysis_type"
    INCLUDE_METADATA = "include_metadata"

    # Array expansion options
    ROW_FIELD = "row_field"
    ROW_COLUMNS = "row_columns"
    ROW_UNPACKER = "row_unpacker"
    AGGREGATIONS = "aggregations"

    # File output options
    FILENAME_SUFFIX = "filename_suffix"
    STRIP_ROI_SUFFIX = "strip_roi_suffix"
    STRIP_PKL = "strip_pkl"

    # ROI options
    MIN_AREA = "min_area"
    EXTRACT_CONTOURS = "extract_contours"
    ROI_SUFFIX = "roi_suffix"
    SUMMARY_SUFFIX = "summary_suffix"

    # Region props options
    PROPERTIES = "properties"
    INTENSITY_PROPERTIES = "intensity_properties"
    REQUIRE_INTENSITY = "require_intensity"
    DETAILS_SUFFIX = "details_suffix"
    JSON_SUFFIX = "json_suffix"

    # TIFF stack options
    NORMALIZE_UINT8 = "normalize_uint8"
    EMPTY_SUMMARY = "empty_summary"


# ===== Error Message Templates =====

class ErrorMessages:
    """Templates for consistent error messages."""

    UNKNOWN_HANDLER = "Unknown materialization handler: '{handler}'. Available: {available}"
    HANDLER_ALREADY_REGISTERED = "Materialization handler already registered: '{handler}'"
    OPTIONS_TYPE_MISMATCH = (
        "Handler '{handler}' expects {expected_type}, got {actual_type}. "
        "Use: {expected_type}(...) instead."
    )
    BACKEND_NOT_ALLOWED = (
        "Materialization handler '{handler}' does not allow backends: {disallowed}. "
        "Allowed: {allowed}"
    )
    BACKEND_NO_ARBITRARY_FILES = (
        "Backend '{backend}' does not support arbitrary files for handler '{handler}'."
    )


# ===== Validation Mappings =====

HANDLER_OPTION_TYPES = {
    # Populated at runtime when handlers register
    # HandlerNames.CSV: TabularOptions,
    # HandlerNames.TABULAR: ArrayExpansionOptions,
    # etc.
}
