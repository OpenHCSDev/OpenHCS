"""
Materialization framework for analysis outputs.

Provides composable, declarative materialization functions that transform
analysis results (dataclasses, dicts, arrays) into serialized formats
(CSV, JSON, ROI archives) via the VFS.

Architecture:
    - MaterializationSpec[T]: Type-safe declarative spec with generic options parameter
    - MaterializationRegistry + materialize(): Registry + dispatcher for specs
    - Typed options: TabularOptions, ArrayExpansionOptions, etc. (see options.py)
    - Built-in handlers: tabular, roi_zip, regionprops, tiff_stack

Key Features:
    - Handler name automatically inferred from options type (no manual specification)
    - Fields auto-extracted from data (no manual field list needed)
    - Type-safe options with IDE autocomplete and validation

Usage:
    from openhcs.processing.materialization import (
        MaterializationSpec,
        TabularOptions,
        ArrayExpansionOptions,
    )

    # Simple tabular output - auto-extracts ALL fields from data
    spec = MaterializationSpec(
        options=TabularOptions(),
    )

    # Array expansion (e.g., for cell counting results)
    spec = MaterializationSpec(
        options=ArrayExpansionOptions(
            row_field="cell_positions",
            row_columns={"0": "x_position", "1": "y_position"},
            aggregations={"cell_count": "sum"},
        ),
    )
"""

# Core framework
from openhcs.processing.materialization.core import (
    MaterializationSpec,
    MaterializationRegistry,
    register_materializer,
    materialize,
)

# Typed options (NEW: type-safe configuration)
from openhcs.processing.materialization.options import (
    TabularOptions,
    ArrayExpansionOptions,
    FileOutputOptions,
    ROIOptions,
    RegionPropsOptions,
    TiffStackOptions,
    BuiltinAggregations,
    combine_options,
    MaterializationOptions,
)

# Constants
from openhcs.processing.materialization.constants import (
    HandlerNames,
    FileExtensions,
    OptionKeys,
    ErrorMessages,
    HANDLER_OPTION_TYPES,
)

__all__ = [
    # Core
    "MaterializationSpec",
    "MaterializationRegistry",
    "register_materializer",
    "materialize",
    # Typed options
    "TabularOptions",
    "ArrayExpansionOptions",
    "FileOutputOptions",
    "ROIOptions",
    "RegionPropsOptions",
    "TiffStackOptions",
    "BuiltinAggregations",
    "combine_options",
    "MaterializationOptions",
    # Constants
    "HandlerNames",
    "FileExtensions",
    "OptionKeys",
    "ErrorMessages",
    "HANDLER_OPTION_TYPES",
]
