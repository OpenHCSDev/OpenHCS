"""
Materialization framework for analysis outputs.

Provides composable, declarative materialization functions that transform
analysis results (dataclasses, dicts, arrays) into serialized formats
(CSV, JSON, ROI archives) via the VFS.

Architecture:
    - MaterializationSpec: Declarative spec for how to serialize a type
    - create_materializer(): Factory that creates mat funcs from specs
    - Built-in specs for common patterns (csv_rows, json_summary, roi_archive)

Usage:
    from openhcs.processing.materialization import csv_materializer, json_materializer

    @special_outputs(("cell_counts", csv_materializer(
        fields=["slice_index", "cell_count", "avg_area"],
        filename_suffix="_cell_counts.csv"
    )))
    def count_cells(image):
        ...
"""

from openhcs.processing.materialization.core import (
    MaterializationSpec,
    create_materializer,
    csv_materializer,
    json_materializer,
    dual_materializer,
)

__all__ = [
    "MaterializationSpec",
    "create_materializer", 
    "csv_materializer",
    "json_materializer",
    "dual_materializer",
]
