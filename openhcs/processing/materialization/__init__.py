"""
Materialization framework for analysis outputs.

Provides composable, declarative materialization functions that transform
analysis results (dataclasses, dicts, arrays) into serialized formats
(CSV, JSON, ROI archives) via the VFS.

Architecture:
    - MaterializationSpec: Declarative spec for how to serialize a type
    - MaterializationRegistry + materialize(): Registry + dispatcher for specs
    - Built-in spec builders for common patterns (csv/json/dual/roi/tiff)

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
    MaterializationRegistry,
    register_materializer,
    materialize,
    csv_materializer,
    json_materializer,
    dual_materializer,
    roi_zip_materializer,
    regionprops_materializer,
    tiff_stack_materializer,
    materializer_spec,
)

__all__ = [
    "MaterializationSpec",
    "MaterializationRegistry",
    "register_materializer",
    "materialize",
    "csv_materializer",
    "json_materializer",
    "dual_materializer",
    "roi_zip_materializer",
    "regionprops_materializer",
    "tiff_stack_materializer",
    "materializer_spec",
]
