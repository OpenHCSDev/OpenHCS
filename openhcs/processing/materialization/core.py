"""
Core materialization framework.

Provides a single spec + registry + dispatcher abstraction for analysis materialization.
"""

from __future__ import annotations

import json
import logging
from dataclasses import dataclass, field, fields, is_dataclass
from pathlib import Path
from typing import Any, Callable, Dict, Generic, List, Optional, Sequence, Tuple, TypeVar, Union

import pandas as pd

from openhcs.constants.constants import Backend

# Type variables for generic MaterializationSpec
T = TypeVar('T', bound=object)

logger = logging.getLogger(__name__)

# Import typed options for handler type narrowing
# These are used for type annotations in handlers
from openhcs.processing.materialization.options import (
    TabularOptions,
    ArrayExpansionOptions,
    FileOutputOptions,
    ROIOptions,
    RegionPropsOptions,
    TiffStackOptions,
    BuiltinAggregations,
)


@dataclass(frozen=True)
class MaterializationSpec(Generic[T]):
    """
    Declarative materialization spec with type-safe options.

    Type Parameters:
        T: The type of options (e.g., TabularOptions, ArrayExpansionOptions, etc.)

    Attributes:
        options: Optional typed handler-specific options (validated at construction).
            Can be None for custom handlers that don't need options.
        handler: Optional handler name. If not specified, automatically inferred from options type.
            For custom handlers using dict options, handler must be specified explicitly.
        allowed_backends: Optional allowlist of backend names.

    Example (built-in handler - handler inferred):
        >>> from openhcs.processing.materialization.options import TabularOptions
        >>> spec = MaterializationSpec(options=TabularOptions())

    Example (custom handler - handler required):
        >>> spec = MaterializationSpec(handler="custom_handler", options={})
    """
    options: Optional[T] = None
    handler: Optional[str] = None
    allowed_backends: Optional[List[str]] = None

    def __post_init__(self):
        """Infer handler if not specified, then validate."""
        # If no options provided (custom handler), skip inference
        if self.options is None:
            return

        # For custom handlers using dict options, handler is explicitly provided
        # Don't try to infer (won't work for dict options)
        if self.handler is None and isinstance(self.options, dict):
            # Custom handler with dict options - keep handler as None
            # Will be validated at runtime
            return

        # If handler not specified, infer from options type
        if self.handler is None:
            inferred = MaterializationRegistry.get_handler_for_options(type(self.options))
            object.__setattr__(self, 'handler', inferred)

        # Validate that options type is registered (only for typed handlers)
        from openhcs.processing.materialization.constants import HANDLER_OPTION_TYPES

        handler_option_types = HANDLER_OPTION_TYPES
        actual_handler = self.handler

        # Skip validation for custom handlers (no type registration)
        if actual_handler is None or actual_handler not in handler_option_types:
            return

        expected_type = handler_option_types[actual_handler]

        # Check if options is instance of expected type
        if not isinstance(self.options, expected_type):
            actual_type = type(self.options).__name__
            raise TypeError(
                f"Handler '{actual_handler}' expects {expected_type.__name__}, "
                f"got {actual_type}. "
                f"Use: {expected_type.__name__}(...) instead."
            )


@dataclass(frozen=True)
class MaterializationHandler:
    """Container for a materialization handler and its metadata."""
    name: str
    func: Callable[..., str]
    requires_arbitrary_files: bool = True
    options_type: Optional[type] = None  # Expected options type for this handler


class MaterializationRegistry:
    """Registry for materialization handlers with type tracking."""

    _handlers: Dict[str, MaterializationHandler] = {}
    _option_types: Dict[str, type] = {}  # Handler name -> options type mapping
    _options_to_handler: Dict[type, str] = {}  # Options type -> handler name (reverse mapping)

    @classmethod
    def register(
        cls,
        name: str,
        func: Callable[..., str],
        *,
        options_type: Optional[type] = None,
        requires_arbitrary_files: bool = True
    ) -> None:
        """Register a materialization handler with its options type.

        Args:
            name: Handler name
            func: Handler function
            options_type: Expected options dataclass type for validation
            requires_arbitrary_files: Whether this handler requires arbitrary file support

        Raises:
            ValueError: If handler already registered with a different function
        """
        # Check if already registered
        if name in cls._handlers:
            existing = cls._handlers[name]
            # Allow re-registration if it's the exact same function (idempotent)
            if existing.func is func:
                logger.debug(f"Handler '{name}' already registered with same function, skipping")
                return
            # Different function trying to use same name - error
            raise ValueError(
                f"Materialization handler '{name}' already registered with "
                f"different function. Cannot re-register."
            )

        cls._handlers[name] = MaterializationHandler(
            name=name,
            func=func,
            requires_arbitrary_files=requires_arbitrary_files,
            options_type=options_type
        )

        # Store options type for validation and reverse lookup
        if options_type is not None:
            cls._option_types[name] = options_type
            cls._options_to_handler[options_type] = name

            # Also populate constants HANDLER_OPTION_TYPES for shared access
            from openhcs.processing.materialization.constants import HANDLER_OPTION_TYPES
            HANDLER_OPTION_TYPES[name] = options_type

    @classmethod
    def get(cls, name: str) -> MaterializationHandler:
        """Get handler by name.

        Args:
            name: Handler name

        Returns:
            MaterializationHandler instance

        Raises:
            KeyError: If handler not found
        """
        if name not in cls._handlers:
            raise KeyError(f"Unknown materialization handler: {name}")
        return cls._handlers[name]

    @classmethod
    def get_handler_for_options(cls, options_type: type) -> Optional[str]:
        """Get handler name from options type.

        Args:
            options_type: Options dataclass type

        Returns:
            Handler name string, or None if not registered (for custom handlers)
        """
        return cls._options_to_handler.get(options_type)

    @classmethod
    def get_options_type(cls, name: str) -> Optional[type]:
        """Get expected options type for a handler.

        Args:
            name: Handler name

        Returns:
            Options type or None if not specified
        """
        return cls._option_types.get(name)


def register_materializer(
    name: str,
    *,
    options_type: Optional[type] = None,
    requires_arbitrary_files: bool = True
) -> Callable[[Callable[..., str]], Callable[..., str]]:
    """Decorator to register a materialization handler with type tracking.

    Args:
        name: Handler name
        options_type: Expected options dataclass type for validation
        requires_arbitrary_files: Whether handler requires arbitrary file support

    Returns:
        Decorator function

    Example:
        >>> from openhcs.processing.materialization.options import TabularOptions
        >>>
        >>> @register_materializer("csv", options_type=TabularOptions)
        >>> def _materialize_csv(...):
        ...     ...
    """
    def decorator(func: Callable[..., str]) -> Callable[..., str]:
        MaterializationRegistry.register(
            name,
            func,
            options_type=options_type,
            requires_arbitrary_files=requires_arbitrary_files
        )
        func.__materialization_handler__ = name
        return func
    return decorator


# ===== Type Guard for Options =====

T = TypeVar('T', bound=object)

def _expect_options(spec: MaterializationSpec, options_type: type[T]) -> T:
    """Type narrowing for handler options (validation already done in __post_init__).

    This function provides type narrowing for type checkers.
    Runtime validation is already handled by MaterializationSpec.__post_init__.

    Args:
        spec: MaterializationSpec containing options
        options_type: Expected options type (e.g., TabularOptions)

    Returns:
        The options, narrowed to the specified type

    Example:
        >>> # In handler:
        >>> options = _expect_options(spec, TabularOptions)
        >>> # Type checker knows options is TabularOptions
        >>> fields = options.fields  # Autocomplete works!
    """
    return spec.options


def _normalize_backends(backends: Sequence[str] | str) -> List[str]:
    if isinstance(backends, str):
        return [backends]
    return list(backends)


class PathBuilder:
    """Unified path generation for materialization handlers.

    Eliminates repeated path construction logic.
    """
    def __init__(self, base_path: str, *, strip_roi: bool = False, strip_pkl: bool = True):
        p = Path(base_path)
        name = p.name
        if name.endswith(".roi.zip"):
            name = name[: -len(".roi.zip")]
        if strip_pkl and name.endswith(".pkl"):
            name = name[: -len(".pkl")]
        if strip_roi and name.endswith(".roi"):
            name = name[: -len(".roi")]
        self.base_path = p.with_name(name)
        self.parent = self.base_path.parent
        self.name = self.base_path.name

    def with_suffix(self, suffix: str) -> str:
        """Add a suffix to the base path."""
        return str(self.parent / f"{self.name}{suffix}")

    def with_default_ext(self, default_ext: str) -> str:
        """Add a default extension."""
        return str(self.parent / f"{self.name}{default_ext}")


class BackendSaver:
    """Centralized multi-backend save pattern.
    
    Eliminates repeated backend iteration boilerplate across handlers.
    """
    def __init__(self, backends: List[str], filemanager, backend_kwargs: Dict[str, Dict[str, Any]]):
        self.backends = backends
        self.filemanager = filemanager
        self.backend_kwargs = backend_kwargs or {}
    
    def save(self, content, path: str) -> None:
        """Save content to path across all backends."""
        for backend in self.backends:
            _prepare_output_path(self.filemanager, backend, path)
            kwargs = self.backend_kwargs.get(backend, {})
            self.filemanager.save(content, path, backend, **kwargs)
    
    def save_if(self, condition: bool, content, path: str) -> None:
        """Save content if condition is True."""
        if condition:
            self.save(content, path)


def _extract_fields(item: Any, field_names: Optional[List[str]] = None) -> Dict[str, Any]:
    """Extract fields from dataclass, dict, or pandas DataFrame.

    Supports:
    - dataclass instances (uses dataclass reflection)
    - dicts (uses dict keys)
    - pandas DataFrames (uses column names)
    - pandas Series (uses index)

    Returns:
        Dict mapping field names to values
    """
    # Handle pandas DataFrames
    try:
        import pandas as pd
        if isinstance(item, pd.DataFrame):
            if field_names:
                # Select only requested columns that exist
                return {f: item[f].tolist() for f in field_names if f in item.columns}
            # Return all columns as lists
            return {col: item[col].tolist() for col in item.columns}

        if isinstance(item, pd.Series):
            if field_names:
                return {f: item[f] for f in field_names if f in item.index}
            return item.to_dict()
    except ImportError:
        pass

    if is_dataclass(item):
        if field_names:
            return {f: getattr(item, f, None) for f in field_names if hasattr(item, f)}
        return {f.name: getattr(item, f.name) for f in fields(item)}
    if isinstance(item, dict):
        if field_names:
            return {f: item.get(f) for f in field_names if f in item}
        return item
    return {"value": item}


def _prepare_output_path(filemanager, backend: str, output_path: str) -> None:
    backend_instance = filemanager._get_backend(backend)
    if backend_instance.requires_filesystem_validation:
        filemanager.ensure_directory(str(Path(output_path).parent), backend)
        if filemanager.exists(output_path, backend):
            filemanager.delete(output_path, backend)


def _validate_backends(
    spec: MaterializationSpec,
    handler: MaterializationHandler,
    backends: List[str],
    filemanager
) -> None:
    if spec.allowed_backends is not None:
        disallowed = [b for b in backends if b not in spec.allowed_backends]
        if disallowed:
            raise ValueError(
                f"Materialization handler '{handler.name}' does not allow backends: {disallowed}. "
                f"Allowed: {spec.allowed_backends}"
            )

    if handler.requires_arbitrary_files:
        for backend in backends:
            backend_instance = filemanager._get_backend(backend)
            if not backend_instance.supports_arbitrary_files:
                raise ValueError(
                    f"Backend '{backend}' does not support arbitrary files for handler "
                    f"'{handler.name}'."
                )


def materialize(
    spec: MaterializationSpec,
    data: Any,
    path: str,
    filemanager,
    backends: Sequence[str] | str,
    backend_kwargs: Optional[Dict[str, Dict[str, Any]]] = None,
    context: Any = None,
    extra_inputs: Optional[Dict[str, Any]] = None,
) -> str:
    handler_name = spec.handler or "custom"

    handler = MaterializationRegistry.get(handler_name)
    normalized_backends = _normalize_backends(backends)
    _validate_backends(spec, handler, normalized_backends, filemanager)

    # Pass options if available, otherwise pass spec directly
    return handler.func(
        data,
        path,
        filemanager,
        normalized_backends,
        backend_kwargs or {},
        spec,
        context,
        extra_inputs or {},
    )


# Built-in handlers

@register_materializer("tabular", options_type=TabularOptions, requires_arbitrary_files=True)
def _materialize_tabular(
    data: List[Any],
    path: str,
    filemanager,
    backends: List[str],
    backend_kwargs: Dict[str, Dict[str, Any]],
    spec: MaterializationSpec,
    context: Any,
    extra_inputs: Dict[str, Any],
) -> str:
    """Unified tabular materializer for CSV, JSON, or dual output.

    Uses options.output_format to determine which format(s) to generate:
    - "csv": CSV file only
    - "json": JSON file with nested results
    - "dual": Both CSV + JSON files

    Replaceses separate csv, json, and dual handlers with a single implementation.
    """
    options = _expect_options(spec, TabularOptions)
    saver = BackendSaver(backends, filemanager, backend_kwargs)

    # Determine output format
    format_name = spec.handler if spec.handler in ("csv", "json", "dual") else options.output_format

    # Generate output paths
    paths = PathBuilder(path, strip_roi=options.strip_roi_suffix if hasattr(options, 'strip_roi_suffix') else False)
    csv_path = paths.with_suffix("_details.csv")
    json_path = paths.with_suffix(".json")

    # Extract data ONCE for all formats
    rows = []
    for i, item in enumerate(data or []):
        row = _extract_fields(item, options.fields)
        if "slice_index" not in row:
            row["slice_index"] = i
        rows.append(row)

    # Generate outputs based on format
    if format_name in ("csv", "dual") and rows:
        csv_content = pd.DataFrame(rows).to_csv(index=False)
        saver.save(csv_content, csv_path)

    if format_name in ("json", "dual"):
        summary_data = [_extract_fields(item, options.summary_fields or options.fields) or {"slice_index": i}
                      for i, item in enumerate(data or [])]
        summary = {"total_items": len(summary_data), "results": summary_data}
        saver.save(json.dumps(summary, indent=2, default=str), json_path)

    # Return primary path
    return json_path if format_name in ("json", "dual") else csv_path


@register_materializer("tiff_stack", options_type=TiffStackOptions, requires_arbitrary_files=True)
def _materialize_tiff_stack(
    data: List[Any],
    path: str,
    filemanager,
    backends: List[str],
    backend_kwargs: Dict[str, Dict[str, Any]],
    spec: MaterializationSpec,
    context: Any,
    extra_inputs: Dict[str, Any],
) -> str:
    """Materialize image arrays as TIFF stack using typed TiffStackOptions."""
    options = _expect_options(spec, TiffStackOptions)
    saver = BackendSaver(backends, filemanager, backend_kwargs)
    paths = PathBuilder(path, strip_roi=options.strip_roi_suffix, strip_pkl=options.strip_pkl)

    # Empty data case
    if not data:
        summary_path = paths.with_suffix(options.summary_suffix)
        saver.save(options.empty_summary, summary_path)
        return summary_path

    # Save individual TIFFs
    base_name = paths.name
    for i, arr in enumerate(data):
        filename = str(paths.parent / f"{base_name}_slice_{i:03d}.tif")
        out_arr = arr
        if options.normalize_uint8 and out_arr.dtype != "uint8":
            max_val = getattr(out_arr, "max", lambda: 0)()
            out_arr = (out_arr * 255).astype("uint8") if max_val <= 1.0 else out_arr.astype("uint8")
        saver.save(out_arr, filename)

    # Save summary
    summary_path = paths.with_suffix(options.summary_suffix)
    summary_content = f"Images saved: {len(data)} files\n" \
                     f"Base filename pattern: {base_name}_slice_XXX.tif\n" \
                     f"Image dtype: {data[0].dtype}\n" \
                     f"Image shape: {data[0].shape}\n"
    saver.save(summary_content, summary_path)
    return summary_path

    base_path = _generate_output_path(path, "", "", strip_roi=strip_roi, strip_pkl=strip_pkl)
    for i, arr in enumerate(data):
        filename = f"{base_path}_slice_{i:03d}.tif"
        out_arr = arr
        if normalize_uint8:
            if out_arr.dtype != "uint8":
                max_val = getattr(out_arr, "max", lambda: 0)()
                if max_val <= 1.0:
                    out_arr = (out_arr * 255).astype("uint8")
                else:
                    out_arr = out_arr.astype("uint8")

        for backend in backends:
            _prepare_output_path(filemanager, backend, filename)
            kwargs = backend_kwargs.get(backend, {})
            filemanager.save(out_arr, filename, backend, **kwargs)

    summary_path = f"{base_path}{summary_suffix}"
    summary_content = f"Images saved: {len(data)} files\n"
    summary_content += f"Base filename pattern: {base_path}_slice_XXX.tif\n"
    summary_content += f"Image dtype: {data[0].dtype}\n"
    summary_content += f"Image shape: {data[0].shape}\n"

    for backend in backends:
        _prepare_output_path(filemanager, backend, summary_path)
        kwargs = backend_kwargs.get(backend, {})
        filemanager.save(summary_content, summary_path, backend, **kwargs)

    return summary_path


@register_materializer("roi_zip", options_type=ROIOptions, requires_arbitrary_files=True)
def _materialize_roi_zip(
    data: List[Any],
    path: str,
    filemanager,
    backends: List[str],
    backend_kwargs: Dict[str, Dict[str, Any]],
    spec: MaterializationSpec,
    context: Any,
    extra_inputs: Dict[str, Any],
) -> str:
    """Materialize segmentation masks as ROI zip using typed ROIOptions."""
    from polystore.roi import extract_rois_from_labeled_mask

    options = _expect_options(spec, ROIOptions)
    saver = BackendSaver(backends, filemanager, backend_kwargs)
    paths = PathBuilder(path, strip_roi=options.strip_roi_suffix, strip_pkl=options.strip_pkl)

    # Empty data case
    if not data:
        summary_path = paths.with_suffix(options.summary_suffix)
        saver.save("No segmentation masks generated (empty data)\n", summary_path)
        return summary_path

    # Extract ROIs
    all_rois = []
    for mask in data:
        rois = extract_rois_from_labeled_mask(mask, min_area=options.min_area, extract_contours=options.extract_contours)
        all_rois.extend(rois)

    # Save ROI file
    roi_path = paths.with_suffix(options.roi_suffix)
    saver.save_if(len(all_rois) > 0, all_rois, roi_path)

    # Save summary
    summary_path = paths.with_suffix(options.summary_suffix)
    summary_content = f"Segmentation ROIs: {len(all_rois)} cells\nZ-planes: {len(data)}\n"
    if all_rois:
        summary_content += f"ROI file: {roi_path}\n"
    else:
        summary_content += "No ROIs extracted (all regions below min_area threshold)\n"
    saver.save(summary_content, summary_path)
    return summary_path


def _coerce_jsonable(value: Any) -> Any:
    """Convert numpy types to JSON-serializable Python types."""
    try:
        import numpy as np
        if isinstance(value, np.generic):
            return value.item()
        if isinstance(value, np.ndarray):
            return value.tolist()
    except Exception:
        pass
    return value


def _normalize_slices(obj: Any, *, name: str) -> List[np.ndarray]:
    """Normalize input to list of 2D arrays."""
    import numpy as np
    if obj is None:
        return []
    if isinstance(obj, list):
        return [np.asarray(x) for x in obj]
    arr = np.asarray(obj)
    if arr.ndim == 2:
        return [arr]
    if arr.ndim == 3:
        return [arr[i] for i in range(arr.shape[0])]
    raise ValueError(f"{name} must be a 2D/3D array or list of 2D arrays, got shape {arr.shape}")


@register_materializer("regionprops", options_type=RegionPropsOptions, requires_arbitrary_files=True)
def _materialize_regionprops(
    data: Any,
    path: str,
    filemanager,
    backends: List[str],
    backend_kwargs: Dict[str, Dict[str, Any]],
    spec: MaterializationSpec,
    context: Any,
    extra_inputs: Dict[str, Any],
) -> str:
    """
    Materialize region properties from labeled masks.

    Input:
      - data: labeled mask(s) as list[2D] or 3D ndarray (Z, Y, X)
      - extra_inputs["intensity"]: optional aligned intensity slices to compute intensity metrics

    Output:
      - ROI zip archive (for Fiji/Napari) + CSV details + JSON summary
    """
    import numpy as np
    from skimage.measure import regionprops_table
    from polystore.roi import ROI, extract_rois_from_labeled_mask

    options = _expect_options(spec, RegionPropsOptions)
    saver = BackendSaver(backends, filemanager, backend_kwargs)
    paths = PathBuilder(path)

    # Configure properties
    base_properties = list(options.properties or ["label", "area", "perimeter", "centroid", "bbox"])
    intensity_properties = list(options.intensity_properties or ["mean_intensity"])
    for required in ("label", "area", "centroid", "bbox"):
        if required not in base_properties:
            base_properties.append(required)

    # Normalize input slices
    intensity = extra_inputs.get("intensity") or extra_inputs.get("intensity_slices")
    intensity_slices = _normalize_slices(intensity, name="intensity") if intensity is not None else []

    if options.require_intensity and not intensity_slices:
        raise ValueError(
            "regionprops materializer requires intensity input. "
            "Pass extra_inputs['intensity'] or set require_intensity=False."
        )
    if intensity_slices and len(intensity_slices) != len(_normalize_slices(data, name="label")):
        raise ValueError("Intensity/label slice count mismatch.")

    # Setup paths
    json_path = paths.with_suffix(options.json_suffix)
    csv_path = paths.with_suffix(options.details_suffix)
    roi_path = paths.with_suffix(options.roi_suffix)

    all_rois: List[ROI] = []
    rows: List[Dict[str, Any]] = []
    per_slice: List[Dict[str, Any]] = []
    label_slices = _normalize_slices(data, name="labeled_mask")

    # Process each slice
    for z_idx, labels in enumerate(label_slices):
        if labels.ndim != 2:
            raise ValueError(f"Label slice {z_idx} must be 2D")
        if not np.issubdtype(labels.dtype, np.integer):
            labels = labels.astype(np.int32)

        intensity_img = intensity_slices[z_idx] if intensity_slices else None
        if intensity_img and (intensity_img.ndim != 2 or intensity_img.shape != labels.shape):
            raise ValueError("Intensity slice shape mismatch.")

        # Compute region properties
        props = list(dict.fromkeys(base_properties + (intensity_properties if intensity_img else [])))
        table = regionprops_table(labels, intensity_image=intensity_img, properties=props)

        # Filter and extract data
        areas = table.get("area")
        keep_idx = [i for i, a in enumerate(areas or []) if float(a) >= options.min_area] if areas is not None else list(range(len(table.get("label", []))))
        labels_col = table.get("label", [])
        kept_labels = [int(labels_col[i]) for i in keep_idx]

        # Build CSV rows
        for i in keep_idx:
            row = {"slice_index": z_idx}
            for key, values in table.items() or {}:
                if values is not None:
                    row[key.replace("-", "_")] = _coerce_jsonable(values[i])
            rows.append(row)

        # Build per-slice summary
        slice_summary: Dict[str, Any] = {"slice_index": z_idx, "region_count": len(keep_idx)}
        if areas and keep_idx:
            kept_areas = [float(areas[i]) for i in keep_idx]
            slice_summary["total_area"] = sum(kept_areas)
            slice_summary["mean_area"] = sum(kept_areas) / len(kept_areas)
        if intensity_img and (mean_int := table.get("mean_intensity")) and keep_idx:
            slice_summary["mean_mean_intensity"] = sum([float(mean_int[i]) for i in keep_idx]) / len(keep_idx)
        per_slice.append(slice_summary)

        # Extract and annotate ROIs
        rois = extract_rois_from_labeled_mask(labels, min_area=options.min_area, extract_contours=options.extract_contours)
        intensity_by_label = {
            int(labels_col[i]): {k: _coerce_jsonable(table[k][i]) for k in intensity_properties if k in table}
            for i in keep_idx
        } if intensity_img and kept_labels else {}

        for roi in rois:
            label_id = int(roi.metadata.get("label", 0))
            metadata = dict(roi.metadata, slice_index=z_idx)
            if label_id in intensity_by_label:
                metadata.update(intensity_by_label[label_id])
            all_rois.append(ROI(shapes=roi.shapes, metadata=metadata))

    # Build and save summary
    summary = {
        "total_slices": len(label_slices),
        "total_regions": len(rows),
        "regions_per_slice": per_slice,
        "details_csv": csv_path,
        "roi_zip": roi_path,
        "properties": base_properties,
        "intensity_properties": intensity_properties if intensity_slices else [],
    }
    saver.save(json.dumps(summary, indent=2, default=str), json_path)

    # Save CSV and ROI if data exists
    if rows:
        saver.save(pd.DataFrame(rows).to_csv(index=False), csv_path)
    if all_rois:
        saver.save(all_rois, roi_path)

    return json_path


# ===== Helper functions for array field discovery and expansion =====

def _discover_array_fields(item: Any) -> List[str]:
    """Discover all array/tuple fields in a dataclass.

    Args:
        item: Dataclass instance to inspect

    Returns:
        List of field names that are array/tuple types
    """
    if not hasattr(item, '__dataclass_fields__'):
        return []

    from dataclasses import fields
    from typing import get_origin

    array_fields = []
    for f in fields(item):
        value = getattr(item, f.name, None)
        origin = hasattr(f.type, '__origin__') and get_origin(f.type)
        if origin in (list, List, tuple, Tuple):
            array_fields.append(f.name)
        elif isinstance(value, list) and value and isinstance(value[0], (tuple, list)):
            array_fields.append(f.name)
    return array_fields


def _expand_array_field(
    array_data: List[Any],
    base_row: Dict[str, Any],
    row_columns: Dict[str, str]
) -> List[Dict[str, Any]]:
    """Expand an array field into multiple rows.

    Args:
        array_data: Array data to expand
        base_row: Base fields to include in each row
        row_columns: Mapping from array indices to column names

    Returns:
        List of expanded rows
    """
    if not array_data:
        return [base_row]

    return [
        {
            **base_row,
            **{col: elem[int(idx)] for idx, col in row_columns.items() if isinstance(elem, (list, tuple)) and int(idx) < len(elem)}
        }
        for elem in array_data
    ]


# ===== Generic tabular handler with array expansion =====
# This replaces the obsolete cell_counts handler

@register_materializer("tabular", options_type=ArrayExpansionOptions, requires_arbitrary_files=True)
def _materialize_tabular_with_arrays(
    data: List[Any],
    path: str,
    filemanager,
    backends: List[str],
    backend_kwargs: Dict[str, Dict[str, Any]],
    spec: MaterializationSpec,
    context: Any,
    extra_inputs: Dict[str, Any],
) -> str:
    """
    Generic handler for tabular output with array expansion.

    Outputs:
    1. JSON summary with aggregated statistics
    2. CSV with one row per array element

    Supports two expansion modes:
    1. Dict-based: row_columns={"0": "x", "1": "y"} for simple tuple indexing
    2. Callable: row_unpacker=custom_func for complex unpacking logic

    Supports two aggregation modes:
    1. String-based: aggregations={"field": "sum"} using built-in functions
    2. Callable: aggregations={"field": custom_func} for custom logic
    """
    options = _expect_options(spec, ArrayExpansionOptions)
    saver = BackendSaver(backends, filemanager, backend_kwargs)
    paths = PathBuilder(path, strip_roi=False, strip_pkl=True)

    # Setup paths
    json_path = paths.with_suffix(getattr(options, 'filename_suffix', '.json'))
    csv_path = paths.with_suffix("_details.csv")

    # Build rows using array expansion
    rows = []
    for item_idx, item in enumerate(data or []):
        base_row = _extract_fields(item, options.fields)
        if "slice_index" not in base_row and "slice_index" not in (options.fields or []):
            base_row["slice_index"] = item_idx

        # Expansion strategy dispatch
        if options.row_unpacker:
            # Strategy 1: Custom unpacker
            for exp_row in options.row_unpacker(item):
                rows.append({**base_row, **exp_row})
        elif options.row_field:
            # Strategy 2: Explicit field mode
            array_data = getattr(item, options.row_field, [])
            rows.extend(_expand_array_field(array_data, base_row, options.row_columns))
        elif array_fields := _discover_array_fields(item):
            # Strategy 3: Auto-discovery mode
            primary_field = array_fields[0]
            array_data = getattr(item, primary_field, [])
            rows.extend(_expand_array_field(array_data, base_row, {}))
        else:
            rows.append(base_row)

    # Build and save summary
    summary = _build_summary_from_data(
        data or [],
        options.summary_fields or options.fields,
        options.aggregations,
        options.include_metadata
    )
    summary.setdefault("total_items", len(data or []))
    saver.save(json.dumps(summary, indent=2, default=str), json_path)

    # Save CSV
    if rows:
        saver.save(pd.DataFrame(rows).to_csv(index=False), csv_path)
    logger.info(f"Materialized {len(rows)} rows to {json_path}")
    return json_path


def _discover_aggregations(data: List[Any]) -> Dict[str, Union[str, Callable[[List[Any]], Any]]]:
    """Auto-discover aggregations based on dataclass field types.

    Args:
        data: List of dataclass instances

    Returns:
        Dict mapping aggregation names to built-in aggregation functions
    """
    if not data:
        return {}

    first_item = data[0]
    if not hasattr(first_item, '__dataclass_fields__'):
        return {}

    from dataclasses import fields
    from typing import get_origin

    aggregations = {}

    for f in fields(first_item):
        field_value = getattr(first_item, f.name, None)
        if field_value is None:
            continue

        # Get type origin for generic types
        origin = get_origin(f.type)

        # Dispatch based on type
        if origin in (list, List):
            aggregations[f"{f.name}_count"] = "count"
        elif f.type in (int, float):
            aggregations[f"{f.name}_sum"] = "sum"
            if len(data) > 1:
                aggregations[f"{f.name}_mean"] = "mean"
        elif f.type == str:
            aggregations[f"{f.name}_first"] = "first"

    logger.debug(f"Auto-discovered aggregations: {list(aggregations.keys())}")
    return aggregations


def _build_summary_from_data(
    data: List[Any],
    field_names: Optional[List[str]],
    aggregations: Dict[str, Union[str, Callable[[List[Any]], Any]]],
    include_metadata: bool
) -> Dict[str, Any]:
    """Build summary dict from data using aggregation specifications.

    Args:
        data: List of data items
        field_names: Fields to extract from each item
        aggregations: Dict mapping result keys to aggregation specs
        include_metadata: Whether to include metadata

    Returns:
        Summary dict with aggregated values
    """
    summary = {}
    if not aggregations:
        aggregations = _discover_aggregations(data)
    if not aggregations:
        return summary

    for key, agg_spec in aggregations.items():
        if isinstance(agg_spec, str):
            agg_func = BuiltinAggregations.get(agg_spec)
            if agg_func:
                values = [_extract_fields(item, field_names)[field_names[0]] if field_names and field_names[0] in _extract_fields(item, field_names) else list(_extract_fields(item, field_names).values())[0] if not field_names else item for item in data]
                summary[key] = agg_func(values) if values else None
        elif callable(agg_spec):
            try:
                summary[key] = agg_spec(data)
            except Exception as e:
                logger.warning(f"Custom aggregation failed: {e}")
                summary[key] = None

    return summary
