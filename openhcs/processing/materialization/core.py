"""
Core materialization framework.

Provides a single spec + registry + dispatcher abstraction for analysis materialization.
"""

from __future__ import annotations

import json
import logging
from dataclasses import dataclass, field, fields, is_dataclass
from pathlib import Path
from typing import Any, Callable, Dict, Generic, List, Optional, Sequence, TypeVar, Union

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
)


@dataclass(frozen=True)
class MaterializationSpec(Generic[T]):
    """
    Declarative materialization spec with type-safe options.

    Type Parameters:
        T: The type of options (e.g., TabularOptions, ArrayExpansionOptions, etc.)

    Attributes:
        handler: Registered handler name in MaterializationRegistry.
        options: Typed handler-specific options (validated at construction).
        allowed_backends: Optional allowlist of backend names.

    Example:
        >>> from openhcs.processing.materialization.options import TabularOptions
        >>> spec = MaterializationSpec(
        ...     handler="csv",
        ...     options=TabularOptions(fields=["x", "y"]),
        ... )
    """
    handler: str
    options: T
    allowed_backends: Optional[List[str]] = None

    def __post_init__(self):
        """Validate options type at construction time (fail fast)."""
        # Import here to avoid circular dependency
        from openhcs.processing.materialization.constants import HANDLER_OPTION_TYPES

        handler_option_types = HANDLER_OPTION_TYPES

        # Only validate if handler is registered (may not be during import time)
        if self.handler in handler_option_types:
            expected_type = handler_option_types[self.handler]

            # Check if options is instance of expected type
            if not isinstance(self.options, expected_type):
                actual_type = type(self.options).__name__
                raise TypeError(
                    f"Handler '{self.handler}' expects {expected_type.__name__}, "
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
            name: Handler name (used in MaterializationSpec.handler)
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

        # Store options type for validation
        if options_type is not None:
            cls._option_types[name] = options_type

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
    """Type guard: runtime check + type narrowing for handler options.

    This function provides BOTH:
    - Runtime type checking (catches bugs early)
    - Type narrowing (type checker understands the return type)

    Args:
        spec: MaterializationSpec containing options
        options_type: Expected options type (e.g., TabularOptions)

    Returns:
        The options, narrowed to the specified type

    Raises:
        TypeError: If options don't match expected type

    Example:
        >>> # In handler:
        >>> options = _expect_options(spec, TabularOptions)
        >>> # Type checker knows options is TabularOptions
        >>> fields = options.fields  # Autocomplete works!
    """
    if not isinstance(spec.options, options_type):
        actual_type = type(spec.options).__name__
        expected_type = options_type.__name__
        raise TypeError(
            f"Handler expects {expected_type}, got {actual_type}. "
            f"Use: MaterializationSpec(handler, {expected_type}(...))"
        )
    return spec.options


def _normalize_backends(backends: Sequence[str] | str) -> List[str]:
    if isinstance(backends, str):
        return [backends]
    return list(backends)


def _extract_fields(item: Any, field_names: Optional[List[str]] = None) -> Dict[str, Any]:
    """Extract fields from dataclass or dict."""
    if is_dataclass(item):
        if field_names:
            return {f: getattr(item, f, None) for f in field_names if hasattr(item, f)}
        return {f.name: getattr(item, f.name) for f in fields(item)}
    if isinstance(item, dict):
        if field_names:
            return {f: item.get(f) for f in field_names if f in item}
        return item
    return {"value": item}


def _strip_known_suffixes(path: str, *, strip_roi: bool = False, strip_pkl: bool = True) -> Path:
    """
    Strip known suffixes from a path while preserving compound suffix semantics.

    Note: Path.stem only strips the last suffix (e.g., ".zip"), which breaks compound
    suffixes like ".roi.zip" (it leaves a dangling ".roi"). We treat ".roi.zip" as a
    single compound suffix and remove it atomically.
    """
    p = Path(path)
    name = p.name

    # Strip compound suffixes first
    if name.endswith(".roi.zip"):
        name = name[: -len(".roi.zip")]

    # Strip common single suffixes
    if strip_pkl and name.endswith(".pkl"):
        name = name[: -len(".pkl")]
    if strip_roi and name.endswith(".roi"):
        name = name[: -len(".roi")]

    return p.with_name(name)


def _generate_output_path(
    base_path: str,
    suffix: str,
    default_ext: str,
    *,
    strip_roi: bool = False,
    strip_pkl: bool = True
) -> str:
    """Generate output path with proper suffix handling."""
    path = _strip_known_suffixes(base_path, strip_roi=strip_roi, strip_pkl=strip_pkl)
    parent = path.parent
    if suffix:
        return str(parent / f"{path.name}{suffix}")
    return str(parent / f"{path.name}{default_ext}")


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
    handler = MaterializationRegistry.get(spec.handler)
    normalized_backends = _normalize_backends(backends)
    _validate_backends(spec, handler, normalized_backends, filemanager)
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

@register_materializer("csv", options_type=TabularOptions, requires_arbitrary_files=True)
def _materialize_csv(
    data: List[Any],
    path: str,
    filemanager,
    backends: List[str],
    backend_kwargs: Dict[str, Dict[str, Any]],
    spec: MaterializationSpec,
    context: Any,
    extra_inputs: Dict[str, Any],
) -> str:
    """Materialize data as CSV using typed TabularOptions."""
    # Type guard: runtime check + type narrowing
    options = _expect_options(spec, TabularOptions)

    # Direct attribute access - no .get() needed!
    fields_opt = options.fields
    strip_roi = options.strip_roi_suffix if hasattr(options, 'strip_roi_suffix') else False

    # Generate output path
    filename_suffix = getattr(options, 'filename_suffix', '.csv')
    output_path = _generate_output_path(path, filename_suffix, ".csv", strip_roi=strip_roi)

    rows = []
    for i, item in enumerate(data or []):
        row = _extract_fields(item, fields_opt)
        if "slice_index" not in row:
            row["slice_index"] = i
        rows.append(row)

    if rows:
        df = pd.DataFrame(rows)
        csv_content = df.to_csv(index=False)
        for backend in backends:
            _prepare_output_path(filemanager, backend, output_path)
            kwargs = backend_kwargs.get(backend, {})
            filemanager.save(csv_content, output_path, backend, **kwargs)

    logger.info(f"Materialized {len(rows)} rows to {output_path}")
    return output_path


@register_materializer("json", options_type=TabularOptions, requires_arbitrary_files=True)
def _materialize_json(
    data: List[Any],
    path: str,
    filemanager,
    backends: List[str],
    backend_kwargs: Dict[str, Dict[str, Any]],
    spec: MaterializationSpec,
    context: Any,
    extra_inputs: Dict[str, Any],
) -> str:
    """Materialize data as JSON using typed TabularOptions."""
    # Type guard: runtime check + type narrowing
    options = _expect_options(spec, TabularOptions)

    # Direct attribute access
    fields_opt = options.fields
    analysis_type = options.analysis_type
    include_metadata = options.include_metadata
    strip_roi = options.strip_roi_suffix if hasattr(options, 'strip_roi_suffix') else False

    # Generate output path
    filename_suffix = getattr(options, 'filename_suffix', '.json')
    output_path = _generate_output_path(path, filename_suffix, ".json", strip_roi=strip_roi)

    results = []
    for i, item in enumerate(data or []):
        record = _extract_fields(item, fields_opt)
        if "slice_index" not in record:
            record["slice_index"] = i
        results.append(record)

    summary = {
        "total_items": len(results),
        "results": results
    }
    if include_metadata and analysis_type:
        summary["analysis_type"] = analysis_type

    json_content = json.dumps(summary, indent=2, default=str)
    for backend in backends:
        _prepare_output_path(filemanager, backend, output_path)
        kwargs = backend_kwargs.get(backend, {})
        filemanager.save(json_content, output_path, backend, **kwargs)

    logger.info(f"Materialized {len(results)} items to {output_path}")
    return output_path


@register_materializer("dual", options_type=TabularOptions, requires_arbitrary_files=True)
def _materialize_dual(
    data: List[Any],
    path: str,
    filemanager,
    backends: List[str],
    backend_kwargs: Dict[str, Dict[str, Any]],
    spec: MaterializationSpec,
    context: Any,
    extra_inputs: Dict[str, Any],
) -> str:
    """Materialize data as dual output (CSV + JSON) using typed TabularOptions."""
    # Type guard: runtime check + type narrowing
    options = _expect_options(spec, TabularOptions)

    # Direct attribute access
    fields_opt = options.fields
    summary_fields = options.summary_fields
    analysis_type = options.analysis_type
    include_metadata = options.include_metadata
    strip_roi = options.strip_roi_suffix if hasattr(options, 'strip_roi_suffix') else False

    base_path = _generate_output_path(path, "", "", strip_roi=strip_roi)
    json_path = f"{base_path}.json"
    csv_path = f"{base_path}_details.csv"

    rows = []
    for i, item in enumerate(data or []):
        row = _extract_fields(item, fields_opt)
        if "slice_index" not in row:
            row["slice_index"] = i
        rows.append(row)

    summary_data = []
    for i, item in enumerate(data or []):
        record = _extract_fields(item, summary_fields or fields_opt)
        if "slice_index" not in record:
            record["slice_index"] = i
        summary_data.append(record)

    summary = {
        "total_items": len(summary_data),
        "results": summary_data
    }
    if include_metadata and analysis_type:
        summary["analysis_type"] = analysis_type

    for backend in backends:
        _prepare_output_path(filemanager, backend, json_path)
        kwargs = backend_kwargs.get(backend, {})
        if rows:
            df = pd.DataFrame(rows)
            filemanager.save(df.to_csv(index=False), csv_path, backend, **kwargs)
        filemanager.save(json.dumps(summary, indent=2, default=str), json_path, backend, **kwargs)

    logger.info(f"Materialized {len(rows)} rows (dual format) to {json_path}")
    return json_path


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
    # Type guard: runtime check + type narrowing
    options = _expect_options(spec, TiffStackOptions)

    # Direct attribute access
    normalize_uint8 = options.normalize_uint8
    summary_suffix = options.summary_suffix
    empty_summary = options.empty_summary
    strip_roi = options.strip_roi_suffix
    strip_pkl = options.strip_pkl

    if not data:
        summary_path = _generate_output_path(path, summary_suffix, ".txt", strip_roi=strip_roi, strip_pkl=strip_pkl)
        for backend in backends:
            _prepare_output_path(filemanager, backend, summary_path)
            kwargs = backend_kwargs.get(backend, {})
            filemanager.save(empty_summary, summary_path, backend, **kwargs)
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
    # Type guard: runtime check + type narrowing
    options = _expect_options(spec, ROIOptions)

    # Direct attribute access
    min_area = options.min_area
    extract_contours = options.extract_contours
    roi_suffix = options.roi_suffix
    summary_suffix = options.summary_suffix
    strip_roi = options.strip_roi_suffix
    strip_pkl = options.strip_pkl

    if not data:
        summary_path = _generate_output_path(path, summary_suffix, ".txt", strip_roi=strip_roi, strip_pkl=strip_pkl)
        # Use default empty summary since ROIOptions doesn't have empty_summary field
        summary_content = "No segmentation masks generated (empty data)\n"
        for backend in backends:
            _prepare_output_path(filemanager, backend, summary_path)
            kwargs = backend_kwargs.get(backend, {})
            filemanager.save(summary_content, summary_path, backend, **kwargs)
        return summary_path

    from polystore.roi import extract_rois_from_labeled_mask

    all_rois = []
    for mask in data:
        rois = extract_rois_from_labeled_mask(
            mask,
            min_area=min_area,
            extract_contours=extract_contours
        )
        all_rois.extend(rois)

    base_path = _generate_output_path(path, "", "", strip_roi=strip_roi, strip_pkl=strip_pkl)
    roi_path = f"{base_path}{roi_suffix}"

    if all_rois:
        for backend in backends:
            _prepare_output_path(filemanager, backend, roi_path)
            kwargs = backend_kwargs.get(backend, {})
            filemanager.save(all_rois, roi_path, backend, **kwargs)

    summary_path = f"{base_path}{summary_suffix}"
    summary_content = f"Segmentation ROIs: {len(all_rois)} cells\n"
    summary_content += f"Z-planes: {len(data)}\n"
    if all_rois:
        summary_content += f"ROI file: {roi_path}\n"
    else:
        summary_content += "No ROIs extracted (all regions below min_area threshold)\n"

    for backend in backends:
        _prepare_output_path(filemanager, backend, summary_path)
        kwargs = backend_kwargs.get(backend, {})
        filemanager.save(summary_content, summary_path, backend, **kwargs)

    return summary_path


def _coerce_jsonable(value: Any) -> Any:
    try:
        import numpy as np

        if isinstance(value, np.generic):
            return value.item()
        if isinstance(value, np.ndarray):
            return value.tolist()
    except Exception:
        pass
    return value


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

    # Type guard: runtime check + type narrowing
    options = _expect_options(spec, RegionPropsOptions)

    # Direct attribute access
    analysis_type = options.analysis_type
    min_area = options.min_area
    extract_contours = options.extract_contours
    roi_suffix = options.roi_suffix
    details_suffix = options.details_suffix
    json_suffix = options.json_suffix
    require_intensity = options.require_intensity

    base_properties = list(options.properties or ["label", "area", "perimeter", "centroid", "bbox"])
    intensity_properties = list(options.intensity_properties or ["mean_intensity"])

    # Ensure required properties for filtering + stable schema
    for required in ("label", "area", "centroid", "bbox"):
        if required not in base_properties:
            base_properties.append(required)

    intensity = extra_inputs.get("intensity")
    if intensity is None:
        intensity = extra_inputs.get("intensity_slices")

    def _normalize_slices(obj: Any, *, name: str) -> List[np.ndarray]:
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

    label_slices = _normalize_slices(data, name="labeled_mask")
    intensity_slices = _normalize_slices(intensity, name="intensity") if intensity is not None else []

    if require_intensity and not intensity_slices:
        raise ValueError(
            "regionprops materializer requires intensity input, but none was provided. "
            "Pass extra_inputs['intensity'] (aligned to label slices) or set require_intensity=False."
        )
    if intensity_slices and len(intensity_slices) != len(label_slices):
        raise ValueError(
            f"Intensity/label slice mismatch: intensity={len(intensity_slices)} slices, "
            f"labels={len(label_slices)} slices."
        )

    base_path = _generate_output_path(path, "", "")
    json_path = f"{base_path}{json_suffix}"
    csv_path = f"{base_path}{details_suffix}"
    roi_path = f"{base_path}{roi_suffix}"

    all_rois: List[ROI] = []
    rows: List[Dict[str, Any]] = []
    per_slice: List[Dict[str, Any]] = []

    for z_idx, labels in enumerate(label_slices):
        if labels.ndim != 2:
            raise ValueError(f"Label slice {z_idx} must be 2D, got shape {labels.shape}")
        if not np.issubdtype(labels.dtype, np.integer):
            labels = labels.astype(np.int32)

        intensity_img = None
        if intensity_slices:
            intensity_img = intensity_slices[z_idx]
            if intensity_img.ndim != 2:
                raise ValueError(f"Intensity slice {z_idx} must be 2D, got shape {intensity_img.shape}")
            if intensity_img.shape != labels.shape:
                raise ValueError(
                    f"Intensity slice {z_idx} shape {intensity_img.shape} does not match "
                    f"label slice shape {labels.shape}."
                )

        props = list(dict.fromkeys(base_properties + (intensity_properties if intensity_img is not None else [])))
        table = regionprops_table(
            labels,
            intensity_image=intensity_img,
            properties=props
        )

        # Filter out tiny regions (match ROI extraction behavior)
        areas = table.get("area")
        keep_idx: List[int] = []
        if areas is not None:
            keep_idx = [i for i, a in enumerate(areas) if float(a) >= min_area]
        else:
            keep_idx = list(range(len(table.get("label", []))))

        labels_col = table.get("label", [])
        kept_labels: List[int] = [int(labels_col[i]) for i in keep_idx]

        # Build rows from regionprops_table output
        for i in keep_idx:
            row: Dict[str, Any] = {"slice_index": z_idx}
            for key, values in table.items():
                if values is None:
                    continue
                norm_key = key.replace("-", "_")
                row[norm_key] = _coerce_jsonable(values[i])
            rows.append(row)

        # Per-slice summary
        slice_summary: Dict[str, Any] = {"slice_index": z_idx, "region_count": len(keep_idx)}
        if areas is not None and keep_idx:
            kept_areas = [float(areas[i]) for i in keep_idx]
            slice_summary["total_area"] = float(sum(kept_areas))
            slice_summary["mean_area"] = float(sum(kept_areas) / len(kept_areas))
        if intensity_img is not None:
            mean_int = table.get("mean_intensity")
            if mean_int is not None and keep_idx:
                kept_mean_int = [float(mean_int[i]) for i in keep_idx]
                slice_summary["mean_mean_intensity"] = float(sum(kept_mean_int) / len(kept_mean_int))
        per_slice.append(slice_summary)

        # Extract ROIs and attach slice/intensity metadata
        rois = extract_rois_from_labeled_mask(
            labels,
            min_area=min_area,
            extract_contours=extract_contours,
        )

        intensity_by_label: Dict[int, Dict[str, Any]] = {}
        if intensity_img is not None and kept_labels:
            for i in keep_idx:
                label_id = int(labels_col[i])
                intensity_by_label[label_id] = {
                    k: _coerce_jsonable(table[k][i])
                    for k in intensity_properties
                    if k in table
                }

        for roi in rois:
            label_id = int(roi.metadata.get("label", 0))
            metadata = dict(roi.metadata)
            metadata["slice_index"] = z_idx
            if label_id in intensity_by_label:
                metadata.update(intensity_by_label[label_id])
            all_rois.append(ROI(shapes=roi.shapes, metadata=metadata))

    summary = {
        "analysis_type": analysis_type,
        "total_slices": len(label_slices),
        "total_regions": len(rows),
        "regions_per_slice": per_slice,
        "details_csv": csv_path,
        "roi_zip": roi_path,
        "properties": base_properties,
        "intensity_properties": intensity_properties if intensity_slices else [],
    }

    # JSON summary always (even if empty)
    json_content = json.dumps(summary, indent=2, default=str)
    for backend in backends:
        _prepare_output_path(filemanager, backend, json_path)
        kwargs = backend_kwargs.get(backend, {})
        filemanager.save(json_content, json_path, backend, **kwargs)

    # CSV details if any rows
    if rows:
        df = pd.DataFrame(rows)
        csv_content = df.to_csv(index=False)
        for backend in backends:
            _prepare_output_path(filemanager, backend, csv_path)
            kwargs = backend_kwargs.get(backend, {})
            filemanager.save(csv_content, csv_path, backend, **kwargs)

    # ROI zip if any ROIs
    if all_rois:
        for backend in backends:
            _prepare_output_path(filemanager, backend, roi_path)
            kwargs = backend_kwargs.get(backend, {})
            filemanager.save(all_rois, roi_path, backend, **kwargs)

    return json_path


# ===== Helper functions for array field discovery and expansion =====

def _is_array_field(field: Any, field_value: Any) -> bool:
    """Check if a dataclass field is an array/tuple type.

    Args:
        field: dataclass field object
        field_value: Runtime value of the field

    Returns:
        True if field represents an array/tuple structure
    """
    from typing import get_origin

    # Check type annotation
    origin = hasattr(field.type, '__origin__') and get_origin(field.type)
    if origin in (list, List, tuple, Tuple):
        return True

    # Runtime check for list of tuples
    if isinstance(field_value, list) and len(field_value) > 0:
        first_elem = field_value[0]
        if isinstance(first_elem, (tuple, list)):
            return True

    return False


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

    return [
        f.name
        for f in fields(item)
        if _is_array_field(f, getattr(item, f.name, None))
    ]


def _discover_column_mapping(
    field_name: str,
    array_data: List[Any],
    existing_mapping: Dict[str, str]
) -> Dict[str, str]:
    """Auto-discover column mapping for array expansion.

    Args:
        field_name: Name of the field being expanded
        array_data: Array data to expand
        existing_mapping: User-provided mapping (takes precedence)

    Returns:
        Dict mapping string indices to column names
    """
    if existing_mapping:
        return existing_mapping

    if not array_data:
        return {}

    first_elem = array_data[0]
    if not isinstance(first_elem, (tuple, list)):
        return {}

    # Auto-generate: field_name_0, field_name_1, ...
    return {
        str(i): f"{field_name}_{i}"
        for i in range(len(first_elem))
    }


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

    rows = []
    for element in array_data:
        row = dict(base_row)
        for idx_str, col_name in row_columns.items():
            try:
                idx = int(idx_str)
                row[col_name] = element[idx]
            except (ValueError, IndexError, TypeError) as e:
                logger.warning(
                    f"Failed to extract index {idx_str}: {e}. "
                    f"element type: {type(element)}"
                )
        rows.append(row)

    return rows


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
    from openhcs.processing.materialization.options import BuiltinAggregations

    # Type guard: runtime check + type narrowing
    options = _expect_options(spec, ArrayExpansionOptions)

    # Get configuration
    fields_opt = options.fields
    summary_fields = options.summary_fields or options.fields
    analysis_type = options.analysis_type
    include_metadata = options.include_metadata
    strip_roi = options.strip_roi_suffix if hasattr(options, 'strip_roi_suffix') else False

    # Generate output paths
    filename_suffix = getattr(options, 'filename_suffix', '.json')
    strip_pkl = options.strip_pkl if hasattr(options, 'strip_pkl') else True
    base_path = _generate_output_path(path, "", "", strip_roi=strip_roi, strip_pkl=strip_pkl)
    json_path = f"{base_path}{filename_suffix}"
    csv_path = f"{base_path}_details.csv"

    # Build rows using array expansion
    rows = []
    for item_idx, item in enumerate(data or []):
        # Extract base fields from item
        base_row = _extract_fields(item, fields_opt)
        if "slice_index" not in base_row and "slice_index" not in (fields_opt or []):
            base_row["slice_index"] = item_idx

        # STRATEGY DISPATCH: Choose expansion strategy
        if options.row_unpacker:
            # Strategy 1: Custom unpacker (user takes full control)
            expanded_rows = options.row_unpacker(item)
            for exp_row in expanded_rows:
                exp_row.update(base_row)
                rows.append(exp_row)
            continue

        if options.row_field:
            # Strategy 2: User-specified field (explicit mode)
            array_data = getattr(item, options.row_field, [])
            row_columns = _discover_column_mapping(
                options.row_field, array_data, options.row_columns
            )
            expanded = _expand_array_field(array_data, base_row, row_columns)
            rows.extend(expanded)
            continue

        # Strategy 3: Auto-discovery (implicit mode)
        array_fields = _discover_array_fields(item)
        if not array_fields:
            rows.append(base_row)
            continue

        # Expand primary array field
        primary_field = array_fields[0]
        array_data = getattr(item, primary_field, [])
        row_columns = _discover_column_mapping(primary_field, array_data, {})
        expanded = _expand_array_field(array_data, base_row, row_columns)
        rows.extend(expanded)

    # Build summary with aggregations
    summary = _build_summary_from_data(
        data or [],
        summary_fields or fields_opt,
        options.aggregations,
        analysis_type,
        include_metadata
    )

    # Ensure total_items is in summary
    if "total_items" not in summary:
        summary["total_items"] = len(data or [])

    # Save JSON summary
    json_content = json.dumps(summary, indent=2, default=str)
    for backend in backends:
        _prepare_output_path(filemanager, backend, json_path)
        kwargs = backend_kwargs.get(backend, {})
        filemanager.save(json_content, json_path, backend, **kwargs)

    # Save CSV details
    if rows:
        df = pd.DataFrame(rows)
        csv_content = df.to_csv(index=False)
        for backend in backends:
            _prepare_output_path(filemanager, backend, csv_path)
            kwargs = backend_kwargs.get(backend, {})
            filemanager.save(csv_content, csv_path, backend, **kwargs)

    logger.info(f"Materialized {len(rows)} rows (tabular with arrays) to {json_path}")
    return json_path


def _discover_aggregations(data: List[Any]) -> Dict[str, str]:
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


def _apply_builtin_aggregation(
    data: List[Any],
    field_names: Optional[List[str]],
    agg_name: str,
    agg_func: Callable
) -> Optional[Any]:
    """Apply a built-in aggregation function to data.

    Args:
        data: List of data items
        field_names: Fields to extract from each item
        agg_name: Name of the aggregation (for logging)
        agg_func: Aggregation function to apply

    Returns:
        Aggregated value or None if failed
    """
    values = []
    for item in data:
        extracted = _extract_fields(item, field_names) if field_names else {"value": item}
        if len(extracted) == 1:
            values.append(list(extracted.values())[0])
        else:
            logger.warning(
                f"Built-in aggregation '{agg_name}' requires single field, "
                f"got {len(extracted)} fields. Skipping."
            )
            return None

    if not values:
        return None

    try:
        return agg_func(values)
    except Exception as e:
        logger.warning(f"Aggregation '{agg_name}' failed: {e}")
        return None


def _build_summary_from_data(
    data: List[Any],
    field_names: Optional[List[str]],
    aggregations: Dict[str, Union[str, Callable[[List[Any]], Any]]],
    analysis_type: Optional[str],
    include_metadata: bool
) -> Dict[str, Any]:
    """
    Build summary dict from data using aggregation specifications.

    Args:
        data: List of data items
        field_names: Fields to extract from each item
        aggregations: Dict mapping result keys to aggregation specs
        analysis_type: Type identifier for the analysis
        include_metadata: Whether to include metadata

    Returns:
        Summary dict with aggregated values
    """
    summary = {}

    if include_metadata and analysis_type:
        summary["analysis_type"] = analysis_type

    # Auto-discover aggregations if not provided
    if not aggregations:
        aggregations = _discover_aggregations(data)

    if not aggregations:
        return summary

    # Apply each aggregation
    for key, agg_spec in aggregations.items():
        if isinstance(agg_spec, str):
            # Built-in aggregation
            agg_func = BuiltinAggregations.get(agg_spec)
            if agg_func is None:
                logger.warning(f"Unknown aggregation '{agg_spec}', skipping")
                continue

            result = _apply_builtin_aggregation(data, field_names, agg_spec, agg_func)
            summary[key] = result

        elif callable(agg_spec):
            # Custom aggregation function
            try:
                result = agg_spec(data)
                summary[key] = result
            except Exception as e:
                logger.warning(f"Custom aggregation failed: {e}")
                summary[key] = None
        else:
            logger.warning(f"Invalid aggregation spec: {agg_spec}")

    return summary
