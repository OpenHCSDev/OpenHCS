"""
Core materialization framework.

Provides a single spec + registry + dispatcher abstraction for analysis materialization.
Uses generic ABC-based handlers to eliminate duplication.
"""

from __future__ import annotations

import json
import logging
from abc import ABC, abstractmethod
from dataclasses import dataclass, fields, is_dataclass
from pathlib import Path
from typing import Any, Callable, Dict, Generic, List, Optional, Sequence, Tuple, TypeVar, Union

from openhcs.constants.constants import Backend

# Type variables for generic MaterializationSpec
T = TypeVar('T', bound=object)
U = TypeVar('U', bound=object)

logger = logging.getLogger(__name__)

# Import typed options for handler type narrowing
from openhcs.processing.materialization.options import (
    TabularOptions,
    ArrayExpansionOptions,
    FileOutputOptions,
    ROIOptions,
    RegionPropsOptions,
    TiffStackOptions,
    BuiltinAggregations,
)


# ===== Generic Abstractions =====

class MaterializationHandler(ABC, Generic[T]):
    """ABC defining the materialization contract.

    Handlers implement domain-specific logic while framework handles:
    - Backend iteration (via context)
    - Path generation (via context)
    - Common data extraction patterns

    This eliminates duplication across all handlers.
    """

    @abstractmethod
    def process_data(self, data: Any, context: MaterializationContext) -> T:
        """Process input data into domain-specific format."""
        pass

    @abstractmethod
    def get_output_paths(self, context: MaterializationContext, result: T) -> List[Tuple[str, Any]]:
        """Get (path, content) tuples for output files."""
        pass


@dataclass
class MaterializationContext:
    """Shared context for materialization handlers.

    Consolidates common configuration and path logic.
    """
    base_path: str
    backends: List[str]
    backend_kwargs: Dict[str, Dict[str, Any]]
    options: Any
    filemanager: Any

    def get_paths(self) -> 'PathHelper':
        """Get path helper for this context."""
        return PathHelper(self.base_path, self.options)

    def get_saver(self) -> 'BackendSaver':
        """Get backend saver for this context."""
        return BackendSaver(self.backends, self.filemanager, self.backend_kwargs)


class PathHelper:
    """Unified path generation for materialization.

    Eliminates repeated path construction logic.
    """

    def __init__(self, base_path: str, options: Any):
        self.base_path = self._strip_path(base_path, options)
        self.parent = self.base_path.parent
        self.name = self.base_path.name

    @staticmethod
    def _strip_path(path: str, options: Any) -> Path:
        """Strip known suffixes from path."""
        p = Path(path)
        name = p.name

        # Strip compound suffixes
        if name.endswith(".roi.zip"):
            name = name[: -len(".roi.zip")]

        # Strip based on options
        strip_pkl = getattr(options, 'strip_pkl', True)
        strip_roi = getattr(options, 'strip_roi_suffix', False)
        if strip_pkl and name.endswith(".pkl"):
            name = name[: -len(".pkl")]
        if strip_roi and name.endswith(".roi"):
            name = name[: -len(".roi")]

        return p.with_name(name)

    def with_suffix(self, suffix: str) -> str:
        """Add a suffix to the base path."""
        return str(self.parent / f"{self.name}{suffix}")


class BackendSaver:
    """Centralized multi-backend save pattern.

    Eliminates repeated backend iteration boilerplate.
    """

    def __init__(self, backends: List[str], filemanager, backend_kwargs: Dict[str, Dict[str, Any]]):
        self.backends = backends
        self.filemanager = filemanager
        self.backend_kwargs = backend_kwargs or {}

    def save(self, content, path: str) -> None:
        """Save content to path across all backends."""
        for backend in self.backends:
            self._prepare_path(backend, path)
            kwargs = self.backend_kwargs.get(backend, {})
            self.filemanager.save(content, path, backend, **kwargs)

    def save_if(self, condition: bool, content, path: str) -> None:
        """Save content if condition is True."""
        if condition:
            self.save(content, path)

    def _prepare_path(self, backend: str, path: str) -> None:
        """Prepare output path for save."""
        backend_instance = self.filemanager._get_backend(backend)
        if backend_instance.requires_filesystem_validation:
            self.filemanager.ensure_directory(str(Path(path).parent), backend)
            if self.filemanager.exists(path, backend):
                self.filemanager.delete(path, backend)


# ===== Materialization Spec =====

@dataclass(frozen=True)
class MaterializationSpec(Generic[T]):
    """
    Declarative materialization spec with type-safe options.

    Type Parameters:
        T: The type of options (e.g., TabularOptions, ArrayExpansionOptions, etc.)

    Attributes:
        options: Optional typed handler-specific options (validated at construction).
        handler: Optional handler name. If not specified, automatically inferred from options type.
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


# ===== Materialization Registry =====

@dataclass(frozen=True)
class MaterializationHandler:
    """Registered materialization handler.

    Attributes:
        name: Handler name (used in MaterializationSpec.handler)
        func: Handler function (signature depends on handler type)
        requires_arbitrary_files: Whether this handler requires arbitrary file support
        options_type: Expected options dataclass type for validation
    """
    name: str
    func: Callable
    requires_arbitrary_files: bool
    options_type: Optional[type] = None


class MaterializationRegistry:
    """Registry for materialization handlers with type tracking."""

    _handlers: Dict[str, MaterializationHandler] = {}
    _option_types: Dict[str, type] = {}
    _options_to_handler: Dict[type, str] = {}

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


# ===== Decorator =====

def register_materializer(
    name: str,
    *,
    options_type: Optional[type] = None,
    requires_arbitrary_files: bool = True
):
    """Decorator to register a materialization handler.

    Args:
        name: Handler name (used in MaterializationSpec.handler)
        options_type: Expected options dataclass type for validation
        requires_arbitrary_files: Whether this handler requires arbitrary file support

    Usage:
        @register_materializer("csv", options_type=TabularOptions)
        def materialize_csv(data, path, filemanager, backends, backend_kwargs, spec, context, extra_inputs):
            ...
    """
    def decorator(func: Callable[..., str]) -> Callable[..., str]:
        MaterializationRegistry.register(
            name,
            func,
            options_type=options_type,
            requires_arbitrary_files=requires_arbitrary_files,
        )

        # Set __materialization_handler__ attribute for type checking
        func.__materialization_handler__ = name
        return func

    return decorator


# ===== Generic Orchestrator =====

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
    """Generic materialization using registry-based handlers.

    Orchestrates the materialization flow:
    1. Create context with paths and configuration
    2. Process data through handler
    3. Build and save outputs to backends

    This provides backward compatibility while leveraging ABC-based abstractions internally.
    """
    handler_name = spec.handler or "custom"

    handler = MaterializationRegistry.get(handler_name)
    normalized_backends = _normalize_backends(backends)
    _validate_backends(spec, handler, normalized_backends, filemanager)

    # Call the legacy handler function
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


def _normalize_backends(backends: Sequence[str] | str) -> List[str]:
    """Normalize backend input to list."""
    if isinstance(backends, str):
        return [backends]
    return list(backends)


def _validate_backends(
    spec: MaterializationSpec,
    handler: MaterializationHandler,
    backends: List[str],
    filemanager,
):
    """Validate backend configuration against spec and handler requirements."""
    if spec.allowed_backends:
        invalid = [b for b in backends if b not in spec.allowed_backends]
        if invalid:
            raise ValueError(
                f"Backend(s) {invalid} not in allowed backends for this spec: {spec.allowed_backends}"
            )

    if handler.requires_arbitrary_files:
        # Validate that all backends support arbitrary file paths
        for backend in backends:
            backend_instance = filemanager._get_backend(backend)
            if not backend_instance.supports_arbitrary_files:
                raise ValueError(
                    f"Handler '{handler.name}' requires arbitrary file support, "
                    f"but backend '{backend}' does not support it."
                )


# ===== Helper Functions =====

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
                return {f: item[f].tolist() for f in field_names if f in item.columns}
            return {col: item[col].tolist() for col in item.columns}

        if isinstance(item, pd.Series):
            if field_names:
                return {f: item[f] for f in field_names if f in item.index}
            return item.to_dict()
    except ImportError:
        pass

    # Handle dataclasses
    if is_dataclass(item):
        if field_names:
            return {f: getattr(item, f, None) for f in field_names if hasattr(item, f)}
        return {f.name: getattr(item, f.name) for f in fields(item)}
    if isinstance(item, dict):
        if field_names:
            return {f: item.get(f) for f in field_names if f in item}
        return item
    return {"value": item}


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


# ===== Handler Implementations =====

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
    """Unified tabular materializer for CSV, JSON, or dual output."""
    options = spec.options
    saver = BackendSaver(backends, filemanager, backend_kwargs)
    paths = PathHelper(path, options)

    # Determine output format
    format_name = spec.handler if spec.handler in ("csv", "json", "dual") else options.output_format

    # Generate output paths
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
        import pandas as pd
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
    options = spec.options
    saver = BackendSaver(backends, filemanager, backend_kwargs)
    paths = PathHelper(path, options)

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

    options = spec.options
    saver = BackendSaver(backends, filemanager, backend_kwargs)
    paths = PathHelper(path, options)

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
    """Materialize region properties from labeled masks."""
    import numpy as np
    from skimage.measure import regionprops_table
    from polystore.roi import ROI, extract_rois_from_labeled_mask

    options = spec.options
    saver = BackendSaver(backends, filemanager, backend_kwargs)
    paths = PathHelper(path, options)

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
        import pandas as pd
        saver.save(pd.DataFrame(rows).to_csv(index=False), csv_path)
    if all_rois:
        saver.save(all_rois, roi_path)

    return json_path


def _normalize_slices(obj: Any, *, name: str) -> List[np.ndarray]:
    """Normalize input to list of 2D arrays."""
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
    """Generic handler for tabular output with array expansion."""
    options = spec.options
    saver = BackendSaver(backends, filemanager, backend_kwargs)
    paths = PathHelper(path, options)

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
        import pandas as pd
        saver.save(pd.DataFrame(rows).to_csv(index=False), csv_path)
    logger.info(f"Materialized {len(rows)} rows to {json_path}")
    return json_path


def _discover_array_fields(item: Any) -> List[str]:
    """Discover all array/tuple fields in a dataclass."""
    if not hasattr(item, '__dataclass_fields__'):
        return []

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
    """Expand an array field into multiple rows."""
    if not array_data:
        return [base_row]

    return [
        {
            **base_row,
            **{col: elem[int(idx)] for idx, col in row_columns.items() if isinstance(elem, (list, tuple)) and int(idx) < len(elem)}
        }
        for elem in array_data
    ]


def _build_summary_from_data(
    data: List[Any],
    field_names: Optional[List[str]],
    aggregations: Dict[str, Union[str, Callable[[List[Any]], Any]]],
    include_metadata: bool
) -> Dict[str, Any]:
    """Build summary dict from data using aggregation specifications."""
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


def _discover_aggregations(data: List[Any]) -> Dict[str, Union[str, Callable]]:
    """Auto-discover aggregations based on dataclass field types."""
    if not data or not hasattr(data[0], '__dataclass_fields__'):
        return {}

    from dataclasses import fields as get_fields

    aggregations = {}
    for f in get_fields(data[0]):
        field_type = f.type

        # Extract Optional[T]
        if hasattr(field_type, '__origin__') and field_type.__origin__ is Union:
            args = getattr(field_type, '__args__', ())
            if len(args) == 2 and type(None) in args:
                field_type = args[0] if args[1] is type(None) else args[1]

        # Check for numeric types
        if field_type in (int, float):
            aggregations[f.name] = "sum"
        elif hasattr(field_type, '__origin__') and field_type.__origin__ in (list, List):
            aggregations[f.name] = "len"

    return aggregations
