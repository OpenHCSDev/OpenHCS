"""
Core materialization framework.

Provides a single spec + registry + dispatcher abstraction for analysis materialization.
"""

from __future__ import annotations

import json
import logging
from dataclasses import dataclass, field, fields, is_dataclass
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence

import pandas as pd

from openhcs.constants.constants import Backend

logger = logging.getLogger(__name__)


@dataclass(frozen=True)
class MaterializationSpec:
    """
    Declarative materialization spec.

    handler: Registered handler name in MaterializationRegistry.
    options: Handler-specific options (serializable).
    allowed_backends: Optional allowlist of backend names.
    """
    handler: str
    options: Dict[str, Any] = field(default_factory=dict)
    allowed_backends: Optional[List[str]] = None


@dataclass(frozen=True)
class MaterializationHandler:
    name: str
    func: Callable[..., str]
    requires_arbitrary_files: bool = True


class MaterializationRegistry:
    _handlers: Dict[str, MaterializationHandler] = {}

    @classmethod
    def register(
        cls,
        name: str,
        func: Callable[..., str],
        *,
        requires_arbitrary_files: bool = True
    ) -> None:
        if name in cls._handlers:
            raise ValueError(f"Materialization handler already registered: {name}")
        cls._handlers[name] = MaterializationHandler(
            name=name,
            func=func,
            requires_arbitrary_files=requires_arbitrary_files
        )

    @classmethod
    def get(cls, name: str) -> MaterializationHandler:
        if name not in cls._handlers:
            raise KeyError(f"Unknown materialization handler: {name}")
        return cls._handlers[name]


def register_materializer(
    name: str,
    *,
    requires_arbitrary_files: bool = True
) -> Callable[[Callable[..., str]], Callable[..., str]]:
    def decorator(func: Callable[..., str]) -> Callable[..., str]:
        MaterializationRegistry.register(
            name,
            func,
            requires_arbitrary_files=requires_arbitrary_files
        )
        func.__materialization_handler__ = name
        return func
    return decorator


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

@register_materializer("csv", requires_arbitrary_files=True)
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
    options = spec.options
    fields_opt = options.get("fields")
    filename_suffix = options.get("filename_suffix", ".csv")
    strip_roi = options.get("strip_roi_suffix", False)
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


@register_materializer("json", requires_arbitrary_files=True)
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
    options = spec.options
    fields_opt = options.get("fields")
    filename_suffix = options.get("filename_suffix", ".json")
    analysis_type = options.get("analysis_type")
    include_metadata = options.get("include_metadata", True)
    strip_roi = options.get("strip_roi_suffix", False)
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


@register_materializer("dual", requires_arbitrary_files=True)
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
    options = spec.options
    fields_opt = options.get("fields")
    summary_fields = options.get("summary_fields")
    analysis_type = options.get("analysis_type")
    include_metadata = options.get("include_metadata", True)
    strip_roi = options.get("strip_roi_suffix", False)
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


@register_materializer("tiff_stack", requires_arbitrary_files=True)
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
    options = spec.options
    normalize_uint8 = options.get("normalize_uint8", False)
    summary_suffix = options.get("summary_suffix", "_summary.txt")
    strip_roi = options.get("strip_roi_suffix", False)

    if not data:
        summary_path = _generate_output_path(path, summary_suffix, ".txt", strip_roi=strip_roi)
        summary_content = options.get(
            "empty_summary",
            "No images generated (empty data)\n"
        )
        for backend in backends:
            _prepare_output_path(filemanager, backend, summary_path)
            kwargs = backend_kwargs.get(backend, {})
            filemanager.save(summary_content, summary_path, backend, **kwargs)
        return summary_path

    base_path = _generate_output_path(path, "", "", strip_roi=strip_roi)
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


@register_materializer("roi_zip", requires_arbitrary_files=True)
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
    options = spec.options
    min_area = options.get("min_area", 10)
    extract_contours = options.get("extract_contours", True)
    roi_suffix = options.get("roi_suffix", "_rois.roi.zip")
    summary_suffix = options.get("summary_suffix", "_segmentation_summary.txt")
    strip_roi = options.get("strip_roi_suffix", False)

    if not data:
        summary_path = _generate_output_path(path, summary_suffix, ".txt", strip_roi=strip_roi)
        summary_content = options.get(
            "empty_summary",
            "No segmentation masks generated (empty data)\n"
        )
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

    base_path = _generate_output_path(path, "", "", strip_roi=strip_roi)
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


@register_materializer("regionprops", requires_arbitrary_files=True)
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

    options = spec.options
    analysis_type = options.get("analysis_type", "regionprops")
    min_area = int(options.get("min_area", 10))
    extract_contours = bool(options.get("extract_contours", True))
    roi_suffix = options.get("roi_suffix", "_rois.roi.zip")
    details_suffix = options.get("details_suffix", "_details.csv")
    json_suffix = options.get("json_suffix", ".json")
    require_intensity = bool(options.get("require_intensity", False))

    base_properties = list(options.get("properties") or ["label", "area", "perimeter", "centroid", "bbox"])
    intensity_properties = list(options.get("intensity_properties") or ["mean_intensity"])

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


def _get_result_attr(obj: Any, name: str, default: Any = None) -> Any:
    if isinstance(obj, dict):
        return obj.get(name, default)
    return getattr(obj, name, default)


@register_materializer("cell_counts", requires_arbitrary_files=True)
def _materialize_cell_counts(
    data: List[Any],
    path: str,
    filemanager,
    backends: List[str],
    backend_kwargs: Dict[str, Dict[str, Any]],
    spec: MaterializationSpec,
    context: Any,
    extra_inputs: Dict[str, Any],
) -> str:
    if not data:
        logger.warning("CELL_COUNT materializer called with empty data")
        return path

    options = spec.options
    strip_roi = options.get("strip_roi_suffix", False)
    base_path = _generate_output_path(path, "", "", strip_roi=strip_roi)
    json_path = f"{base_path}.json"
    csv_path = f"{base_path}_details.csv"

    is_multi_channel = _get_result_attr(data[0], "chan_1_results") is not None

    if is_multi_channel:
        summary, rows = _build_cell_counts_multi_summary(data)
    else:
        summary, rows = _build_cell_counts_single_summary(data)

    json_content = json.dumps(summary, indent=2, default=str)

    for backend in backends:
        _prepare_output_path(filemanager, backend, json_path)
        _prepare_output_path(filemanager, backend, csv_path)
        kwargs = backend_kwargs.get(backend, {})
        filemanager.save(json_content, json_path, backend, **kwargs)
        if rows:
            df = pd.DataFrame(rows)
            filemanager.save(df.to_csv(index=False), csv_path, backend, **kwargs)

    return json_path


def _build_cell_counts_single_summary(data: List[Any]) -> tuple[Dict[str, Any], List[Dict[str, Any]]]:
    summary = {
        "analysis_type": "single_channel_cell_counting",
        "total_slices": len(data),
        "results_per_slice": []
    }
    rows: List[Dict[str, Any]] = []

    total_cells = 0
    for result in data:
        slice_index = _get_result_attr(result, "slice_index")
        method = _get_result_attr(result, "method")
        cell_count = _get_result_attr(result, "cell_count", 0)
        cell_positions = _get_result_attr(result, "cell_positions", []) or []
        cell_areas = _get_result_attr(result, "cell_areas", []) or []
        cell_intensities = _get_result_attr(result, "cell_intensities", []) or []
        detection_confidence = _get_result_attr(result, "detection_confidence", []) or []
        parameters_used = _get_result_attr(result, "parameters_used", {}) or {}

        total_cells += cell_count
        summary["results_per_slice"].append({
            "slice_index": slice_index,
            "method": method,
            "cell_count": cell_count,
            "avg_cell_area": float(sum(cell_areas) / len(cell_areas)) if cell_areas else 0,
            "avg_cell_intensity": float(sum(cell_intensities) / len(cell_intensities)) if cell_intensities else 0,
            "parameters": parameters_used
        })

        for i, (pos, area, intensity, confidence) in enumerate(zip(
            cell_positions, cell_areas, cell_intensities, detection_confidence
        )):
            rows.append({
                "slice_index": slice_index,
                "cell_id": f"slice_{slice_index}_cell_{i}",
                "x_position": pos[0],
                "y_position": pos[1],
                "cell_area": area,
                "cell_intensity": intensity,
                "detection_confidence": confidence,
                "detection_method": method
            })

    summary["total_cells_all_slices"] = total_cells
    summary["average_cells_per_slice"] = total_cells / len(data) if data else 0
    return summary, rows


def _build_cell_counts_multi_summary(data: List[Any]) -> tuple[Dict[str, Any], List[Dict[str, Any]]]:
    summary = {
        "analysis_type": "multi_channel_cell_counting_colocalization",
        "total_slices": len(data),
        "colocalization_summary": {
            "total_chan_1_cells": 0,
            "total_chan_2_cells": 0,
            "total_colocalized": 0,
            "average_colocalization_percentage": 0
        },
        "results_per_slice": []
    }
    rows: List[Dict[str, Any]] = []

    total_coloc_pct = 0
    for result in data:
        chan_1 = _get_result_attr(result, "chan_1_results")
        chan_2 = _get_result_attr(result, "chan_2_results")
        colocalized_count = _get_result_attr(result, "colocalized_count", 0)
        colocalization_percentage = _get_result_attr(result, "colocalization_percentage", 0)
        chan_1_only = _get_result_attr(result, "chan_1_only_count", 0)
        chan_2_only = _get_result_attr(result, "chan_2_only_count", 0)
        colocalization_method = _get_result_attr(result, "colocalization_method")
        colocalization_metrics = _get_result_attr(result, "colocalization_metrics", {}) or {}
        overlap_positions = _get_result_attr(result, "overlap_positions", []) or []
        slice_index = _get_result_attr(result, "slice_index")

        summary["colocalization_summary"]["total_chan_1_cells"] += _get_result_attr(chan_1, "cell_count", 0)
        summary["colocalization_summary"]["total_chan_2_cells"] += _get_result_attr(chan_2, "cell_count", 0)
        summary["colocalization_summary"]["total_colocalized"] += colocalized_count
        total_coloc_pct += colocalization_percentage

        summary["results_per_slice"].append({
            "slice_index": slice_index,
            "chan_1_count": _get_result_attr(chan_1, "cell_count", 0),
            "chan_2_count": _get_result_attr(chan_2, "cell_count", 0),
            "colocalized_count": colocalized_count,
            "colocalization_percentage": colocalization_percentage,
            "chan_1_only": chan_1_only,
            "chan_2_only": chan_2_only,
            "colocalization_method": colocalization_method,
            "colocalization_metrics": colocalization_metrics
        })

        for i, pos in enumerate(overlap_positions):
            rows.append({
                "slice_index": slice_index,
                "colocalization_id": f"slice_{slice_index}_coloc_{i}",
                "x_position": pos[0],
                "y_position": pos[1],
                "colocalization_method": colocalization_method
            })

    summary["colocalization_summary"]["average_colocalization_percentage"] = (
        total_coloc_pct / len(data) if data else 0
    )
    return summary, rows


# Convenience factory functions (return specs, not callables)

def csv_materializer(
    fields: Optional[List[str]] = None,
    filename_suffix: str = ".csv",
    analysis_type: Optional[str] = None,
    include_metadata: bool = True,
    strip_roi_suffix: bool = False
) -> MaterializationSpec:
    return MaterializationSpec(
        handler="csv",
        options={
            "fields": fields,
            "filename_suffix": filename_suffix,
            "analysis_type": analysis_type,
            "include_metadata": include_metadata,
            "strip_roi_suffix": strip_roi_suffix
        }
    )


def json_materializer(
    fields: Optional[List[str]] = None,
    filename_suffix: str = ".json",
    analysis_type: Optional[str] = None,
    include_metadata: bool = True,
    strip_roi_suffix: bool = False
) -> MaterializationSpec:
    return MaterializationSpec(
        handler="json",
        options={
            "fields": fields,
            "filename_suffix": filename_suffix,
            "analysis_type": analysis_type,
            "include_metadata": include_metadata,
            "strip_roi_suffix": strip_roi_suffix
        }
    )


def dual_materializer(
    fields: Optional[List[str]] = None,
    summary_fields: Optional[List[str]] = None,
    analysis_type: Optional[str] = None,
    include_metadata: bool = True,
    strip_roi_suffix: bool = False
) -> MaterializationSpec:
    return MaterializationSpec(
        handler="dual",
        options={
            "fields": fields,
            "summary_fields": summary_fields,
            "analysis_type": analysis_type,
            "include_metadata": include_metadata,
            "strip_roi_suffix": strip_roi_suffix
        }
    )


def materializer_spec(
    handler: str,
    *,
    options: Optional[Dict[str, Any]] = None,
    allowed_backends: Optional[List[str]] = None
) -> MaterializationSpec:
    return MaterializationSpec(
        handler=handler,
        options=options or {},
        allowed_backends=allowed_backends
    )


def roi_zip_materializer(
    *,
    min_area: int = 10,
    extract_contours: bool = True,
    roi_suffix: str = "_rois.roi.zip",
    summary_suffix: str = "_segmentation_summary.txt",
    strip_roi_suffix: bool = False
) -> MaterializationSpec:
    return MaterializationSpec(
        handler="roi_zip",
        options={
            "min_area": min_area,
            "extract_contours": extract_contours,
            "roi_suffix": roi_suffix,
            "summary_suffix": summary_suffix,
            "strip_roi_suffix": strip_roi_suffix
        }
    )


def regionprops_materializer(
    *,
    min_area: int = 10,
    extract_contours: bool = True,
    roi_suffix: str = "_rois.roi.zip",
    details_suffix: str = "_details.csv",
    json_suffix: str = ".json",
    analysis_type: str = "regionprops",
    properties: Optional[List[str]] = None,
    intensity_properties: Optional[List[str]] = None,
    require_intensity: bool = False,
    intensity_source: str | None = "step_output",
    intensity_group_by: str | None = None,
) -> MaterializationSpec:
    inputs: Dict[str, Any] = {}
    if intensity_source is not None:
        inputs["intensity"] = {
            "kind": "image_slices",
            "source": intensity_source,
            "group_by": intensity_group_by,
        }
    return MaterializationSpec(
        handler="regionprops",
        options={
            "min_area": min_area,
            "extract_contours": extract_contours,
            "roi_suffix": roi_suffix,
            "details_suffix": details_suffix,
            "json_suffix": json_suffix,
            "analysis_type": analysis_type,
            "properties": properties,
            "intensity_properties": intensity_properties,
            "require_intensity": require_intensity,
            "inputs": inputs,
        },
    )


def tiff_stack_materializer(
    *,
    normalize_uint8: bool = False,
    summary_suffix: str = "_summary.txt",
    empty_summary: str = "No images generated (empty data)\n",
    strip_roi_suffix: bool = False
) -> MaterializationSpec:
    return MaterializationSpec(
        handler="tiff_stack",
        options={
            "normalize_uint8": normalize_uint8,
            "summary_suffix": summary_suffix,
            "empty_summary": empty_summary,
            "strip_roi_suffix": strip_roi_suffix
        }
    )
