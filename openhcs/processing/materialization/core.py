"""
Core materialization framework.

Provides the abstraction layer for converting analysis data to disk formats.
"""

import json
import logging
from dataclasses import dataclass, fields, is_dataclass
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence, Union

import pandas as pd

from openhcs.constants.constants import Backend

logger = logging.getLogger(__name__)


@dataclass(frozen=True)
class MaterializationSpec:
    """
    Declarative specification for materializing analysis outputs.
    
    Attributes:
        format: Output format ('csv', 'json', 'dual')
        filename_suffix: Suffix to append to base path (e.g., '_counts.csv')
        fields: List of field names to extract from dataclass/dict results.
                If None, extracts all fields.
        summary_fields: For 'dual' format, fields to include in JSON summary
        flatten_lists: If True, expand list fields into separate rows
        include_metadata: If True, add processing metadata to output
    """
    format: str  # 'csv', 'json', 'dual'
    filename_suffix: str = ""
    fields: Optional[List[str]] = None
    summary_fields: Optional[List[str]] = None
    flatten_lists: bool = True
    include_metadata: bool = True
    

def _extract_fields(item: Any, field_names: Optional[List[str]] = None) -> Dict[str, Any]:
    """Extract fields from dataclass or dict."""
    if is_dataclass(item):
        if field_names:
            return {f: getattr(item, f, None) for f in field_names if hasattr(item, f)}
        return {f.name: getattr(item, f.name) for f in fields(item)}
    elif isinstance(item, dict):
        if field_names:
            return {f: item.get(f) for f in field_names if f in item}
        return item
    else:
        return {"value": item}


def _generate_output_path(base_path: str, suffix: str, default_ext: str) -> str:
    """Generate output path with proper suffix handling."""
    # Strip common extensions
    path = Path(base_path)
    stem = path.stem
    if stem.endswith('.pkl'):
        stem = stem[:-4]
    if stem.endswith('.roi'):
        stem = stem[:-4]
    
    parent = path.parent
    
    if suffix:
        return str(parent / f"{stem}{suffix}")
    return str(parent / f"{stem}{default_ext}")


def create_materializer(spec: MaterializationSpec) -> Callable:
    """
    Factory that creates a materialization function from a spec.
    
    Returns a function with signature:
        (data: List[T], path: str, filemanager, backend: str) -> str
    
    This signature matches what @special_outputs expects.
    """
    
    def materializer(
        data: List[Any],
        path: str,
        filemanager,
        backend: Union[str, List[str]],
        backend_kwargs: Optional[Dict] = None
    ) -> str:
        """Generated materializer function."""
        if not data:
            logger.warning(f"Materializer called with empty data for {path}")
            return path
        
        # Normalize backend to list
        backends = [backend] if isinstance(backend, str) else backend
        backend_kwargs = backend_kwargs or {}
        
        if spec.format == 'csv':
            return _materialize_csv(data, path, filemanager, backends, backend_kwargs, spec)
        elif spec.format == 'json':
            return _materialize_json(data, path, filemanager, backends, backend_kwargs, spec)
        elif spec.format == 'dual':
            return _materialize_dual(data, path, filemanager, backends, backend_kwargs, spec)
        else:
            raise ValueError(f"Unknown materialization format: {spec.format}")
    
    return materializer


def _materialize_csv(
    data: List[Any],
    path: str,
    filemanager,
    backends: List[str],
    backend_kwargs: Dict,
    spec: MaterializationSpec
) -> str:
    """Materialize data as CSV."""
    output_path = _generate_output_path(path, spec.filename_suffix, ".csv")
    
    rows = []
    for i, item in enumerate(data):
        row = _extract_fields(item, spec.fields)
        if 'slice_index' not in row:
            row['slice_index'] = i
        rows.append(row)
    
    if rows:
        df = pd.DataFrame(rows)
        csv_content = df.to_csv(index=False)
        
        for backend in backends:
            if backend == Backend.DISK.value:
                filemanager.ensure_directory(str(Path(output_path).parent), backend)
            kwargs = backend_kwargs.get(backend, {})
            filemanager.save(csv_content, output_path, backend, **kwargs)
    
    logger.info(f"Materialized {len(rows)} rows to {output_path}")
    return output_path


def _materialize_json(
    data: List[Any],
    path: str,
    filemanager,
    backends: List[str],
    backend_kwargs: Dict,
    spec: MaterializationSpec
) -> str:
    """Materialize data as JSON."""
    output_path = _generate_output_path(path, spec.filename_suffix, ".json")
    
    results = []
    for i, item in enumerate(data):
        record = _extract_fields(item, spec.fields)
        if 'slice_index' not in record:
            record['slice_index'] = i
        results.append(record)
    
    summary = {
        "total_items": len(results),
        "results": results
    }
    
    if spec.include_metadata:
        summary["analysis_type"] = "custom_analysis"
    
    json_content = json.dumps(summary, indent=2, default=str)
    
    for backend in backends:
        if backend == Backend.DISK.value:
            filemanager.ensure_directory(str(Path(output_path).parent), backend)
        kwargs = backend_kwargs.get(backend, {})
        filemanager.save(json_content, output_path, backend, **kwargs)
    
    logger.info(f"Materialized {len(results)} items to {output_path}")
    return output_path


def _materialize_dual(
    data: List[Any],
    path: str,
    filemanager,
    backends: List[str],
    backend_kwargs: Dict,
    spec: MaterializationSpec
) -> str:
    """Materialize data as both JSON summary + CSV details."""
    base_path = _generate_output_path(path, "", "")
    json_path = f"{base_path}.json"
    csv_path = f"{base_path}_details.csv"
    
    # CSV with all fields
    rows = []
    for i, item in enumerate(data):
        row = _extract_fields(item, spec.fields)
        if 'slice_index' not in row:
            row['slice_index'] = i
        rows.append(row)
    
    # JSON with summary fields
    summary_data = []
    for i, item in enumerate(data):
        record = _extract_fields(item, spec.summary_fields or spec.fields)
        if 'slice_index' not in record:
            record['slice_index'] = i
        summary_data.append(record)
    
    summary = {
        "total_items": len(summary_data),
        "results": summary_data
    }
    
    if spec.include_metadata:
        summary["analysis_type"] = "custom_analysis"
    
    # Save to all backends
    for backend in backends:
        if backend == Backend.DISK.value:
            filemanager.ensure_directory(str(Path(json_path).parent), backend)
        kwargs = backend_kwargs.get(backend, {})
        
        if rows:
            df = pd.DataFrame(rows)
            filemanager.save(df.to_csv(index=False), csv_path, backend, **kwargs)
        
        filemanager.save(json.dumps(summary, indent=2, default=str), json_path, backend, **kwargs)
    
    logger.info(f"Materialized {len(rows)} rows (dual format) to {json_path}")
    return json_path


# Convenience factory functions

def csv_materializer(
    fields: Optional[List[str]] = None,
    filename_suffix: str = ".csv"
) -> Callable:
    """
    Create a CSV materializer.
    
    Args:
        fields: Field names to extract. None = all fields.
        filename_suffix: Suffix for output file (default: '.csv')
    
    Example:
        @special_outputs(("counts", csv_materializer(fields=["count", "area"])))
        def analyze(image):
            return processed, [CountResult(count=10, area=50.0)]
    """
    spec = MaterializationSpec(
        format='csv',
        filename_suffix=filename_suffix,
        fields=fields
    )
    return create_materializer(spec)


def json_materializer(
    fields: Optional[List[str]] = None,
    filename_suffix: str = ".json"
) -> Callable:
    """
    Create a JSON materializer.
    
    Args:
        fields: Field names to extract. None = all fields.
        filename_suffix: Suffix for output file (default: '.json')
    """
    spec = MaterializationSpec(
        format='json',
        filename_suffix=filename_suffix,
        fields=fields
    )
    return create_materializer(spec)


def dual_materializer(
    fields: Optional[List[str]] = None,
    summary_fields: Optional[List[str]] = None,
    filename_suffix: str = ""
) -> Callable:
    """
    Create a dual CSV+JSON materializer.
    
    Produces both:
    - {base}.json with summary
    - {base}_details.csv with all data
    
    Args:
        fields: Fields for CSV (None = all)
        summary_fields: Fields for JSON summary (None = same as fields)
        filename_suffix: Base suffix before .json/.csv
    """
    spec = MaterializationSpec(
        format='dual',
        filename_suffix=filename_suffix,
        fields=fields,
        summary_fields=summary_fields
    )
    return create_materializer(spec)
