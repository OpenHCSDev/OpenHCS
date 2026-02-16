"""OpenHCS tool adapter."""

from __future__ import annotations

import logging
from contextlib import ExitStack
from pathlib import Path
from typing import Any

import numpy as np
from tqdm import tqdm
from skimage import filters, morphology, measure

from benchmark.contracts.tool_adapter import (
    BenchmarkResult,
    ToolAdapter,
    ToolExecutionError,
    ToolNotInstalledError,
)
from benchmark.contracts.metric import MetricCollector

logger = logging.getLogger(__name__)


class OpenHCSAdapter(ToolAdapter):
    """OpenHCS tool adapter."""

    name = "OpenHCS"

    def __init__(self):
        import openhcs

        self.version = openhcs.__version__

    def validate_installation(self) -> None:
        """Check OpenHCS is importable."""
        try:
            import openhcs  # noqa: F401
        except ImportError as exc:
            raise ToolNotInstalledError(f"OpenHCS not installed: {exc}") from exc

    def _prepare_filemanager(self):
        """Initialize FileManager and microscope handler."""
        from openhcs.io.filemanager import FileManager
        from openhcs.io.base import storage_registry, ensure_storage_registry

        ensure_storage_registry()
        return FileManager(storage_registry)

    def _load_microscope(self, filemanager, dataset_path: Path, microscope_type: str):
        """Create microscope handler for dataset."""
        from openhcs.microscopes import create_microscope_handler

        return create_microscope_handler(
            microscope_type=microscope_type or "auto",
            plate_folder=dataset_path,
            filemanager=filemanager,
            allowed_auto_types=[microscope_type] if microscope_type else None,
        )

    def _run_minimal_pipeline(self, image: np.ndarray, params: dict[str, Any]) -> np.ndarray:
        """Blur → threshold → label segmentation pipeline."""
        method = params.get("threshold_method")
        if method not in (None, "Otsu"):
            raise ToolExecutionError(f"Unsupported threshold_method '{method}'")

        scope = params.get("threshold_scope")
        if scope not in (None, "Global"):
            raise ToolExecutionError(f"Unsupported threshold_scope '{scope}'")

        declump = params.get("declump_method")
        if declump not in (None, "Shape"):
            raise ToolExecutionError(f"Unsupported declump_method '{declump}'")

        diameter_range = params.get("diameter_range")
        if diameter_range is not None and (
            not isinstance(diameter_range, tuple)
            or len(diameter_range) != 2
            or not all(isinstance(x, (int, float)) for x in diameter_range)
        ):
            raise ToolExecutionError("diameter_range must be a (min, max) tuple")

        # Convert to float for processing while preserving dynamic range
        if image.dtype != np.float32:
            image = image.astype(np.float32)

        # Gaussian blur
        blurred = filters.gaussian(image, sigma=1)

        # Threshold
        threshold_value = filters.threshold_otsu(blurred)
        mask = blurred > threshold_value

        # Optional morphological opening to denoise
        radius = params.get("opening_radius", 0)
        if radius and radius > 0:
            selem = morphology.disk(radius)
            mask = morphology.opening(mask, selem)

        # Fill small holes if requested
        if params.get("fill_holes", False):
            mask = morphology.remove_small_holes(mask)

        labels = measure.label(mask)

        # Apply size filtering derived from diameter_range if provided
        if diameter_range:
            min_d, max_d = diameter_range
            min_area = np.pi * (min_d / 2) ** 2
            max_area = np.pi * (max_d / 2) ** 2
            props = measure.regionprops(labels)
            remove_ids = [
                prop.label
                for prop in props
                if prop.area < min_area or prop.area > max_area
            ]
            if remove_ids:
                mask = np.isin(labels, remove_ids, invert=True)
                labels = measure.label(mask)
        return labels.astype(np.uint16)

    def run(
        self,
        dataset_path: Path,
        pipeline_name: str,
        pipeline_params: dict[str, Any],
        metrics: list[Any],
        output_dir: Path,
    ) -> BenchmarkResult:
        """Execute OpenHCS pipeline with metrics."""
        output_dir.mkdir(parents=True, exist_ok=True)

        microscope_type = pipeline_params.get("microscope_type")
        if microscope_type in (None, "auto"):
            raise ToolExecutionError("microscope_type must be explicit (e.g., 'bbbc021'); auto-detect is not allowed.")

        # Validate metric collectors
        for metric in metrics:
            if not isinstance(metric, MetricCollector):
                raise ToolExecutionError(f"Metric {metric} does not extend MetricCollector")

        filemanager = self._prepare_filemanager()

        try:
            microscope_handler = self._load_microscope(filemanager, dataset_path, microscope_type)
        except Exception as exc:
            raise ToolExecutionError(f"Failed to create microscope handler: {exc}") from exc

        # Enumerate image files via FileManager (leveraging OpenHCS discovery)
        try:
            from openhcs.constants.constants import Backend
            image_paths = filemanager.list_image_files(dataset_path, Backend.DISK.value, recursive=True)
        except Exception as exc:
            raise ToolExecutionError(f"Failed to list dataset images: {exc}") from exc

        if not image_paths:
            raise ToolExecutionError(f"No image files found in dataset path: {dataset_path}")

        with ExitStack() as stack:
            for metric in metrics:
                stack.enter_context(metric)

            for img_path in tqdm(image_paths, desc="OpenHCS pipeline", leave=False):
                image = filemanager.load(img_path, "disk", content_type="image")
                labels = self._run_minimal_pipeline(image, pipeline_params)

                output_path = output_dir / f"{Path(img_path).stem}_labels.tif"
                filemanager.save(labels, output_path, "disk")

        # Collect metrics after contexts have exited
        metric_results: dict[str, Any] = {
            metric.name: metric.get_result() for metric in metrics
        }

        return BenchmarkResult(
            tool_name=self.name,
            dataset_id=pipeline_params.get("dataset_id", dataset_path.name),
            pipeline_name=pipeline_name,
            metrics=metric_results,
            output_path=output_dir,
            success=True,
            error_message=None,
            provenance={
                "openhcs_version": getattr(self, "version", "unknown"),
                "microscope_type": microscope_handler.microscope_type,
                "image_count": len(image_paths),
            },
        )
