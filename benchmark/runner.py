"""Benchmark runner."""

from __future__ import annotations

from pathlib import Path
from typing import Iterable

from benchmark.contracts.dataset import DatasetSpec
from benchmark.contracts.tool_adapter import BenchmarkResult, ToolAdapter
from benchmark.datasets.acquire import acquire_dataset
from benchmark.pipelines.registry import get_pipeline_spec


def run_benchmark(
    dataset_spec: DatasetSpec,
    tool_adapters: list[ToolAdapter],
    pipeline_name: str,
    metrics: Iterable,
) -> list[BenchmarkResult]:
    """
    Run benchmark across tools.

    1. Validate all tools
    2. Acquire dataset
    3. For each tool: run with metrics
    4. Return results
    """
    # Validate tools are installed
    for adapter in tool_adapters:
        adapter.validate_installation()

    acquired = acquire_dataset(dataset_spec)
    pipeline_spec = get_pipeline_spec(pipeline_name)

    # Merge pipeline parameters with dataset-specific context
    pipeline_params = {
        **pipeline_spec.parameters,
        "dataset_id": dataset_spec.id,
        "microscope_type": acquired.microscope_type,
    }

    results: list[BenchmarkResult] = []
    output_root = Path.cwd() / "benchmark_outputs"
    output_root.mkdir(parents=True, exist_ok=True)

    for adapter in tool_adapters:
        tool_output_dir = output_root / f"{adapter.name}_{dataset_spec.id}"
        tool_result = adapter.run(
            dataset_path=acquired.path,
            pipeline_name=pipeline_spec.name,
            pipeline_params=pipeline_params,
            metrics=list(metrics),
            output_dir=tool_output_dir,
        )
        results.append(tool_result)

    return results
