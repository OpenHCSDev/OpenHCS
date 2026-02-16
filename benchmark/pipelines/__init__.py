"""Pipeline registry."""

from benchmark.pipelines.registry import (
    PipelineSpec,
    NUCLEI_SEGMENTATION,
    PIPELINE_REGISTRY,
    get_pipeline_spec,
)

__all__ = [
    "PipelineSpec",
    "NUCLEI_SEGMENTATION",
    "PIPELINE_REGISTRY",
    "get_pipeline_spec",
]
