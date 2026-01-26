"""Example: run OpenHCS benchmark on BBBC021 nuclei segmentation."""

from pathlib import Path

from benchmark import (
    BBBC021_SINGLE_PLATE,
    OpenHCSAdapter,
    TimeMetric,
    MemoryMetric,
    run_benchmark,
)


def main() -> None:
    adapter = OpenHCSAdapter()
    metrics = [TimeMetric(), MemoryMetric()]

    results = run_benchmark(
        dataset_spec=BBBC021_SINGLE_PLATE,
        tool_adapters=[adapter],
        pipeline_name="nuclei_segmentation",
        metrics=metrics,
    )

    for result in results:
        status = "OK" if result.success else f"FAILED ({result.error_message})"
        print(f"[{result.tool_name}] {status}")
        print(f"  Dataset : {result.dataset_id}")
        print(f"  Pipeline: {result.pipeline_name}")
        print("  Metrics :")
        for name, value in result.metrics.items():
            print(f"    - {name}: {value}")
        print(f"  Outputs : {Path(result.output_path).resolve()}")


if __name__ == "__main__":
    main()
