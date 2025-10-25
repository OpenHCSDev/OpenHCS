Getting Started with OpenHCS
============================

Installation
-----------

.. code-block:: bash

    pip install openhcs

Requirements:
- Python 3.8+
- For GPU acceleration: CUDA-compatible GPU with appropriate drivers

Installation Options
~~~~~~~~~~~~~~~~~~~

**Standard Installation** (with GPU support):

.. code-block:: bash

    pip install openhcs
    # Includes GPU libraries: pyclesperanto, cupy, etc.

**CPU-Only Installation** (for CI/testing environments):

.. code-block:: bash

    # Install with minimal dependencies
    pip install openhcs --no-deps
    pip install numpy scipy scikit-image pandas

    # Enable CPU-only mode
    export OPENHCS_CPU_ONLY=1

**Development Installation**:

.. code-block:: bash

    git clone https://github.com/your-org/openhcs.git
    cd openhcs
    pip install -e .

See :doc:`../user_guide/cpu_only_mode` for detailed CPU-only configuration.

Basic Example
------------

This example shows the core OpenHCS workflow: creating a pipeline with processing steps and running it on microscopy data.

.. code-block:: python

    from openhcs.core.pipeline import Pipeline
    from openhcs.core.steps.function_step import FunctionStep
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
    from openhcs.core.config import GlobalPipelineConfig
    from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize
    from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_single_channel
    from openhcs.constants.constants import VariableComponents

    # Define processing steps
    pipeline = Pipeline([
        # Normalize images
        FunctionStep(
            func=(stack_percentile_normalize, {
                'low_percentile': 1.0,
                'high_percentile': 99.0
            }),
            name="normalize",
            variable_components=[VariableComponents.SITE]
        ),

        # Count cells
        FunctionStep(
            func=(count_cells_single_channel, {}),
            name="count_cells",
            variable_components=[VariableComponents.SITE]
        )
    ])

    # Configure and run
    config = GlobalPipelineConfig(num_workers=2)
    orchestrator = PipelineOrchestrator(
        plate_path="/path/to/your/microscopy/data",
        global_config=config
    )

    # Execute pipeline
    orchestrator.run_pipeline(pipeline)

Understanding the Example
------------------------

The basic example demonstrates key OpenHCS concepts:

**Pipeline**: A list of processing steps that execute in sequence

**FunctionStep**: The basic processing unit that wraps a function with configuration

**Variable Components**: Defines how data is grouped for processing (SITE processes each imaging position separately)

**Orchestrator**: Manages pipeline execution across your dataset

Interactive Development
----------------------

OpenHCS provides two interface options:

**Desktop GUI (Recommended for local use):**

.. code-block:: bash

    # Install with GUI support
    pip install "openhcs[gui]"

    # Launch desktop application
    openhcs-gui

**Terminal Interface (For remote/SSH use):**

.. code-block:: bash

    # Install with TUI support
    pip install "openhcs[tui]"

    # Launch terminal interface
    openhcs-tui

Both interfaces provide:
- Microscopy data directory selection
- Pipeline configuration and editing
- Real-time execution monitoring
- Results visualization

Next Steps
----------

After running the basic example, explore these areas:

**Core Concepts**: :doc:`../concepts/index`
  Understand pipelines, steps, function patterns, and data organization

**Function Library**: :doc:`../concepts/function_library`
  Learn about available image processing functions and backends

**Configuration**: :doc:`../concepts/storage_system`
  Configure storage backends, memory management, and output options

**Advanced Examples**: :doc:`../guides/index`
  Multi-channel analysis, GPU acceleration, and large dataset processing

Common Patterns
---------------

**Multi-Channel Analysis**:

.. code-block:: python

    # Different analysis for different channels
    FunctionStep(
        func={
            '1': (count_cells_single_channel, {}),  # DAPI channel
            '2': (trace_neurites, {})               # GFP channel
        },
        group_by=GroupBy.CHANNEL,
        variable_components=[VariableComponents.SITE]
    )

**Function Chains**:

.. code-block:: python

    # Sequential processing steps
    FunctionStep(
        func=[
            (gaussian_filter, {'sigma': 2.0}),
            (threshold_otsu, {}),
            (binary_opening, {'footprint_radius': 3})
        ],
        variable_components=[VariableComponents.SITE]
    )

1-minute Quick Start
--------------------

If you want to try OpenHCS quickly with minimal setup, copy this tiny pipeline into a file named `quickstart.py` and run it with a small folder of images (or a single image for testing):

.. code-block:: python

    # quickstart.py — minimal pipeline
    from openhcs.core.pipeline import Pipeline
    from openhcs.core.steps.function_step import FunctionStep
    from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
    from openhcs.core.config import GlobalPipelineConfig
    from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize
    from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_single_channel

    pipeline = Pipeline([
        FunctionStep(func=(stack_percentile_normalize, {'low_percentile':1.0,'high_percentile':99.0}), name='normalize'),
        FunctionStep(func=(count_cells_single_channel, {}), name='count_cells')
    ])

    config = GlobalPipelineConfig(num_workers=1)
    orchestrator = PipelineOrchestrator(plate_path='path/to/images', global_config=config)
    orchestrator.run_pipeline(pipeline)

This runs a normalization step followed by a simple per-site cell counting analysis. Use `path/to/images` to point to a folder with one or more test images. The snippet is intentionally minimal — see the full "Basic Example" above for more realistic configurations.
