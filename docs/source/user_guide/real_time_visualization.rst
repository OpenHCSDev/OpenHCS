Real-Time Visualization with Napari
===================================

Overview
--------

OpenHCS provides automatic real-time visualization of pipeline results using napari, a fast n-dimensional image viewer. This enables you to monitor processing progress and immediately see results as they're generated.

**Key Benefits**:

- **Automatic Setup**: Napari viewers are created automatically when needed
- **Smart Filtering**: Only shows meaningful outputs (final results, checkpoints), not every intermediate step
- **No Performance Impact**: Visualization runs in separate processes, doesn't slow down processing
- **Persistent Viewers**: Napari windows stay open across multiple pipeline runs

Quick Start
-----------

Enable napari streaming for any pipeline step by adding ``stream_to_napari=True``:

.. code-block:: python

   from openhcs import Step, Pipeline
   from openhcs.config import LazyStepMaterializationConfig

   # Create pipeline with real-time visualization
   pipeline = Pipeline([
       Step(
           name="Image Enhancement",
           func=enhance_images,
           materialization_config=LazyStepMaterializationConfig(),
           stream_to_napari=True  # Enable real-time visualization
       ),
       Step(
           name="Cell Segmentation", 
           func=segment_cells,
           stream_to_napari=True  # This step will also be visualized
       )
   ])

   # Run pipeline - napari window opens automatically
   orchestrator.execute_pipeline(pipeline)

When you run this pipeline, OpenHCS will:

1. **Automatically create** a napari viewer window
2. **Stream results** from steps with ``stream_to_napari=True``
3. **Keep the viewer open** for subsequent pipeline runs

Installation Requirements
-------------------------

Napari streaming requires napari to be installed:

.. code-block:: bash

   # Install OpenHCS with visualization support
   pip install "openhcs[viz]"

   # Or install napari separately
   pip install napari

If napari is not installed, OpenHCS will log a warning and continue without visualization.

What Gets Visualized
--------------------

OpenHCS intelligently filters what gets sent to napari based on your materialization configuration:

**Materialized Files Only**
  Only files that would be saved to disk are visualized. This prevents overwhelming you with intermediate processing steps.

**Final Results**
  Steps that write to disk or zarr backends automatically stream their outputs.

**Checkpoints**
  Steps with ``materialization_config`` stream their checkpoint files.

**Memory-Only Steps**
  Steps that keep everything in memory don't stream anything (as expected).

Example configurations:

.. code-block:: python

   # This step's results will be visualized (has materialization config)
   Step(
       name="Final Results",
       func=generate_results,
       materialization_config=LazyStepMaterializationConfig(),
       stream_to_napari=True
   )

   # This step won't be visualized (no materialization, stays in memory)
   Step(
       name="Intermediate Processing",
       func=process_intermediate,
       stream_to_napari=True  # No effect - nothing gets materialized
   )

Viewer Management
-----------------

Automatic Creation
~~~~~~~~~~~~~~~~~~

OpenHCS automatically creates napari viewers when any step in your pipeline has ``stream_to_napari=True``. You don't need to manually create or manage viewers.

Persistent Viewers
~~~~~~~~~~~~~~~~~~

Napari viewers stay open across multiple pipeline runs by default. This means:

- **First run**: Creates new napari window
- **Subsequent runs**: Reuses existing napari window
- **New data**: Appears as new layers or updates existing layers

Manual Control
~~~~~~~~~~~~~~

If you need manual control over the napari viewer:

.. code-block:: python

   from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer

   # Create visualizer manually
   visualizer = NapariStreamVisualizer(
       filemanager, 
       viewer_title="My Custom Viewer"
   )

   # Start viewer
   visualizer.start_viewer()

   # Check if running
   if visualizer.is_running:
       print("Napari viewer is active")

   # Stop viewer (optional - usually stays open)
   visualizer.stop_viewer()

Layer Organization
------------------

Data appears in napari as separate layers with descriptive names:

**Layer Naming**
  Layers are named based on the file paths, making it easy to identify different processing steps and wells.

**Example Layer Names**:
  - ``checkpoints_step2_A01_s001_w1_z001.tif``
  - ``final_results_B03_s002_w2_z001.tif``

**Layer Updates**
  When the same file is processed again (e.g., rerunning a pipeline), the existing layer is updated rather than creating a new one.

Performance Considerations
--------------------------

**No Processing Impact**
  Napari runs in a separate process, so visualization doesn't slow down your pipeline execution.

**Memory Efficiency**
  Large images use shared memory for efficient data transfer between processes.

**Network Usage**
  All communication happens locally via ZeroMQ on port 5555. No network traffic is generated.

**Resource Usage**
  Napari viewers use modest system resources and can handle typical high-content screening image sizes efficiently.

Troubleshooting
---------------

**Napari Window Doesn't Appear**

1. Check that napari is installed: ``pip install napari``
2. Verify your steps have ``stream_to_napari=True``
3. Ensure steps have materialization configs (otherwise nothing gets streamed)

**No Images in Napari**

1. Check that your steps are actually materializing files (not keeping everything in memory)
2. Look for log messages like "Streamed X materialized images to napari"
3. Verify your pipeline is processing the expected data

**Performance Issues**

1. Napari visualization should not impact pipeline performance
2. If you experience slowdowns, check system memory usage
3. Consider reducing the number of steps with ``stream_to_napari=True``

**Port Conflicts**

OpenHCS uses port 5555 for napari communication. If this port is in use:

1. Close other applications using port 5555
2. Or modify ``DEFAULT_NAPARI_STREAM_PORT`` in your configuration

Integration Examples
--------------------

**Basic Pipeline with Visualization**:

.. code-block:: python

   from openhcs import Pipeline, Step
   from openhcs.config import LazyStepMaterializationConfig

   pipeline = Pipeline([
       # Preprocessing (not visualized)
       Step(name="Load Images", func=load_images),
       
       # Enhancement (visualized)
       Step(
           name="Enhance Images",
           func=enhance_images,
           materialization_config=LazyStepMaterializationConfig(),
           stream_to_napari=True
       ),
       
       # Final analysis (visualized)
       Step(
           name="Cell Analysis",
           func=analyze_cells,
           materialization_config=LazyStepMaterializationConfig(),
           stream_to_napari=True
       )
   ])

**Multi-Well Experiment**:

When processing multiple wells, each well's results appear as separate layers in napari, allowing you to compare results across conditions in real-time.

**Large Dataset Processing**:

For large datasets, consider enabling visualization only for key steps to avoid overwhelming the napari interface while still monitoring critical processing stages.
