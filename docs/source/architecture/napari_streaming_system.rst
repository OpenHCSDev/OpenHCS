Napari Streaming System
=======================

Overview
--------

Pipeline visualization requires real-time data streaming to external processes without blocking pipeline execution. The napari streaming system provides automatic visualization creation and materialization-aware data filtering for efficient real-time monitoring.

**The Visualization Challenge**: Traditional visualization approaches embed viewers in the main process, causing Qt threading conflicts and blocking pipeline execution. This creates a fundamental tension between visualization needs and processing performance.

**The OpenHCS Solution**: A process-based streaming architecture that separates visualization into independent processes communicating via ZeroMQ. This eliminates Qt threading issues while enabling true real-time monitoring without performance impact on pipeline execution.

**Key Innovation**: Materialization-aware filtering ensures only meaningful outputs (final results, checkpoints) are visualized rather than overwhelming users with every intermediate processing step.

Automatic Visualizer Creation
-----------------------------

Compiler Detection
~~~~~~~~~~~~~~~~~~

The system automatically detects visualization requirements during pipeline compilation and creates napari viewers when needed:

.. code-block:: python

   # Pipeline steps declare streaming intent using LazyNapariStreamingConfig
   Step(
       name="Image Enhancement Processing",
       func=enhance_images,
       step_materialization_config=LazyStepMaterializationConfig(),
       napari_streaming_config=LazyNapariStreamingConfig(well_filter=2)
   )

   # Compiler detects streaming configs during compilation
   for attr_name in dir(resolved_step):
       config = getattr(resolved_step, attr_name, None)
       if isinstance(actual_config, StreamingConfig):
           has_streaming = True
           required_visualizers.append({
               'backend': actual_config.backend.name,
               'config': actual_config
           })

The compiler scans pipeline steps during compilation and detects ``StreamingConfig`` instances. This ensures visualizers are only created when streaming configurations are present.

Process-Based Architecture
~~~~~~~~~~~~~~~~~~~~~~~~~~

The orchestrator automatically creates napari viewer processes when streaming is detected:

.. code-block:: python

   # Orchestrator creates napari viewer process automatically
   if needs_visualizer:
       visualizer = NapariStreamVisualizer(
           filemanager, 
           viewer_title="OpenHCS Pipeline Visualization"
       )
       visualizer.start_viewer()  # Separate process with Qt event loop
       
   # Worker processes communicate via ZeroMQ (no Qt conflicts)
   filemanager.save_batch(data, paths, Backend.NAPARI_STREAM.value)

**Why Process Separation Works**: Running napari in a dedicated process with its own Qt event loop eliminates threading conflicts. Pipeline workers stream data via ZeroMQ on a constant port (5555), enabling true parallel execution without visualization blocking processing.

Materialization-Aware Streaming
-------------------------------

Intelligent Data Filtering
~~~~~~~~~~~~~~~~~~~~~~~~~~

Traditional streaming sends all processed data, overwhelming visualization with intermediate results. The materialization-aware system only streams files that would be written to persistent storage:

.. code-block:: python

   # Only stream files that would be materialized
   if step_plan.get('stream_to_napari', False):
       napari_paths = []
       napari_data = []
       
       # 1. Main output materialization (disk/zarr writes)
       if write_backend != Backend.MEMORY.value:
           napari_paths = get_paths_for_axis(step_output_dir, Backend.MEMORY.value)
           napari_data = filemanager.load_batch(napari_paths, Backend.MEMORY.value)
       
       # 2. Per-step materialization (checkpoint writes)
       if "materialized_output_dir" in step_plan:
           materialized_paths = _generate_materialized_paths(...)
           napari_paths.extend(materialized_paths)
           napari_data.extend(memory_data)
       
       # Stream only materialized files
       if napari_paths:
           filemanager.save_batch(napari_data, napari_paths, Backend.NAPARI_STREAM.value)

This filtering ensures visualization shows only meaningful outputs (final results, checkpoints) rather than every intermediate processing step, making the visualization focused and useful.

Streaming Logic Integration
~~~~~~~~~~~~~~~~~~~~~~~~~~~

The materialization-aware logic integrates seamlessly with OpenHCS's existing materialization system:

- **Main Output Materialization**: When steps write to disk or zarr backends, those files are streamed
- **Per-Step Materialization**: When steps have materialization configs with checkpoint directories, those files are streamed  
- **Memory-Only Steps**: When steps keep everything in memory, nothing is streamed (as expected)

This ensures streaming behavior aligns perfectly with data persistence decisions, providing visualization exactly where users need it most.

ZeroMQ Communication Protocol
-----------------------------

Message Format Compatibility
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The system supports dual message formats for maximum flexibility:

.. code-block:: python

   # Streaming backend sends JSON messages
   metadata = {
       'path': str(file_path),
       'shape': np_data.shape,
       'dtype': str(np_data.dtype),
       'shm_name': shared_memory_name,  # For large arrays
       'data': np_data.tolist()         # Fallback for small arrays
   }
   publisher.send_json(metadata)

   # Napari process handles both JSON and pickle formats
   try:
       data = json.loads(message.decode('utf-8'))  # From streaming backend
       # Load from shared memory or direct data
   except (json.JSONDecodeError, UnicodeDecodeError):
       data = pickle.loads(message)  # From direct visualizer calls

The dual-format support enables both automatic streaming (JSON) and manual visualization calls (pickle) through the same napari viewer process.

Shared Memory Optimization
~~~~~~~~~~~~~~~~~~~~~~~~~~

Large arrays use shared memory for efficient data transfer:

.. code-block:: python

   # Large arrays use shared memory for efficiency
   if np_data.nbytes > 1024:  # Threshold for shared memory
       shm = multiprocessing.shared_memory.SharedMemory(
           create=True, size=np_data.nbytes, name=shm_name
       )
       shm_array = np.ndarray(np_data.shape, dtype=np_data.dtype, buffer=shm.buf)
       shm_array[:] = np_data[:]
       
       # Send metadata only, data stays in shared memory
       metadata = {'shm_name': shm_name, 'shape': shape, 'dtype': dtype}
   else:
       # Small arrays sent directly in JSON
       metadata = {'data': np_data.tolist(), 'shape': shape, 'dtype': dtype}

This optimization minimizes ZeroMQ message size and memory copying for large image arrays while maintaining simplicity for small data.

Integration Patterns
--------------------

Pipeline Step Configuration
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Streaming is enabled per-step and respects materialization configuration:

.. code-block:: python

   # Enable streaming for specific steps
   Step(
       name="Final Results",
       func=generate_results,
       step_materialization_config=LazyStepMaterializationConfig(),
       napari_streaming_config=LazyNapariStreamingConfig()  # Only final results streamed
   )

   # Memory-only steps don't stream (no materialization)
   Step(
       name="Intermediate Processing",
       func=process_intermediate,
       napari_streaming_config=LazyNapariStreamingConfig()  # No effect - nothing materialized
   )

Streaming respects the materialization configuration, ensuring only persistent outputs appear in visualization.

Persistent Viewer Management
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Viewers persist across pipeline runs for efficient resource usage:

.. code-block:: python

   # Viewer persists across pipeline runs
   visualizer.start_viewer()  # Creates process if not running
   # ... pipeline execution ...
   visualizer.stop_viewer()   # Keeps process alive if persistent=True

   # Reuse existing viewer for subsequent runs
   if visualizer.is_running:
       # Connect to existing process on port 5555
   else:
       # Create new process

This enables efficient resource usage by maintaining napari viewers across multiple pipeline executions rather than creating new processes each time.

**Architecture Benefits**: The napari streaming system provides real-time visualization without compromising pipeline performance, intelligent data filtering to show only relevant outputs, and persistent viewer management for efficient resource usage across multiple pipeline runs.
