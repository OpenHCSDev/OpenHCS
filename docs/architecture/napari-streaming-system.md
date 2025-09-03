# Napari Streaming System

## Overview

Pipeline visualization requires real-time data streaming to external processes without blocking pipeline execution. The napari streaming system provides automatic visualization creation and materialization-aware data filtering for efficient real-time monitoring.

Traditional visualization approaches embed viewers in the main process, causing Qt threading conflicts and blocking pipeline execution. The streaming architecture separates visualization into independent processes that communicate via ZeroMQ.

## Automatic Visualizer Creation

### Compiler Detection

```python
# Pipeline steps declare streaming intent:
Step(
    name="Image Enhancement",
    func=enhance_images,
    materialization_config=LazyStepMaterializationConfig(),
    stream_to_napari=True  # Triggers automatic visualizer creation
)

# Compiler detects streaming requirements:
has_napari_streaming = any(getattr(step, 'stream_to_napari', False) 
                          for step in pipeline_definition)
if has_napari_streaming:
    context.create_visualizer = True
```

The compiler scans pipeline steps during compilation and sets the visualizer creation flag when any step enables napari streaming.

### Process-Based Architecture

```python
# Orchestrator creates napari viewer process automatically:
if needs_visualizer:
    visualizer = NapariStreamVisualizer(
        filemanager, 
        viewer_title="OpenHCS Pipeline Visualization"
    )
    visualizer.start_viewer()  # Separate process with Qt event loop
    
# Worker processes communicate via ZeroMQ (no Qt conflicts):
filemanager.save_batch(data, paths, Backend.NAPARI_STREAM.value)
```

This eliminates Qt threading issues by running napari in a dedicated process with its own event loop, while pipeline workers stream data via ZeroMQ on a constant port (5555).

## Materialization-Aware Streaming

### Intelligent Data Filtering

Traditional streaming sends all processed data, overwhelming visualization with intermediate results. The materialization-aware system only streams files that would be written to persistent storage.

```python
# Only stream files that would be materialized:
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
```

This ensures visualization shows only meaningful outputs (final results, checkpoints) rather than every intermediate processing step.

## ZeroMQ Communication Protocol

### Message Format Compatibility

```python
# Streaming backend sends JSON messages:
metadata = {
    'path': str(file_path),
    'shape': np_data.shape,
    'dtype': str(np_data.dtype),
    'shm_name': shared_memory_name,  # For large arrays
    'data': np_data.tolist()         # Fallback for small arrays
}
publisher.send_json(metadata)

# Napari process handles both JSON and pickle formats:
try:
    data = json.loads(message.decode('utf-8'))  # From streaming backend
    # Load from shared memory or direct data
except (json.JSONDecodeError, UnicodeDecodeError):
    data = pickle.loads(message)  # From direct visualizer calls
```

The dual-format support enables both automatic streaming (JSON) and manual visualization calls (pickle) through the same napari viewer process.

### Shared Memory Optimization

```python
# Large arrays use shared memory for efficiency:
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
```

This minimizes ZeroMQ message size and memory copying for large image arrays while maintaining simplicity for small data.

## Integration Patterns

### Pipeline Step Configuration

```python
# Enable streaming for specific steps:
Step(
    name="Final Results",
    func=generate_results,
    materialization_config=LazyStepMaterializationConfig(),
    stream_to_napari=True  # Only final results streamed
)

# Memory-only steps don't stream (no materialization):
Step(
    name="Intermediate Processing", 
    func=process_intermediate,
    stream_to_napari=True  # No effect - nothing materialized
)
```

Streaming respects the materialization configuration, ensuring only persistent outputs appear in visualization.

### Persistent Viewer Management

```python
# Viewer persists across pipeline runs:
visualizer.start_viewer()  # Creates process if not running
# ... pipeline execution ...
visualizer.stop_viewer()   # Keeps process alive if persistent=True

# Reuse existing viewer for subsequent runs:
if visualizer.is_running:
    # Connect to existing process on port 5555
else:
    # Create new process
```

This enables efficient resource usage by maintaining napari viewers across multiple pipeline executions rather than creating new processes each time.
