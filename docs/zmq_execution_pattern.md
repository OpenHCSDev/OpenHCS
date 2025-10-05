# ZMQ Execution Pattern

The ZMQ execution pattern provides a unified, location-transparent way to execute OpenHCS pipelines. It replaces the subprocess runner pattern with a more robust, bidirectional communication system based on the proven Napari ZMQ streaming architecture.

## Overview

The pattern consists of:

1. **ZMQExecutionServer**: Receives pipeline execution requests via ZMQ, executes them, and streams progress updates
2. **ZMQExecutionClient**: Sends execution requests to servers, receives results and progress updates
3. **Dual-channel architecture**: Separate data and control channels for robust communication
4. **Multi-instance support**: Connect to existing servers or spawn new ones automatically
5. **Location transparency**: Same API whether server is local subprocess or remote machine

## Architecture

### Dual-Channel Pattern

The pattern uses two ZMQ channels (extracted from Napari streaming):

- **Data Port** (e.g., 7777): PUB/SUB socket for streaming progress updates
- **Control Port** (data_port + 1000, e.g., 8777): REQ/REP socket for commands and responses

### Message Flow

```
Client                          Server
  |                               |
  |-- PING (control) ------------>|
  |<-- PONG (control) ------------|
  |                               |
  |-- EXECUTE (control) --------->|
  |   (pipeline_code,             |
  |    config_code)               |
  |                               |
  |                          [executing]
  |                               |
  |<-- PROGRESS (data) -----------|
  |<-- PROGRESS (data) -----------|
  |<-- PROGRESS (data) -----------|
  |                               |
  |<-- RESULTS (control) ---------|
```

## Usage

### Basic Example

```python
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
from openhcs.core.pipeline import Pipeline
from openhcs.core.config import GlobalPipelineConfig, PipelineConfig

# Create pipeline and config
pipeline = Pipeline(...)
global_config = GlobalPipelineConfig(...)
pipeline_config = PipelineConfig(...)

# Connect to server (spawns if needed)
client = ZMQExecutionClient(port=7777, persistent=True)
client.connect()

# Execute pipeline
response = client.execute_pipeline(
    plate_id="/path/to/plate",
    pipeline_steps=pipeline.steps,
    global_config=global_config,
    pipeline_config=pipeline_config
)

# Check results
if response['status'] == 'complete':
    print(f"Success! Wells processed: {len(response['results']['well_results'])}")
else:
    print(f"Error: {response['message']}")

# Cleanup
client.disconnect()
```

### Context Manager

```python
with ZMQExecutionClient(port=7777) as client:
    response = client.execute_pipeline(...)
    # Automatic cleanup on exit
```

### Progress Callbacks (Future)

```python
def on_progress(message):
    print(f"Well {message['well_id']}: {message['step']} - {message['status']}")

client = ZMQExecutionClient(
    port=7777,
    progress_callback=on_progress
)
```

## Server Modes

### Persistent Mode (Detached Subprocess)

Survives parent process termination. Ideal for:
- Remote execution servers
- Shared execution servers (multiple UIs)
- Long-running services

```python
client = ZMQExecutionClient(port=7777, persistent=True)
```

Server runs as detached subprocess via:
```bash
python -m openhcs.runtime.zmq_execution_server_launcher --port 7777 --persistent
```

### Non-Persistent Mode (Multiprocessing.Process)

Dies with parent process. Ideal for:
- Testing
- Single-use execution
- UI-managed execution

```python
client = ZMQExecutionClient(port=7777, persistent=False)
```

Server runs as multiprocessing.Process, automatically cleaned up when client disconnects.

## Multi-Instance Support

The client automatically handles multiple server instances:

1. **Check if port in use**: Uses socket binding to detect existing servers
2. **Try to connect**: Sends ping to verify server is responsive
3. **Spawn if needed**: If no server or unresponsive, spawns new one
4. **Kill unresponsive**: If server exists but doesn't respond, kills and restarts

This mirrors Napari's viewer management pattern.

## Code-Based Transport

Unlike the subprocess runner (which pickles objects to temp files), the ZMQ pattern uses **code-based transport**:

1. Client converts objects to Python code using `pickle_to_python`
2. Client sends code as JSON strings via ZMQ
3. Server executes code to recreate objects
4. Server executes pipeline with recreated objects

Benefits:
- ✅ No temp files
- ✅ Network-safe (JSON strings)
- ✅ Human-readable (can inspect generated code)
- ✅ No enum pickling errors
- ✅ Location-transparent (same code for local/remote)

## Comparison with Subprocess Runner

| Feature | Subprocess Runner | ZMQ Execution |
|---------|------------------|---------------|
| Communication | One-way (fire-and-forget) | Bidirectional (request/response) |
| Transport | Pickle files | Code strings (JSON) |
| Progress | Log file polling | Real-time streaming |
| Cancellation | Kill process | Graceful cancellation |
| Multi-instance | No | Yes (port-based) |
| Process reuse | No | Yes (persistent mode) |
| Location | Local only | Local or remote |
| Handshake | No | Yes (ping/pong) |

## Testing

### Basic Test

```bash
python examples/test_zmq_execution_pattern.py
```

### Real Plate Test

```bash
python examples/test_zmq_with_real_plate.py
```

### Manual Server

Start server manually:
```bash
python -m openhcs.runtime.zmq_execution_server_launcher --port 7777 --persistent
```

Then run client in another terminal:
```bash
python examples/test_zmq_execution_pattern.py
```

## Implementation Details

### Base Classes

**ZMQServer** (`openhcs/runtime/zmq_base.py`):
- Abstract base class for dual-channel servers
- Implements handshake protocol (ping/pong)
- Port management utilities
- Lifecycle management (start/stop/is_running)

**ZMQClient** (`openhcs/runtime/zmq_base.py`):
- Abstract base class for dual-channel clients
- Connection management (connect/disconnect/is_connected)
- Multi-instance support (connect to existing or spawn new)
- Process spawning utilities

### Execution Classes

**ZMQExecutionServer** (`openhcs/runtime/zmq_execution_server.py`):
- Inherits from ZMQServer
- Handles execute, status, cancel requests
- Executes pipelines synchronously in main thread
- Sends progress updates via data channel

**ZMQExecutionClient** (`openhcs/runtime/zmq_execution_client.py`):
- Inherits from ZMQClient
- High-level API: `execute_pipeline()`, `get_status()`, `cancel_execution()`
- Code generation using `pickle_to_python`
- Progress callback support

## Future Enhancements

### Progress Streaming

Infrastructure is ready, needs orchestrator integration:

```python
# In orchestrator
def _on_well_progress(well_id, step, status):
    if hasattr(self, 'progress_callback'):
        self.progress_callback(well_id, step, status)

# Server sends via data channel
server.send_progress_update(well_id, step, status)

# Client receives and calls callback
if self.progress_callback:
    self.progress_callback(message)
```

### Graceful Cancellation

Infrastructure is ready, needs orchestrator integration:

```python
# Client sends cancel request
client.cancel_execution(execution_id)

# Server interrupts orchestrator
orchestrator.cancel()
```

### UI Integration

Replace subprocess runner in PyQt and Textual:

```python
# OLD: Subprocess runner
pickle.dump(data, file)
subprocess.Popen([sys.executable, subprocess_runner.py, file.name])

# NEW: ZMQ client
client = ZMQExecutionClient(port=7777, persistent=True)
client.execute_pipeline(
    pipeline_steps=pipeline_steps,
    global_config=global_config,
    pipeline_config=pipeline_config,
    progress_callback=self._on_progress_update
)
```

### RemoteOrchestrator Refactor

Make RemoteOrchestrator a thin wrapper:

```python
class RemoteOrchestrator:
    def __init__(self, server_host: str, server_port: int = 7777):
        self.client = ZMQExecutionClient(
            host=server_host,
            port=server_port,
            persistent=True
        )
    
    def run_remote_pipeline(self, plate_id, pipeline_steps, global_config, **kwargs):
        return self.client.execute_pipeline(
            pipeline_steps=pipeline_steps,
            global_config=global_config,
            **kwargs
        )
```

## Benefits

1. **Unified Communication**: Same pattern for local and remote execution
2. **Process Reuse**: Persistent servers handle multiple executions
3. **No Pickle Files**: Code-based transport eliminates temp file management
4. **Multi-Instance**: Multiple UIs can share same execution server
5. **Graceful Degradation**: Connects to existing or spawns new automatically
6. **Clean Separation**: Abstract base classes enable other use cases
7. **Proven Pattern**: Based on battle-tested Napari streaming architecture

