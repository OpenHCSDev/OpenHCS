# ZMQ Execution Pattern - Complete Implementation Summary

**Status**: ✅ **FULLY IMPLEMENTED**

This document summarizes the complete implementation of the ZMQ execution pattern for OpenHCS, which replaces the legacy subprocess runner with a modern, bidirectional communication system.

## Overview

The ZMQ execution pattern provides location-transparent pipeline execution with real-time progress streaming, graceful cancellation, and process reuse. It works seamlessly for both local subprocess execution and remote server execution using the same API.

## Implementation Timeline

| Commit | Date | Feature | Files Changed |
|--------|------|---------|---------------|
| 8bae25f | - | ZMQ base infrastructure | 7 files (+1,920 lines) |
| 23c3efa | - | Progress streaming + RemoteOrchestrator refactor | 4 files (+246, -90) |
| 952a4fb | - | UI integration (PyQt + Textual) | 3 files (+289) |
| 53b615f | - | Graceful cancellation | 5 files (+152, -16) |
| bfb5357 | - | Execution tracking + timeout | 3 files (+113, -8) |
| 3ed0cc1 | - | Multiprocessing cancellation | 1 file (+29, -2) |

**Total**: 23 files changed, ~2,749 insertions, ~116 deletions

## Architecture

### Core Components

1. **ZMQ Base Classes** (`openhcs/runtime/zmq_base.py` - 532 lines)
   - `ZMQServer(ABC)`: Generic dual-channel server with handshake protocol
   - `ZMQClient(ABC)`: Generic multi-instance client with auto-spawning
   - Port management utilities extracted from Napari pattern

2. **Execution Server** (`openhcs/runtime/zmq_execution_server.py` - 424 lines)
   - Execution-specific server implementation
   - Handles execute/status/cancel requests
   - Mirrors `execution_server.py` pattern exactly
   - Supports both `config_params` and `config_code`

3. **Execution Client** (`openhcs/runtime/zmq_execution_client.py` - 375 lines)
   - High-level client API for pipeline execution
   - Code generation using `pickle_to_python`
   - Multi-instance support with auto-spawning
   - Background thread for progress streaming

4. **Server Launcher** (`openhcs/runtime/zmq_execution_server_launcher.py` - 73 lines)
   - Standalone script to launch execution server
   - Detached subprocess mode for persistent servers

### Communication Pattern

**Dual-Channel Architecture**:
- **Data Port** (e.g., 7777): PUB/SUB for progress streaming
- **Control Port** (Data Port + 1000): REQ/REP for commands

**Message Types**:
- `ping`: Handshake to verify server is ready
- `execute`: Execute pipeline with code/params
- `status`: Query execution status
- `cancel`: Request graceful cancellation
- `progress`: Real-time progress updates (data channel)

## Features Implemented

### 1. Progress Streaming ✅

**Orchestrator** (`openhcs/core/orchestrator/orchestrator.py`):
- Added `progress_callback` parameter to `__init__()`
- Callback signature: `(axis_id: str, step: str, status: str, metadata: dict) -> None`
- Progress callbacks at key execution points:
  - Axis started: `progress_callback(axis_id, 'pipeline', 'started', {...})`
  - Step started: `progress_callback(axis_id, step_name, 'started', {...})`
  - Step completed: `progress_callback(axis_id, step_name, 'completed', {...})`
  - Axis completed: `progress_callback(axis_id, 'pipeline', 'completed', {...})`
  - Cancellation: `progress_callback(axis_id, 'pipeline', 'cancelled', {...})`

**ZMQ Server**:
- Wires orchestrator progress callback to `send_progress_update()`
- Streams updates via ZMQ data channel (PUB socket)

**ZMQ Client**:
- Background thread listens for progress updates
- Non-blocking receives with `zmq.NOBLOCK`
- Calls user's progress callback when messages arrive
- Thread-safe with `threading.Event` for clean shutdown

### 2. Graceful Cancellation ✅

**Orchestrator**:
- Added `_cancel_requested` (threading.Event) for threading mode
- Added `_mp_cancel_event` (multiprocessing.Event) for multiprocessing mode
- New methods: `cancel()` and `reset_cancellation()`
- Cancellation check before each step in execution loop
- Sends progress update when cancellation detected
- Raises `RuntimeError` to abort execution

**ZMQ Server**:
- Implemented `_handle_cancel()` method
- Finds orchestrator in `active_executions` by execution_id
- Calls `orchestrator.cancel()` to set cancellation flag
- Returns status response

**ZMQ Client**:
- Enhanced `cancel_execution(execution_id)` method
- Sends cancel request to server
- Logs cancellation request and response

**UI Integration**:
- PyQt and Textual both track `current_execution_id`
- Stop button calls `zmq_client.cancel_execution(execution_id)`
- 5-second timeout with status polling
- Graceful degradation if cancellation takes too long

**Multiprocessing Support**:
- Shared `multiprocessing.Event` passed to worker processes
- Workers check event before each step
- Consistent cancellation across threading and multiprocessing modes

### 3. UI Integration ✅

**Environment Variable**: `OPENHCS_USE_ZMQ_EXECUTION` (default: `true`)

**PyQt PlateManager** (`openhcs/pyqt_gui/widgets/plate_manager.py`):
- Split `action_run_plates()` into `_run_plates_zmq()` and `_run_plates_subprocess()`
- New `_run_plates_zmq()` method creates ZMQExecutionClient
- Progress callback updates `status_message` signal
- Tracks `current_execution_id` for cancellation
- Stop button with timeout and status polling

**Textual PlateManager** (`openhcs/textual_tui/widgets/plate_manager.py`):
- Split `action_run_plate()` into `_run_plates_zmq()` and `_run_plates_subprocess()`
- New `_run_plates_zmq()` method creates ZMQExecutionClient
- Progress callback updates `app.current_status`
- Tracks `current_execution_id` for cancellation
- Stop button with timeout and status polling

**Subprocess Runner Deprecation** (`openhcs/textual_tui/subprocess_runner.py`):
- Added deprecation notice in module docstring
- Explains benefits of ZMQ execution pattern
- Directs users to ZMQExecutionClient
- Maintained for backward compatibility

### 4. RemoteOrchestrator Refactor ✅

**Changes** (`openhcs/runtime/remote_orchestrator.py`):
- Refactored to be thin wrapper around ZMQExecutionClient
- Eliminated ~100 lines of duplicate code
- Added deprecation warnings (module, class, runtime)
- Maintained backward compatibility
- All methods delegate to ZMQExecutionClient
- Response format conversion for compatibility

## Benefits

### vs Subprocess Runner

| Feature | Subprocess Runner | ZMQ Execution |
|---------|------------------|---------------|
| Communication | Fire-and-forget | Bidirectional |
| Progress Updates | Log file polling | Real-time streaming |
| Cancellation | Forceful kill | Graceful (step boundary) |
| Process Reuse | No | Yes |
| Multi-instance | No | Yes |
| Location | Local only | Local or remote |
| Error Handling | Log parsing | Structured responses |

### Performance

- **Process Reuse**: Server stays alive between executions (vs spawn per run)
- **Reduced I/O**: No pickle file creation/deletion
- **Faster Feedback**: Real-time progress (vs log file polling)
- **Better Resource Management**: Graceful shutdown vs forceful kill

### Developer Experience

- **Unified API**: Same code for local and remote execution
- **Type Safety**: Structured message formats
- **Debugging**: Better error messages and logging
- **Testing**: Easier to test with mock clients/servers

## Usage Examples

### Basic Execution

```python
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient

# Create client (spawns server if needed)
client = ZMQExecutionClient(port=7777, persistent=False)
client.connect(timeout=15)

# Execute pipeline
response = client.execute_pipeline(
    plate_id="/path/to/plate",
    pipeline_steps=pipeline_steps,
    global_config=global_config,
    pipeline_config=pipeline_config
)

# Check result
if response['status'] == 'complete':
    print("Execution completed successfully")
else:
    print(f"Execution failed: {response['message']}")

# Cleanup
client.disconnect()
```

### With Progress Callback

```python
def on_progress(message):
    well_id = message.get('well_id', 'unknown')
    step = message.get('step', 'unknown')
    status = message.get('status', 'unknown')
    print(f"[{well_id}] {step}: {status}")

client = ZMQExecutionClient(
    port=7777,
    progress_callback=on_progress
)
client.connect()
response = client.execute_pipeline(...)
client.disconnect()
```

### With Cancellation

```python
client = ZMQExecutionClient(port=7777)
client.connect()

# Start execution (in background thread)
response = client.execute_pipeline(...)
execution_id = response['execution_id']

# Cancel if needed
cancel_response = client.cancel_execution(execution_id)
if cancel_response['status'] == 'ok':
    print("Cancellation requested")

client.disconnect()
```

## Migration Guide

### For End Users

**Default behavior** (ZMQ execution):
```bash
# No changes needed - ZMQ is default
python -m openhcs.pyqt_gui.main
```

**Opt-out** (legacy subprocess):
```bash
export OPENHCS_USE_ZMQ_EXECUTION=false
python -m openhcs.pyqt_gui.main
```

### For Developers

**Old pattern** (deprecated):
```python
from openhcs.runtime.remote_orchestrator import RemoteOrchestrator

orchestrator = RemoteOrchestrator('server-host', 7777)
response = orchestrator.run_remote_pipeline(...)
```

**New pattern** (recommended):
```python
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient

client = ZMQExecutionClient(host='server-host', port=7777)
client.connect()
response = client.execute_pipeline(...)
client.disconnect()
```

## Known Limitations

1. **Cancellation Granularity**: Only checked at step boundaries, not mid-step
2. **Long-Running Steps**: Cannot be interrupted during execution
3. **Shared Cancel Event**: All worker processes share same event (cancels all axes)
4. **No Forceful Kill Fallback**: Timeout is informational only (no automatic kill)
5. **Progress Bar Integration**: Progress callbacks update status text, not actual progress bars

## Future Enhancements

1. **Per-Axis Cancellation**: Individual cancel events for each axis
2. **Forceful Kill Fallback**: Automatic process termination after timeout
3. **Progress Bar Widgets**: Wire callbacks to actual QProgressBar/Textual ProgressBar
4. **Mid-Step Cancellation**: Check cancellation flag during long-running operations
5. **Execution History**: Track completed executions for debugging
6. **Metrics Collection**: Execution time, resource usage, etc.

## Testing

**Test Scripts**:
- `examples/test_zmq_execution_pattern.py`: Basic functionality test
- `examples/test_zmq_with_real_plate.py`: End-to-end test with real plate

**Integration Tests**:
- UI integration tested manually with PyQt and Textual
- Cancellation tested with both threading and multiprocessing modes
- Progress streaming verified with background thread listener

## Documentation

- **Architecture**: `docs/zmq_execution_pattern.md` (330 lines)
- **Plan Files**: `plans/execution/plan_01_zmq_execution_pattern.md` through `plan_05_remote_orchestrator_refactor.md`
- **This Summary**: `docs/zmq_execution_implementation_summary.md`

## Conclusion

The ZMQ execution pattern is now fully implemented and integrated into OpenHCS. It provides a modern, robust, and feature-rich execution system that works seamlessly for both local and remote execution. The implementation maintains backward compatibility while offering significant improvements in communication, progress tracking, and cancellation support.

All core functionality is complete and working. Future enhancements will focus on refinements like per-axis cancellation, forceful kill fallback, and progress bar integration.

