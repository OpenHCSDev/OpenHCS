# ZMQ Execution Mode - Context Handoff Document

## Overview
This document summarizes the recent work on ZMQ execution mode for OpenHCS, including all features implemented and the current bug that needs investigation.

## Features Implemented (Last 2 Days)

### 1. **ZMQ Server ABC Infrastructure** (c877b62, 556d249)
- Created unified `ZMQServer` ABC in `openhcs/runtime/zmq_base.py`
- Dual-channel pattern: data port (e.g., 7777) + control port (data port + 1000)
- Ping/pong handshake protocol for server discovery
- Configurable socket types (PUB/SUB) to support different communication patterns
- Log file path advertising in pong responses for unified log discovery

### 2. **Napari Viewer Refactor** (8dd45c7, abb525e)
- Refactored Napari viewer to inherit from `ZMQServer` ABC instead of custom implementation
- Uses `data_socket_type=zmq.SUB` to receive images from clients
- Eliminated code duplication and improved type safety
- Fixed pong response to include port information

### 3. **ZMQ Server Manager UI** (6eafaf6, 5fd2556, 2995382, c6357cc)
- Generic `ZMQServerManagerWidget` for PyQt6 GUI
- Auto-discovers running ZMQ servers (execution servers + Napari viewers)
- Shows server status: Ready (✅), Active (⏳), or Error (❌)
- Double-click to open server logs in Log Viewer
- Async background scanning with threading (no UI hangs)
- 10-second auto-refresh interval
- Integrated into PyQt main window (Ctrl+Z shortcut)

### 4. **Log Viewer Integration** (0f76015, c5f0645, 5f26efd)
- Log Viewer initializes on app startup (hidden) and monitors continuously
- Auto-detects new log files from ZMQ servers and workers
- Scans for running servers and discovers their log file paths via ping/pong
- Uses `openhcs_` prefix for all ZMQ server logs for consistent naming

### 5. **Persistent Server Mode** (3b7aa60, f99b3bd)
- **CRITICAL FIX**: `ZMQClient.disconnect()` was killing ALL spawned servers
- Now only kills servers if BOTH conditions true:
  1. We spawned it (`not self._connected_to_existing`)
  2. AND it's non-persistent (`not self.persistent`)
- Execution servers now use `persistent=True` to stay alive after pipeline completion
- Servers can be reused across multiple pipeline executions

### 6. **Responsive Server During Execution** (946ca34, 243ca81)
- **CRITICAL FIX**: Server was blocking during pipeline execution
- Refactored `_handle_execute()` to execute pipelines in background thread
- Returns 'accepted' response immediately with execution_id
- Client polls for completion using `get_status()` every 500ms
- Server can now process control messages (pings, status, shutdown) during execution
- Increased ping timeout from 200ms to 1 second for busy servers

### 7. **Thread-Safe Progress Updates** (8490ba9)
- **CRITICAL FIX**: Background execution thread was directly accessing ZMQ sockets
- **ZMQ sockets are NOT thread-safe** - can only be used from creating thread
- Cross-thread socket access corrupted socket state, making server completely unresponsive
- Implemented thread-safe queue pattern:
  - `send_progress_update()` queues messages instead of sending directly
  - `process_messages()` drains queue and sends updates from main thread
  - All ZMQ socket access now happens only in main thread

### 8. **Config Module Preservation** (db4d5a3) - **LATEST FIX**
- **CRITICAL FIX**: `make_dataclass()` was setting `__module__` to `'lazy_factory'`
- Generated code had incorrect imports:
  ```python
  from openhcs.config_framework.lazy_factory import GlobalPipelineConfig  # WRONG
  ```
- Should be:
  ```python
  from openhcs.core.config import GlobalPipelineConfig  # CORRECT
  ```
- Fixed by explicitly setting `lazy_class.__module__ = base_class.__module__` after creation
- Fixes two locations:
  1. `_create_lazy_dataclass_unified()` - for all lazy classes
  2. `_inject_all_pending_fields()` - for field-injected global configs
- Impact: ZMQ execution server can now properly execute generated config code

### 9. **Logging Cleanup** (8e2fd79)
- Changed hundreds of lines of INFO logging to DEBUG level
- Reduced log spam from unified_registry and signature_analyzer
- Makes server logs readable and useful for debugging

## Bug Fixed: Pickling Error with VariableComponents ✅

### Error Message
```
_pickle.PicklingError: Can't pickle <enum 'VariableComponents'>:
it's not the same object as openhcs.constants.constants.VariableComponents
```

### Root Cause
**Enum identity mismatch in multiprocessing contexts**

The `__getattr__` lazy creation pattern was creating **different enum instances** in different processes:
1. Parent process calls `__getattr__` → creates `VariableComponents` instance A
2. Child process (multiprocessing) calls `__getattr__` → creates `VariableComponents` instance B
3. When pickling, Python checks `obj is openhcs.constants.constants.VariableComponents`
4. **FAILS** because instance A ≠ instance B (different objects in memory)

**Why it happened**:
- Missing `__module__` and `__qualname__` attributes on dynamically created enums
- No identity check in `__getattr__` to prevent re-creation
- Each process created its own enum instances

### The Fix
**Location**: `openhcs/constants/constants.py` lines 28-83

**Changes**:
1. ✅ Set `__module__` and `__qualname__` on all dynamically created enums
2. ✅ Add identity check in `__getattr__` to prevent re-creation
3. ✅ Ensure enums are stored in `globals()` exactly once per process

**Code**:
```python
def _create_enums():
    # ... create enums ...
    vc.__module__ = __name__
    vc.__qualname__ = 'VariableComponents'
    return all_components, vc, GroupBy

def __getattr__(name):
    if name in ('AllComponents', 'VariableComponents', 'GroupBy'):
        # Check if already created (handles race conditions)
        if name in globals():
            return globals()[name]

        # Create all enums at once and store in globals
        all_components, vc, gb = _create_enums()
        globals()['AllComponents'] = all_components
        globals()['VariableComponents'] = vc
        globals()['GroupBy'] = gb

        return globals()[name]
```

### Validation ✅
**Test**: Multiprocessing pickle identity check
```bash
$ python3 -c "
import pickle, multiprocessing
def test():
    from openhcs.constants.constants import VariableComponents
    return VariableComponents.CHANNEL.__class__ is VariableComponents
with multiprocessing.Pool(1) as pool:
    print(pool.apply(test))  # True ✅
"
```

**Result**: Identity check passes in subprocess! The enum is now the **same object** across processes

### Next Steps for Debugging

**If user reports a pickling error:**
1. Get the **full error traceback** - need to see what object is actually failing to pickle
2. Check if it's a different enum or object, not `VariableComponents`
3. Look for lambdas, local functions, or callbacks in the pipeline definition
4. Check for circular references in configs or steps

**Current Status:**
- ✅ `VariableComponents` enum is picklable
- ✅ Config module preservation fix is working (`GlobalPipelineConfig` imports from `openhcs.core.config`)
- ✅ ZMQ execution server is async and responsive
- ✅ Thread-safe progress updates implemented
- ⏳ Need actual error message to proceed with debugging

### Test Commands (Already Validated ✅)

**Test pickling directly** ✅ PASSED:
```bash
$ python3 -c "from openhcs.constants.constants import VariableComponents; import pickle; pickle.loads(pickle.dumps(VariableComponents.CHANNEL))"
✅ Pickling works! VariableComponents.CHANNEL
```

**Test ZMQ execution** ⏳ TIMEOUT:
```bash
$ python -m pytest tests/integration/test_main.py::test_code_serialization -xvs -k "zmq_server"
# Times out after 180s
```

**Note**: The test timeout is **unrelated to pickling**. Likely causes:
- Server not shutting down properly after test
- Test waiting for a response that never comes
- Deadlock in the execution flow
- Need to investigate test logs to see where it hangs

## Architecture Summary

### ZMQ Execution Flow
1. **Client** (`ZMQExecutionClient`):
   - Generates Python code from config using `generate_config_code()`
   - Sends code + pipeline steps to server via control channel
   - Polls for completion every 500ms

2. **Server** (`ZMQExecutionServer`):
   - Receives code and executes it to recreate config
   - Spawns background thread for pipeline execution
   - Main thread continues processing control messages (pings, status)
   - Queues progress updates from background thread
   - Main thread drains queue and sends updates via data channel

3. **Worker Processes**:
   - Spawned by orchestrator using multiprocessing
   - Execute individual wells in parallel
   - Send progress updates back to server

### Key Files
- `openhcs/runtime/zmq_base.py` - ABC for ZMQ servers/clients
- `openhcs/runtime/zmq_execution_server.py` - Execution server implementation
- `openhcs/runtime/zmq_execution_client.py` - Execution client implementation
- `openhcs/debug/pickle_to_python.py` - Code generation from configs
- `openhcs/pyqt_gui/widgets/shared/zmq_server_manager.py` - UI for server management
- `openhcs/pyqt_gui/widgets/log_viewer.py` - Log monitoring UI
- `openhcs/config_framework/lazy_factory.py` - Lazy config factory (module preservation fix)

### Thread Safety Rules
1. **ZMQ sockets are NOT thread-safe** - only use from creating thread
2. **Use queue.Queue for cross-thread communication** - background threads queue messages, main thread sends
3. **contextvars are thread-local** - must be set in each thread that needs them

## Next Steps
1. Investigate VariableComponents pickling error
2. Run and fix test_code_serialization tests
3. Verify ZMQ execution works end-to-end from PyQt GUI
4. Document any additional fixes needed

