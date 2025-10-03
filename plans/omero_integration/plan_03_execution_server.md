# plan_03_execution_server.md
## Component: OpenHCS Execution Server (Based on SubprocessRunner)

### Objective
Create a server daemon that listens for pipeline execution requests via ZeroMQ and executes them on behalf of remote clients. This is based on the existing `subprocess_runner.py` pattern but adapted for network communication instead of file-based IPC.

### Plan

1. **Create `OpenHCSExecutionServer` class** in `openhcs/runtime/execution_server.py`
   - Based on `subprocess_runner.py` execution pattern
   - Use ZeroMQ REQ/REP for command protocol (not file-based pickle)
   - Support multiple concurrent executions (thread pool)
   - Maintain server state (running, idle, error)

2. **Implement server initialization**
   - Accept `omero_data_dir: Path` - path to OMERO binary repository
   - Accept `port: int = 7777` - ZeroMQ listening port
   - Create OMERO connection (BlitzGateway)
   - Initialize `OMEROLocalBackend` and register in storage registry
   - Create FileManager with OMERO backend
   - Set up ZeroMQ REP socket: `tcp://*:{port}`

3. **Implement main server loop** (`run()` method)
   - Listen for execution requests (blocking)
   - Receive request: `{plate_id, pipeline_code, config_code, client_address}`
   - Validate request structure
   - Execute pipeline in background thread
   - Send immediate acknowledgment response
   - Stream results to client address

4. **Implement pipeline execution** (`_execute_pipeline()` method)
   - **Reuse `subprocess_runner.run_single_plate()` pattern but with code execution**
   - Execute pipeline code: `exec(pipeline_code, namespace)`
   - Extract pipeline: `pipeline_steps = namespace['pipeline_steps']`
   - Execute config code: `exec(config_code, namespace)`
   - Extract config: `config = namespace['config']`
   - Create `PipelineOrchestrator` with OMERO backend
   - Initialize orchestrator
   - **Compile pipeline on server** (knows GPU topology, paths, backends)
   - Execute compiled plate
   - Handle errors and log to server log file

5. **Implement result streaming**
   - Modify `NapariStreamingConfig` in pipeline steps to point to client address
   - Use existing `NapariStreamingBackend` for streaming (no changes needed)
   - Client receives results via ZeroMQ SUB socket (same as Napari pattern)

6. **Implement request/response protocol**

   **Request format** (JSON):
   ```json
   {
     "command": "execute",
     "plate_id": 123,
     "pipeline_code": "# Complete Python code\npipeline_steps = [\n    FunctionStep(...),\n    ...\n]\n",
     "config_code": "config = GlobalPipelineConfig(\n    num_workers=8,\n    ...\n)",
     "client_address": "192.168.1.100:5555"
   }
   ```

   **Response format** (JSON):
   ```json
   {
     "status": "accepted|running|completed|error",
     "execution_id": "uuid",
     "message": "Pipeline execution started",
     "wells_processed": 96
   }
   ```

7. **Implement logging**
   - Server log: `/var/log/openhcs/execution_server.log`
   - Per-execution logs: `/var/log/openhcs/executions/{execution_id}.log`
   - Reuse `subprocess_runner.setup_subprocess_logging()` pattern

8. **Implement graceful shutdown**
   - Handle SIGTERM/SIGINT
   - Wait for running executions to complete
   - Close OMERO connection
   - Close ZeroMQ sockets
   - Clean up resources

9. **Implement health check endpoint**
   - Separate ZeroMQ REP socket on port 7778
   - Respond to ping with server status
   - Include: uptime, active executions, OMERO connection status

10. **Create server startup script** (`openhcs/runtime/start_execution_server.py`)
    - Parse command-line arguments (port, OMERO config)
    - Set up logging
    - Create and start server
    - Handle daemonization (optional)

### Findings

#### SubprocessRunner Pattern

**Current Architecture** (`openhcs/textual_tui/subprocess_runner.py`):
- Standalone script executed via `subprocess.Popen()`
- Receives data via pickle file: `data_file.pkl`
- Logs to dedicated file: `{log_file_base}.log`
- Executes `run_single_plate()` for each plate
- No return value - logs are single source of truth

**Data Structure** (pickled):
```python
{
    'plate_paths': List[str],
    'pipeline_data': Dict[str, {
        'pipeline_definition': List[AbstractStep],
        'compiled_contexts': Dict[str, ProcessingContext]  # Pre-compiled by UI
    }],
    'global_config': GlobalPipelineConfig,
    'effective_configs': Dict[str, PipelineConfig]
}
```

**Key Functions**:
- `setup_subprocess_logging(log_file_path)` - configure logging
- `run_single_plate(plate_path, pipeline_definition, compiled_contexts, global_config, logger, log_file_base, effective_config)` - execute single plate
- `main()` - entry point that loads pickle and calls `run_single_plate()`

**For Execution Server**: Adapt this pattern but:
- Receive via ZeroMQ (not pickle file)
- Receive Python code (not pickled objects)
- **Compile on server** (not receive pre-compiled contexts)
- Execute in background thread (not blocking)

#### Execution Pattern (Adapted for Server)

```python
# 1. Execute pipeline code to reconstruct objects
namespace = {}
exec(pipeline_code, namespace)
pipeline_steps = namespace['pipeline_steps']

# 2. Execute config code
exec(config_code, namespace)
config = namespace['config']

# 3. Create orchestrator with OMERO backend
orchestrator = PipelineOrchestrator(
    plate_path=plate_id,  # OMERO plate ID
    global_config=config,
    storage_registry=storage_registry  # Has OMEROLocalBackend
)

# 4. Initialize orchestrator
orchestrator.initialize()

# 5. Compile pipeline on server (knows GPU topology, paths, backends)
compiled_contexts = orchestrator.compile_pipelines(
    pipeline_definition=pipeline_steps,
    axis_filter=None  # All wells
)

# 6. Execute compiled plate
results = orchestrator.execute_compiled_plate(
    pipeline_definition=pipeline_steps,
    compiled_contexts=compiled_contexts,
    max_workers=config.num_workers,
    visualizer=None,  # Auto-created, streams to client_address
    log_file_base=log_file_base
)
```

**Critical**: Server **compiles** pipeline (not pre-compiled). This ensures correct GPU assignments, paths, and backends for server environment.

#### Code Execution Pattern (Not Serialization)

**Use Python code instead of pickle**:
- Client generates code using `generate_complete_pipeline_steps_code()`
- Server receives code as string
- Server executes code: `exec(code, namespace)`
- Server extracts objects from namespace

**Advantages**:
- **10-100x smaller payload** (code vs pickled objects)
- **Human-readable** (can inspect what's being sent)
- **Server-side compilation** (correct GPU topology, paths, backends)
- **Meaningful errors** (based on server environment, not client)

**Example**:
```python
# Client sends this code string:
pipeline_code = """
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.filters.gaussian_filter import gaussian_filter

pipeline_steps = []
step_1 = FunctionStep(
    func=(gaussian_filter, {'sigma': 2.0}),
    name="gaussian_filter"
)
pipeline_steps.append(step_1)
"""

# Server executes:
namespace = {}
exec(pipeline_code, namespace)
pipeline_steps = namespace['pipeline_steps']
```

#### ZeroMQ REQ/REP Pattern

**Server** (REP socket):
```python
import zmq
context = zmq.Context()
socket = context.socket(zmq.REP)
socket.bind("tcp://*:7777")

while True:
    request = socket.recv_json()
    # Process request
    response = {"status": "accepted"}
    socket.send_json(response)
```

**Client** (REQ socket):
```python
socket = context.socket(zmq.REQ)
socket.connect("tcp://omero-server:7777")
socket.send_json(request)
response = socket.recv_json()
```

#### Threading for Background Execution

Server must respond immediately, execute in background:
```python
import threading

def run():
    while True:
        request = socket.recv_json()
        
        # Start execution in background thread
        execution_thread = threading.Thread(
            target=self._execute_pipeline,
            args=(request,),
            daemon=False  # Keep alive until completion
        )
        execution_thread.start()
        
        # Send immediate response
        socket.send_json({"status": "accepted"})
```

#### OMERO Backend Integration

Server creates OMERO backend and registers it:
```python
from openhcs.io.omero_local import OMEROLocalBackend
from openhcs.io.backend_registry import create_storage_registry

# Create OMERO backend
omero_backend = OMEROLocalBackend(omero_data_dir, omero_conn)

# Register backend
storage_registry = create_storage_registry()
storage_registry['omero_local'] = omero_backend

# Create FileManager
filemanager = FileManager(storage_registry)

# Pass to orchestrator
orchestrator = PipelineOrchestrator(
    plate_path=plate_id,
    global_config=global_config,
    storage_registry=storage_registry
)
```

#### Error Handling Pattern (from subprocess_runner)

**Fail-loud philosophy**:
- No try/except around execution (let errors propagate)
- Log all errors with full traceback
- Return error status in response
- Client handles errors

```python
try:
    results = self._execute_pipeline(request)
    socket.send_json({"status": "completed", "results": results})
except Exception as e:
    logger.error(f"Execution failed: {e}", exc_info=True)
    socket.send_json({"status": "error", "message": str(e)})
```

### Implementation Draft

(Code will be written here after smell loop approval)

