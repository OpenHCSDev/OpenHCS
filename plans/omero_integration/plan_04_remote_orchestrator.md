# plan_04_remote_orchestrator.md
## Component: Remote Orchestrator Client

### Objective
Create a client-side orchestrator that sends pipeline execution requests to the remote OMERO server and receives streamed results. This provides a local interface that feels like normal OpenHCS usage but executes remotely.

### Plan

1. **Create `RemoteOrchestrator` class** in `openhcs/runtime/remote_orchestrator.py`
   - Client-side wrapper for remote execution
   - Mimics `PipelineOrchestrator` interface for familiarity
   - Handles serialization and network communication
   - Manages result streaming

2. **Implement initialization**
   - Accept `server_host: str` - OMERO server hostname/IP
   - Accept `server_port: int = 7777` - execution server port
   - Accept `omero_conn: BlitzGateway` - OMERO connection for metadata queries
   - Create ZeroMQ REQ socket: `tcp://{server_host}:{server_port}`
   - Verify server is reachable (ping/pong handshake)

3. **Implement `execute_remote()` method**
   - Accept same parameters as `PipelineOrchestrator.run_pipeline()`
   - Generate Python code from pipeline using `generate_complete_pipeline_steps_code()`
   - Generate Python code from config using `generate_config_code()`
   - Get local IP for result streaming
   - Send execution request to server (code as strings, not pickled objects)
   - Wait for acknowledgment
   - Return execution ID

4. **Implement result streaming receiver**
   - Start local ZeroMQ SUB socket on specified port
   - Reuse `NapariStreamVisualizer` pattern for receiving
   - Display results in local Napari viewer
   - Or: save results to local disk
   - Or: forward to custom callback

5. **NO compilation on client side**
   - **Server compiles pipeline** (knows its own GPU topology, paths, backends)
   - Client only generates Python code representation
   - Server executes code to reconstruct pipeline objects
   - Server compiles and executes in its own environment

6. **Implement helper methods**
   - `_generate_pipeline_code(pipeline)` - use `generate_complete_pipeline_steps_code()`
   - `_generate_config_code(config)` - use `generate_config_code()`
   - `_get_local_ip()` - determine local IP for streaming
   - `_start_result_receiver(port)` - start ZeroMQ SUB socket

7. **Implement high-level convenience method** (`run_remote_pipeline()`)
   ```python
   def run_remote_pipeline(
       self,
       plate_id: int,
       pipeline: List[AbstractStep],
       config: PipelineConfig,
       viewer_port: int = 5555
   ):
       """
       High-level method that handles:
       1. Generate Python code from pipeline and config
       2. Send code to server for execution
       3. Server compiles and executes in its environment
       4. Stream results to local viewer
       """
   ```

8. **Implement error handling**
   - Timeout if server doesn't respond (30s default)
   - Retry logic for transient network errors (3 retries)
   - Fail loudly if server returns error status
   - Display error messages from server

9. **Implement progress monitoring**
   - Poll server for execution status (optional)
   - Display progress in local UI
   - Estimate completion time based on wells processed

10. **Create example usage script** (`examples/omero_remote_execution.py`)
    - Connect to OMERO server
    - Query for plate
    - Define pipeline
    - Execute remotely
    - Display results

### Findings

#### PipelineOrchestrator Interface

**Key Methods** (`openhcs/core/orchestrator/orchestrator.py`):
```python
class PipelineOrchestrator:
    def __init__(self, plate_path, pipeline_config=None, storage_registry=None):
        ...
    
    def initialize(self):
        """Initialize orchestrator (parse metadata, create filemanager)."""
        ...
    
    def compile_pipelines(self, pipeline_definition, axis_filter=None):
        """Compile pipeline for all axis values."""
        ...
    
    def execute_compiled_plate(self, pipeline_definition, compiled_contexts, max_workers=None):
        """Execute pre-compiled pipeline."""
        ...
```

**RemoteOrchestrator should mimic this interface** for familiarity.

#### Compilation Must Happen Server-Side

**Why**: Server knows its own execution environment
- Server knows GPU topology (how many GPUs, which are free)
- Server knows OMERO binary repository paths
- Server has `OMEROLocalBackend` registered
- Errors are based on actual execution environment (meaningful for debugging)

**Client sends Python code**:
- Client generates code using `generate_complete_pipeline_steps_code()`
- Server executes code: `exec(pipeline_code, namespace)`
- Server extracts pipeline: `pipeline_steps = namespace['pipeline_steps']`
- Server compiles in its own environment
- Server executes with correct GPU assignments, paths, backends

#### Code Generation (Not Serialization)

**Use existing OpenHCS UI↔code conversion**:
```python
from openhcs.debug.pickle_to_python import (
    generate_complete_pipeline_steps_code,
    generate_config_code
)

# Generate pipeline code
pipeline_code = generate_complete_pipeline_steps_code(
    pipeline_steps=pipeline_steps,
    clean_mode=True  # Only non-default values
)

# Generate config code
config_code = generate_config_code(
    config=config,
    config_class=GlobalPipelineConfig,
    clean_mode=True
)
```

**Payload size**:
- Python code: ~10-100 KB (small, human-readable)
- Pickled contexts: ~1-10 MB (large, opaque)
- **10-100x smaller** with code approach

#### Local IP Detection

Client needs to tell server where to stream results:
```python
import socket

def get_local_ip(server_host, server_port):
    """Get local IP by connecting to server."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.connect((server_host, server_port))
    local_ip = s.getsockname()[0]
    s.close()
    return local_ip
```

This ensures correct IP even with multiple network interfaces.

#### Result Streaming Pattern

**Same as Napari streaming**:
1. Client starts ZeroMQ SUB socket on port 5555
2. Client sends execution request with `client_address: "192.168.1.100:5555"`
3. Server modifies `NapariStreamingConfig` in pipeline steps to point to client
4. Server executes pipeline, streams results to client
5. Client receives results via SUB socket

**Reuse existing code**:
```python
from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer

viewer = NapariStreamVisualizer(
    filemanager=None,  # Not needed for receiving
    viewer_title="OMERO Remote Results",
    port=5555
)
viewer.start_viewer()
```

#### OMERO Metadata Queries

Client needs plate metadata for compilation:
```python
from omero.gateway import BlitzGateway

conn = BlitzGateway(username, password, host=host, port=4064)
conn.connect()

# Get plate
plate = conn.getObject("Plate", plate_id)

# Get wells
wells = []
for well in plate.listChildren():
    wells.append(well.getWellPos())  # e.g., "A01"

# Get channels
image = plate.getWell(0).getImage(0)
channels = []
for c in range(image.getSizeC()):
    channels.append(image.getChannelLabel(c))
```

This metadata is used to create `ProcessingContext` for each well.

#### Error Handling Pattern

**Network errors**:
- Connection refused → server not running
- Timeout → server overloaded or crashed
- Connection reset → server crashed during execution

**Server errors**:
- Response status "error" → execution failed
- Response message contains error details

**Client should**:
- Display error message to user
- Log full error details
- Offer retry option
- Fail loudly (no silent failures)

#### Configuration Code Generation

**Lazy configs are handled by code generation**:
```python
from openhcs.debug.pickle_to_python import generate_config_code

# Generates code with resolved values
config_code = generate_config_code(
    config=config,
    config_class=GlobalPipelineConfig,
    clean_mode=True
)

# Result is executable Python code:
# config = GlobalPipelineConfig(
#     num_workers=8,
#     zarr_config=ZarrConfig(compressor=ZarrCompressor.BLOSC_ZSTD),
#     ...
# )
```

Server executes this code to reconstruct config object.

### Implementation Draft

(Code will be written here after smell loop approval)

