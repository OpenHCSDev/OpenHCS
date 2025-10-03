# plan_02_network_streaming.md
## Component: Network Streaming Backend (Generalized Napari Pattern)

### Objective
Generalize the existing `NapariStreamingBackend` to support remote hosts, enabling streaming from OMERO server to client workstations. This is a trivial change (one line) that unlocks remote execution architecture.

### Plan

1. **Modify `NapariStreamingBackend._get_publisher()` method**
   - Change signature from `_get_publisher(napari_port)` to `_get_publisher(napari_host, napari_port)`
   - Update ZeroMQ connection string from `tcp://localhost:{port}` to `tcp://{host}:{port}`
   - Update publisher cache key from `port` to `f"{host}:{port}"`
   - Update log messages to include host

2. **Update `NapariStreamingConfig` dataclass**
   - Add `napari_host: str = "localhost"` field (default to localhost for backward compatibility)
   - Keep existing `napari_port: int` field
   - Update docstring to mention remote streaming capability

3. **Update all call sites**
   - Modify `save()` method to pass both host and port to `_get_publisher()`
   - Extract host from config: `config.napari_host`
   - Extract port from config: `config.napari_port`

4. **Update `NapariStreamVisualizer` to support binding to specific interface**
   - Modify subscriber socket to bind to `tcp://*:{port}` (all interfaces) instead of `tcp://localhost:{port}`
   - This allows remote connections to reach the visualizer
   - Add `bind_address: str = "*"` parameter to allow restricting to specific interface if needed

5. **Add network streaming documentation**
   - Document remote streaming capability in docstrings
   - Add example of remote execution pattern
   - Note firewall requirements (ports must be open)

### Findings

#### Existing Napari Streaming Architecture

**`NapariStreamingBackend`** (`openhcs/io/napari_stream.py`):
- Inherits from `StreamingBackend` (DataSink without persistence)
- Uses ZeroMQ PUB socket for publishing data
- Current connection: `tcp://localhost:{napari_port}` (line 54)
- Lazy publisher initialization with caching
- JSON message format for metadata + shared memory for large arrays

**`NapariStreamingConfig`** (`openhcs/core/config.py`):
```python
@dataclass
class NapariStreamingConfig:
    enabled: bool = False
    napari_port: int = 5555
    use_shared_memory: bool = True
```

**`NapariStreamVisualizer`** (`openhcs/runtime/napari_stream_visualizer.py`):
- Separate process architecture (Qt event loop isolation)
- ZeroMQ SUB socket for receiving data
- Control socket (REP) for handshake protocol (ping/pong)
- Data socket (SUB) for image streaming
- Current binding: `tcp://localhost:{port}` for both sockets

#### ZeroMQ Network Transparency

ZeroMQ supports both IPC and network sockets with identical API:
- `tcp://localhost:5555` - local loopback
- `tcp://192.168.1.100:5555` - specific IP
- `tcp://omero.server.com:5555` - hostname
- `tcp://*:5555` - bind to all interfaces

**No code changes needed** beyond the connection string - ZeroMQ handles everything.

#### Current Call Sites

**`NapariStreamingBackend.save()`** (line ~80):
```python
publisher = self._get_publisher(config.napari_port)
```

**`NapariStreamingBackend._get_publisher()`** (line 45-64):
```python
def _get_publisher(self, napari_port: int):
    if napari_port not in self._publishers:
        publisher = self._context.socket(zmq.PUB)
        publisher.connect(f"tcp://localhost:{napari_port}")  # <-- CHANGE THIS LINE
        self._publishers[napari_port] = publisher
    return self._publishers[napari_port]
```

#### Backward Compatibility

Default `napari_host = "localhost"` ensures existing code continues to work without changes.
Only remote execution scenarios need to specify a different host.

#### Security Considerations

**Firewall**: Ports must be open for remote streaming
**Authentication**: ZeroMQ doesn't provide authentication - must be handled at application level
**Encryption**: ZeroMQ supports CurveZMQ for encryption (future enhancement)

For initial implementation, assume trusted network (facility LAN).

### Implementation Draft

(Code will be written here after smell loop approval)

