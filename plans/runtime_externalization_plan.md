# Runtime Externalization Plan

Extract a **complete distributed execution framework** from `openhcs/runtime/`
into a standalone `zmqruntime` package. Maximize generic abstractions.

## Philosophy

The current code mixes **generic patterns** with **openhcs-specific implementations**.
We can extract MORE than just transport utilities by creating ABCs for the patterns.

**Generic patterns to extract:**
- Message protocol (already generic)
- Transport layer (already generic)
- Queue-based execution server pattern
- Submit/poll/wait client pattern
- Streaming visualizer pattern
- Shape types and ROI converters

**OpenHCS provides only:**
- Concrete implementations that wire up orchestrator, config, FileManager

## Tiered Analysis

### TIER 1: Core Transport (100% generic, no abstraction needed)

| File | Notes |
|------|-------|
| `zmq_messages.py` | Message protocol - no openhcs imports |
| `queue_tracker.py` | Queue tracking - no openhcs imports |
| `zmq_base.py` | Server/Client ABCs - needs 4 small abstractions |

### TIER 2: Execution Pattern (generic with ABC extraction)

| File | Generic Pattern | OpenHCS-Specific Part |
|------|-----------------|----------------------|
| `zmq_execution_server.py` | Queue-based execution, worker thread, status tracking, progress streaming | `_execute_pipeline()` calls orchestrator |
| `zmq_execution_client.py` | Progress listener, submit/poll/wait flow | `serialize_task()` uses pickle_to_python |

**Abstraction:**
```python
class ExecutionServer(ZMQServer, ABC):
    """Queue-based execution server with progress streaming."""

    @abstractmethod
    def execute_task(self, execution_id: str, request: ExecuteRequest) -> Any:
        """Execute a task. Implementation provides actual execution logic."""
        pass

class ExecutionClient(ZMQClient, ABC):
    """Execution client with progress streaming."""

    @abstractmethod
    def serialize_task(self, task: Any, config: Any) -> dict:
        """Serialize task for transmission. Implementation provides serialization."""
        pass
```

### TIER 3: Streaming Pattern (generic with ABC extraction)

| File | Generic Pattern | OpenHCS-Specific Part |
|------|-----------------|----------------------|
| `napari_stream_visualizer.py` | ZMQ image receiver, process management, ack sending | FileManager, NapariStreamingConfig |
| `fiji_viewer_server.py` | ZMQ image receiver, ImageJ display | openhcs streaming constants |
| `fiji_stream_visualizer.py` | Process launch/stop, health check | openhcs config for paths |

**Abstraction:**
```python
class StreamingVisualizerServer(ZMQServer, ABC):
    """Streaming server that receives and displays images."""

    @abstractmethod
    def display_image(self, image_data: np.ndarray, metadata: dict) -> None:
        """Display received image. Implementation provides display logic."""
        pass

class VisualizerProcessManager(ABC):
    """Manages visualizer subprocess lifecycle."""

    @abstractmethod
    def get_launch_command(self) -> List[str]:
        """Get command to launch visualizer. Implementation provides command."""
        pass
```

### TIER 4: Shape Types (generic - no openhcs concepts)

| File | Generic Pattern | OpenHCS-Specific Part |
|------|-----------------|----------------------|
| `roi_converters.py` | Shape types (Polygon, Point, Ellipse), coordinate transforms, napari/ImageJ format conversion | Imports from `openhcs.core.roi` |

**Abstraction:**
The shape types themselves are generic! Polygon, Point, Ellipse, Polyline are universal.

```python
# Generic shape protocol
class ShapeProtocol(Protocol):
    """Protocol that any shape class can implement."""
    pass

@dataclass
class PolygonShape:
    coordinates: np.ndarray  # (N, 2) array of (y, x)

@dataclass
class PointShape:
    y: float
    x: float
```

`openhcs.core.roi` can inherit from these OR just implement the protocol.

### Truly OpenHCS-Specific (stays in openhcs)

| File | Why |
|------|-----|
| `execution_server.py` (legacy) | Deprecated, heavy openhcs deps |
| `zmq_execution_server_launcher.py` | CLI entry point for openhcs |
| `omero_instance_manager.py` | OMERO-specific docker management |
| `remote_orchestrator.py` | Deprecated wrapper |

## Target Package: `zmqruntime`

Complete distributed execution framework. No domain-specific claims.

### Package Structure

```
external/zmqruntime/
├── pyproject.toml
├── zmqruntime/
│   ├── __init__.py
│   ├── config.py              # TransportMode, ZMQConfig
│   ├── messages.py            # Message protocol
│   ├── transport.py           # URL generation, IPC handling
│   ├── server.py              # ZMQServer ABC
│   ├── client.py              # ZMQClient ABC
│   ├── queue_tracker.py       # QueueTracker, GlobalQueueTrackerRegistry
│   ├── ack_listener.py        # Global ack listener
│   │
│   ├── execution/             # TIER 2: Execution pattern
│   │   ├── __init__.py
│   │   ├── server.py          # ExecutionServer ABC (queue-based)
│   │   └── client.py          # ExecutionClient ABC (submit/poll/wait)
│   │
│   ├── streaming/             # TIER 3: Streaming pattern
│   │   ├── __init__.py
│   │   ├── server.py          # StreamingVisualizerServer ABC
│   │   └── process_manager.py # VisualizerProcessManager ABC
│   │
│   └── shapes/                # TIER 4: Shape types
│       ├── __init__.py
│       ├── types.py           # Generic shape dataclasses
│       ├── napari.py          # Napari format converter
│       └── imagej.py          # ImageJ format converter
```

### Dependencies

```toml
[project]
dependencies = [
    "pyzmq>=22.0",
    "numpy>=1.20",
]

[project.optional-dependencies]
registry = ["object-state"]   # For AutoRegisterMeta (optional)
napari = ["napari", "qtpy"]   # For napari converter
imagej = ["roifile"]          # For ImageJ ROI conversion
```

### Public API

```python
# Core (Tier 1)
from zmqruntime import (
    TransportMode, ZMQConfig,
    ControlMessageType, ResponseType, ExecutionStatus, MessageFields,
    ZMQServer, ZMQClient,
    QueueTracker, GlobalQueueTrackerRegistry,
    get_zmq_transport_url, get_ipc_socket_path,
)

# Execution (Tier 2)
from zmqruntime.execution import ExecutionServer, ExecutionClient

# Streaming (Tier 3)
from zmqruntime.streaming import StreamingVisualizerServer, VisualizerProcessManager

# Shapes (Tier 4)
from zmqruntime.shapes import PolygonShape, PointShape, EllipseShape, PolylineShape
from zmqruntime.shapes.napari import NapariShapeConverter
from zmqruntime.shapes.imagej import ImageJROIConverter
```

## Implementation Plan

### Phase 1: Create package skeleton

1. Create `external/zmqruntime/` directory structure
2. Create `pyproject.toml` with deps and optional extras
3. Create empty modules for all tiers

### Phase 2: Extract Tier 1 (Core Transport)

1. **config.py**: TransportMode enum and ZMQConfig
2. **messages.py**: Copy zmq_messages.py verbatim
3. **queue_tracker.py**: Copy queue_tracker.py verbatim
4. **transport.py**: Extract URL generation from zmq_base.py
5. **server.py**: Extract ZMQServer ABC (make AutoRegisterMeta optional)
6. **client.py**: Extract ZMQClient ABC
7. **ack_listener.py**: Extract with callback registration pattern

### Phase 3: Extract Tier 2 (Execution Pattern)

1. **execution/server.py**: Extract ExecutionServer ABC
   - Move queue worker logic from zmq_execution_server.py
   - Move active executions tracking
   - Move progress queue management
   - Leave `execute_task()` as abstract

2. **execution/client.py**: Extract ExecutionClient ABC
   - Move progress listener from zmq_execution_client.py
   - Move submit/poll/wait pattern
   - Leave `serialize_task()` as abstract

### Phase 4: Extract Tier 3 (Streaming Pattern)

1. **streaming/server.py**: Extract StreamingVisualizerServer ABC
   - Move ZMQ image receiver logic from napari_stream_visualizer.py
   - Move ack sending logic
   - Leave `display_image()` as abstract

2. **streaming/process_manager.py**: Extract VisualizerProcessManager ABC
   - Move subprocess management from fiji_stream_visualizer.py
   - Move health checking logic
   - Leave `get_launch_command()` as abstract

### Phase 5: Extract Tier 4 (Shapes)

1. **shapes/types.py**: Generic shape dataclasses
   ```python
   @dataclass
   class PolygonShape:
       coordinates: np.ndarray  # (N, 2) array of (y, x)
       metadata: dict = field(default_factory=dict)

   @dataclass
   class PointShape:
       y: float
       x: float
       metadata: dict = field(default_factory=dict)
   ```

2. **shapes/napari.py**: NapariShapeConverter
   - Move from roi_converters.py
   - Work with generic shape types

3. **shapes/imagej.py**: ImageJROIConverter
   - Move from roi_converters.py
   - Work with generic shape types

### Phase 6: Update openhcs

1. Add `zmqruntime` to openhcs dependencies

2. Create concrete implementations:
   ```python
   # openhcs/runtime/zmq_execution_server.py
   from zmqruntime.execution import ExecutionServer

   class OpenHCSExecutionServer(ExecutionServer):
       def execute_task(self, execution_id, request):
           # Use orchestrator, config, etc.
           return self._execute_pipeline(...)
   ```

3. Update `openhcs/core/roi.py`:
   - Either inherit from zmqruntime shape types
   - Or implement the shape protocol

4. Register UI callback for ack listener

### Phase 7: Clean up

1. Remove duplicated code from openhcs/runtime/
2. Update all import sites
3. Verify `rg "from openhcs" external/zmqruntime/` returns nothing

## What Stays in openhcs/runtime/

After extraction, these concrete implementations remain:

| File | What It Does |
|------|--------------|
| `zmq_execution_server.py` | `OpenHCSExecutionServer(ExecutionServer)` - wires up orchestrator |
| `zmq_execution_client.py` | `OpenHCSExecutionClient(ExecutionClient)` - wires up pickle_to_python |
| `zmq_execution_server_launcher.py` | CLI entry point for openhcs |
| `napari_stream_visualizer.py` | `OpenHCSNapariVisualizer(StreamingVisualizerServer)` - wires up FileManager |
| `fiji_viewer_server.py` | `OpenHCSFijiViewer(StreamingVisualizerServer)` - wires up fiji config |
| `fiji_stream_visualizer.py` | `OpenHCSFijiProcessManager(VisualizerProcessManager)` - wires up paths |
| `omero_instance_manager.py` | OMERO docker management (unchanged) |

## OpenHCS Import Sites to Update

```
openhcs/runtime/*.py                                    # Import base classes from zmqruntime
openhcs/core/roi.py                                     # Inherit from/implement zmqruntime shapes
openhcs/pyqt_gui/widgets/shared/zmq_server_manager.py   # Register ack callback
openhcs/pyqt_gui/widgets/shared/services/zmq_execution_service.py
openhcs/io/streaming.py
openhcs/io/napari_stream.py
openhcs/io/fiji_stream.py
```

## Validation

1. **Unit tests for zmqruntime:**
   - Message serialization/deserialization
   - Transport URL generation (TCP/IPC)
   - Queue tracker logic
   - ExecutionServer queue worker (mock execute_task)
   - ExecutionClient submit/poll flow (mock serialize_task)
   - Shape converters (napari/imagej formats)

2. **Integration tests (openhcs):**
   - Existing `test_main.py` should pass unchanged
   - ZMQ execution flow with concrete OpenHCSExecutionServer
   - Napari/Fiji streaming

3. **Import verification:**
   ```bash
   # zmqruntime has no openhcs imports
   rg "from openhcs" external/zmqruntime/
   rg "import openhcs" external/zmqruntime/
   # Should return nothing
   ```

## Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Package name | `zmqruntime` | Generic, no domain claims |
| Scope | 4 tiers (transport, execution, streaming, shapes) | Maximize reusability |
| AutoRegisterMeta | Optional dep on object_state | Avoid hard dependency |
| UI callback | Registration pattern | No GUI coupling |
| Shape types | Dataclasses in zmqruntime | Generic, openhcs.roi inherits |
| Execution pattern | ABC with abstract execute_task | openhcs provides orchestrator logic |

## Benefits of Tiered Extraction

1. **zmqruntime is a complete framework** - not just transport utilities
2. **openhcs/runtime/ shrinks dramatically** - only concrete wiring
3. **Other projects can use zmqruntime** - for any distributed execution
4. **Shapes are reusable** - any project needing napari/imagej ROI conversion
5. **Clear separation** - generic patterns vs domain logic
