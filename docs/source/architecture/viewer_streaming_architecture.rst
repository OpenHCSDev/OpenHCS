Viewer Streaming Architecture
==============================

Overview
--------

This document describes the technical architecture of OpenHCS's viewer streaming system, which enables cross-process communication with Napari and Fiji/ImageJ viewers.

**Key Design Principles**:

- **Centralized management**: Single orchestrator manages all viewer instances
- **Process isolation**: Viewers run in separate processes to avoid Qt conflicts
- **Automatic reuse**: Viewers are cached and reused across different contexts
- **Type-safe configuration**: Uses ``isinstance()`` checks instead of ``hasattr()``
- **Progressive building**: Images accumulate into hyperstacks instead of replacing
- **Real-time progress tracking**: Acknowledgment system tracks image processing progress
- **Unified code paths**: Images and ROIs share common streaming infrastructure
- **Registry patterns**: Type-safe dispatch using enums instead of if/else chains
- **Abstract class attributes**: Subclasses configure behavior via class-level constants

.. seealso::

   :doc:`image_acknowledgment_system`
      Detailed documentation of the real-time image acknowledgment system

   :doc:`roi_system`
      ROI extraction, materialization, and streaming system

Architecture Components
-----------------------

Streaming Backend ABC
~~~~~~~~~~~~~~~~~~~~~

**Location**: ``openhcs/io/streaming.py``

**Responsibility**: Abstract base class providing common ZeroMQ and shared memory infrastructure

**Key Innovation**: Uses abstract class attributes to eliminate ~237 lines of duplicated code

.. code-block:: python

   class StreamingBackend(DataSink):
       """Abstract base class for ZeroMQ-based streaming backends.

       Subclasses must define abstract class attributes:
       - VIEWER_TYPE: str (e.g., 'napari', 'fiji')
       - HOST_PARAM: str (e.g., 'napari_host', 'fiji_host')
       - PORT_PARAM: str (e.g., 'napari_port', 'fiji_port')
       - SHM_PREFIX: str (e.g., 'napari_', 'fiji_')
       """

       # Abstract class attributes
       VIEWER_TYPE: str = None
       HOST_PARAM: str = None
       PORT_PARAM: str = None
       SHM_PREFIX: str = None

       def _get_publisher(self, host: str, port: int):
           """Lazy initialization of ZeroMQ publisher (common for all backends)."""

       def _parse_component_metadata(self, file_path, microscope_handler, step_name, step_index):
           """Parse component metadata from filename (common for all backends)."""

       def _detect_data_type(self, data: Any):
           """Detect if data is ROI or image (common for all backends)."""

       def _create_shared_memory(self, data: Any, file_path):
           """Create shared memory for image data (common for all backends)."""

       def _register_with_queue_tracker(self, port: int, image_ids: List[str]):
           """Register sent images with queue tracker (common for all backends)."""

**Concrete Implementations**:

.. code-block:: python

   class NapariStreamingBackend(StreamingBackend):
       # Configure ABC attributes
       VIEWER_TYPE = 'napari'
       HOST_PARAM = 'napari_host'
       PORT_PARAM = 'napari_port'
       SHM_PREFIX = 'napari_'

       # Napari-specific ROI preparation
       def _prepare_shapes_data(self, data, file_path):
           """Convert ROIs to Napari shapes format."""

   class FijiStreamingBackend(StreamingBackend):
       # Configure ABC attributes
       VIEWER_TYPE = 'fiji'
       HOST_PARAM = 'fiji_host'
       PORT_PARAM = 'fiji_port'
       SHM_PREFIX = 'fiji_'

       # Fiji-specific ROI preparation
       def _prepare_rois_data(self, data, file_path):
           """Convert ROIs to ImageJ format."""

**Benefits**:

- **Code reuse**: ~93 lines of common code extracted to ABC
- **Type safety**: Abstract class attributes enforce configuration
- **Fail-loud**: Missing attributes raise ``AttributeError`` at class definition time
- **Unified paths**: Images and ROIs share same infrastructure

Orchestrator
~~~~~~~~~~~~

**Location**: ``openhcs/core/orchestrator/orchestrator.py``

**Responsibility**: Central manager for all viewer instances

**Key Data Structure**:

.. code-block:: python

   # Viewers tracked by (backend_name, port) key
   self._visualizers = {
       ('napari', 5555): NapariStreamVisualizer(...),
       ('fiji', 5565): FijiStreamVisualizer(...),  # Non-overlapping with Napari
   }

**Key Method**:

.. code-block:: python

   def get_or_create_visualizer(self, config, vis_config=None):
       """
       Get existing visualizer or create new one.
       
       Args:
           config: NapariStreamingConfig or FijiStreamingConfig
           vis_config: Optional visualizer config
           
       Returns:
           Visualizer instance (reused or newly created)
       """
       # Type-safe viewer detection
       if isinstance(config, NapariStreamingConfig):
           key = ('napari', config.napari_port)
           port = config.napari_port
       elif isinstance(config, FijiStreamingConfig):
           key = ('fiji', config.fiji_port)
           port = config.fiji_port
       else:
           raise ValueError(f"Unknown config type: {type(config)}")
       
       # Check if viewer already exists and is running
       if key in self._visualizers:
           vis = self._visualizers[key]
           if vis.is_running:
               logger.info(f"Reusing existing viewer on port {port}")
               return vis
           else:
               logger.warning(f"Viewer on port {port} is not running, removing from cache")
               del self._visualizers[key]
       
       # Create new viewer
       logger.info(f"Creating new viewer on port {port}")
       vis = config.create_visualizer(self.filemanager, vis_config)
       vis.start_viewer(async_mode=True)
       
       # Ping server in background thread (required for Fiji)
       # This sets _ready = True so server processes data messages
       import threading
       def ping_server():
           import time
           time.sleep(1.0)
           if hasattr(vis, '_wait_for_server_ready'):
               vis._wait_for_server_ready(timeout=10.0)
       
       thread = threading.Thread(target=ping_server, daemon=True)
       thread.start()
       
       # Store in cache
       self._visualizers[key] = vis
       return vis

**Design Rationale**:

- **Single source of truth**: All viewers tracked in one place
- **Automatic reuse**: Prevents duplicate viewers on same port
- **Type-safe**: Uses ``isinstance()`` instead of ``hasattr()`` for better type checking
- **Async startup**: Non-blocking viewer creation with background ping

NapariStreamVisualizer
~~~~~~~~~~~~~~~~~~~~~~

**Location**: ``openhcs/runtime/napari_stream_visualizer.py``

**Responsibility**: Manage Napari viewer processes and ZMQ communication

**Key Features**:

- Spawns Napari in separate process (avoids Qt conflicts with PyQt GUI)
- Uses ZMQ PUB/SUB for data streaming
- Uses ZMQ REQ/REP for control (ping/pong handshake)
- Supports shared memory for efficient image transfer
- Can detect and connect to existing viewers

**ZMQ Architecture**:

.. code-block:: python

   # Data channel (PUB/SUB)
   data_port = 5555
   publisher = zmq.Context().socket(zmq.PUB)
   publisher.bind(f"tcp://127.0.0.1:{data_port}")
   
   # Control channel (REQ/REP)
   control_port = data_port + 1000  # 6555
   control_socket = zmq.Context().socket(zmq.REQ)
   control_socket.connect(f"tcp://127.0.0.1:{control_port}")

**Handshake Protocol**:

.. code-block:: python

   # Client sends ping
   control_socket.send_json({'type': 'ping'})
   
   # Server responds with pong
   response = control_socket.recv_json()
   # {'type': 'pong', 'ready': True}

**Image Streaming**:

.. code-block:: python

   # Create shared memory
   shm = shared_memory.SharedMemory(create=True, size=image.nbytes)
   shm_array = np.ndarray(image.shape, dtype=image.dtype, buffer=shm.buf)
   shm_array[:] = image[:]
   
   # Send metadata via ZMQ
   publisher.send_json({
       'shm_name': shm.name,
       'shape': image.shape,
       'dtype': str(image.dtype),
       'name': 'A01_s001_w1_z001.tif',
       'metadata': {...}
   })

FijiStreamVisualizer
~~~~~~~~~~~~~~~~~~~~

**Location**: ``openhcs/runtime/fiji_stream_visualizer.py``

**Responsibility**: Manage Fiji/ImageJ viewer processes and hyperstack building

**Key Features**:

- Spawns Fiji via PyImageJ in separate process
- Uses same ZMQ pattern as Napari (data + control channels)
- Builds ImageJ hyperstacks with proper dimension mapping
- Supports progressive hyperstack building (images accumulate)
- Stores metadata alongside hyperstacks for merging

**Hyperstack Building**:

.. code-block:: python

   class FijiViewerServer:
       def __init__(self):
           self.hyperstacks = {}  # window_key -> ImagePlus
           self.hyperstack_metadata = {}  # window_key -> list of image dicts
       
       def _build_single_hyperstack(self, window_key, new_images, ...):
           # Check if hyperstack exists
           if window_key in self.hyperstack_metadata:
               # Merge with existing images
               existing_images = self.hyperstack_metadata[window_key]
               
               # Build coordinate lookup
               lookup = {}
               for img in existing_images:
                   coords = self._extract_coordinates(img['metadata'])
                   lookup[coords] = img
               
               # Add new images (override at same coordinates)
               for img in new_images:
                   coords = self._extract_coordinates(img['metadata'])
                   lookup[coords] = img
               
               all_images = list(lookup.values())
           else:
               all_images = new_images
           
           # Build ImageJ hyperstack
           imp = self._create_hyperstack(all_images, ...)
           imp.show()
           
           # Store for future merging
           self.hyperstacks[window_key] = imp
           self.hyperstack_metadata[window_key] = all_images

**Progressive Building Behavior**:

- Send image 1 (B03, z=1) → Creates hyperstack with 1 Z slice
- Send image 2 (B03, z=2) → Merges → Now has 2 Z slices
- Send image 3 (B03, ch=2, z=1) → Merges → Now has 2 Z × 2 channels
- Images at same coordinates override previous images

Image Browser
~~~~~~~~~~~~~

**Location**: ``openhcs/pyqt_gui/widgets/image_browser.py``

**Responsibility**: UI for browsing and streaming images to viewers

**Key Design Changes**:

- **Removed**: Local viewer tracking (``napari_viewers``, ``fiji_viewers`` dicts)
- **Removed**: Pending queue system (``pending_napari_queue``, ``pending_fiji_queue``)
- **Added**: Delegation to orchestrator for all viewer management
- **Added**: Batch streaming for proper hyperstack construction

**Batch Streaming Pattern**:

.. code-block:: python

   def view_selected_in_fiji(self):
       # Collect ALL filenames first
       filenames = [item.data(UserRole) for item in selected_rows]
       
       # Stream as single batch
       self._load_and_stream_batch_to_fiji(filenames)
   
   def _load_and_stream_batch_to_fiji(self, filenames):
       # Load all images
       image_data_list = [filemanager.load(f) for f in filenames]
       
       # Resolve config once
       fiji_config = resolve_lazy_configurations(...)
       
       # Get or create viewer (delegates to orchestrator)
       viewer = orchestrator.get_or_create_visualizer(fiji_config)
       
       # Stream entire batch
       filemanager.save_batch(
           image_data_list, filenames,
           Backend.FIJI_STREAM.value,
           fiji_port=viewer.fiji_port,
           step_name='image_browser',
           microscope_handler=handler
       )

**Why Batch Streaming**:

- Fiji groups images by ``(step_name, well)`` to build hyperstacks
- Each ``save_batch()`` call is treated as a complete batch
- Sending individually → each image is a "complete" batch → separate hyperstacks
- Sending as batch → all images in one batch → single hyperstack with all dimensions

Type-Safe Streaming Enums
~~~~~~~~~~~~~~~~~~~~~~~~~

**Location**: ``openhcs/constants/streaming.py``

**Purpose**: Replace magic strings with type-safe enums

.. code-block:: python

   class StreamingDataType(Enum):
       """Types of data that can be streamed to viewers."""
       IMAGE = 'image'
       SHAPES = 'shapes'  # For Napari
       ROIS = 'rois'      # For Fiji

   class NapariShapeType(Enum):
       """Napari shape types for ROI visualization."""
       POLYGON = 'polygon'
       ELLIPSE = 'ellipse'
       POINT = 'point'
       LINE = 'line'
       PATH = 'path'
       RECTANGLE = 'rectangle'

**Benefits**:

- **Type safety**: IDE autocomplete and type checking
- **Fail-loud**: Invalid values raise ``AttributeError`` instead of silent bugs
- **Registry keys**: Used as dictionary keys for handler dispatch

ROI Converter Registry
~~~~~~~~~~~~~~~~~~~~~~~

**Location**: ``openhcs/runtime/roi_converters.py``

**Purpose**: Single source of truth for ROI format conversion

.. code-block:: python

   class NapariROIConverter:
       """Convert OpenHCS ROIs to Napari shapes format."""

       # Registry of shape type handlers for adding dimensions
       _SHAPE_DIMENSION_HANDLERS = {
           'polygon': lambda shape_dict, prepend_dims: ...,
           'ellipse': lambda shape_dict, prepend_dims: ...,
           'point': lambda shape_dict, prepend_dims: ...,
       }

       @staticmethod
       def add_dimensions_to_shape(shape_dict, prepend_dims):
           """Add dimensions to 2D shape to make it nD."""
           handler = NapariROIConverter._SHAPE_DIMENSION_HANDLERS.get(shape_type)
           return handler(shape_dict, prepend_dims)

   class FijiROIConverter:
       """Convert OpenHCS ROIs to ImageJ ROI format."""

       @staticmethod
       def rois_to_imagej_bytes(rois, roi_prefix=""):
           """Convert ROI objects to ImageJ ROI bytes."""

       @staticmethod
       def encode_rois_for_transmission(roi_bytes_list):
           """Base64 encode ROI bytes for JSON transmission."""

**Benefits**:

- **Single source of truth**: All ROI conversion logic in one place
- **Registry pattern**: Shape handlers dispatched via dictionary lookup
- **Reusability**: Used by both backends and viewer servers
- **Testability**: Isolated conversion logic easy to unit test

Communication Protocols
-----------------------

ZMQ Dual-Channel Pattern
~~~~~~~~~~~~~~~~~~~~~~~~~

Both Napari and Fiji use the same ZMQ communication pattern:

**Data Channel** (PUB/SUB):

- Port: User-specified (e.g., 5555 for Napari, 5556 for Fiji)
- Pattern: Publisher (client) → Subscriber (viewer)
- Purpose: Stream image data and metadata
- Transport: Shared memory for images, ZMQ for metadata

**Control Channel** (REQ/REP):

- Port: Data port + 1000 (e.g., 6555 for Napari, 6556 for Fiji)
- Pattern: Request (client) → Reply (viewer)
- Purpose: Handshake, status checks, control commands
- Transport: ZMQ JSON messages

**Socket Configuration**:

.. code-block:: python

   # Both channels use LINGER=0 to free ports immediately
   socket.setsockopt(zmq.LINGER, 0)

   # Control channel uses short timeout for non-blocking checks
   socket.setsockopt(zmq.RCVTIMEO, 1000)  # 1 second

Ping/Pong Handshake
~~~~~~~~~~~~~~~~~~~~

**Purpose**: Verify viewer is ready before streaming images

**Protocol**:

.. code-block:: python

   # Client sends ping
   control_socket.send_json({'type': 'ping'})

   # Viewer responds with pong
   response = control_socket.recv_json()
   # {'type': 'pong', 'ready': True}

**Fiji Requirement**:

- Fiji server requires ping to set ``_ready = True``
- Without ping, server ignores data messages
- Orchestrator sends ping in background thread after async startup

Metadata Key Standardization
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Inconsistent metadata key names caused ``KeyError`` bugs

**Before**:

- Napari backend sent ``'component_metadata'``
- Fiji backend sent ``'metadata'``
- zmq_base.py loader expected ``'component_metadata'``
- Servers had inconsistent expectations

**After**: All code uses ``'metadata'`` key

.. code-block:: python

   # Backends send 'metadata'
   batch_images.append({
       'data_type': data_type.value,
       'metadata': component_metadata,  # Standardized key
       'image_id': image_id
   })

   # Servers read 'metadata'
   metadata = image_info.get('metadata', {})
   channel_idx = metadata['channel']  # Fail loud if missing

**Benefits**:

- **Consistency**: Single key name across all components
- **Fail-loud**: Missing metadata raises ``KeyError`` immediately
- **Debuggability**: Clear error messages instead of silent defaults

Unified Image/ROI Code Paths
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Separate code paths for images and ROIs led to duplication

**Solution**: Unified processing with type-based dispatch

.. code-block:: python

   # Backend: Unified save_batch for both images and ROIs
   def save_batch(self, data_list, file_paths, **kwargs):
       for data, file_path in zip(data_list, file_paths):
           # Detect data type using ABC helper
           data_type = self._detect_data_type(data)

           # Parse metadata ONCE for all types
           metadata = self._parse_component_metadata(file_path, ...)

           # Prepare data based on type
           if data_type == StreamingDataType.SHAPES:
               item_data = self._prepare_shapes_data(data, file_path)
           else:  # IMAGE
               item_data = self._create_shared_memory(data, file_path)

           # Build batch item (same structure for all types)
           batch_images.append({
               **item_data,
               'data_type': data_type.value,
               'metadata': metadata,
               'image_id': image_id
           })

   # Server: Registry-based dispatch
   _DATA_TYPE_HANDLERS = {
       StreamingDataType.IMAGE: _handle_images_for_window,
       StreamingDataType.ROIS: _handle_rois_for_window,
   }

   handler = _DATA_TYPE_HANDLERS[data_type]
   handler(window_key, items, ...)

**Benefits**:

- **Code reuse**: Metadata parsing happens once for all types
- **Type safety**: Enum-based dispatch instead of string checks
- **Extensibility**: New data types just add registry entry
- **Maintainability**: Changes to common logic affect all types

Shared Memory Transfer
~~~~~~~~~~~~~~~~~~~~~~~

**Purpose**: Efficient transfer of large image arrays

**Process**:

1. Client creates shared memory segment
2. Client copies image data to shared memory
3. Client sends metadata via ZMQ (includes shared memory name)
4. Viewer reads image from shared memory using name
5. Viewer unlinks shared memory when done

**Code Example**:

.. code-block:: python

   # Client side
   shm = shared_memory.SharedMemory(create=True, size=image.nbytes)
   shm_array = np.ndarray(image.shape, dtype=image.dtype, buffer=shm.buf)
   shm_array[:] = image[:]

   publisher.send_json({
       'shm_name': shm.name,
       'shape': image.shape,
       'dtype': str(image.dtype),
       'name': filename,
       'metadata': metadata
   })

   # Viewer side
   shm = shared_memory.SharedMemory(name=msg['shm_name'])
   image = np.ndarray(msg['shape'], dtype=msg['dtype'], buffer=shm.buf).copy()
   shm.close()
   shm.unlink()

**Benefits**:

- No serialization overhead (direct memory access)
- No ZMQ message size limits
- Minimal CPU usage for large images

Viewer Lifecycle
----------------

Startup Sequence
~~~~~~~~~~~~~~~~

.. code-block:: text

   ┌──────────────────────────────────────────────────────────┐
   │ User Action: Stream Image or Run Pipeline                │
   └──────────────────────────────────────────────────────────┘
                          ↓
   ┌──────────────────────────────────────────────────────────┐
   │ orchestrator.get_or_create_visualizer(config)            │
   └──────────────────────────────────────────────────────────┘
                          ↓
   ┌──────────────────────────────────────────────────────────┐
   │ Check: key in orchestrator._visualizers?                 │
   │ key = ('napari', port) or ('fiji', port)                 │
   └──────────────────────────────────────────────────────────┘
                          ↓
                    ┌─────┴─────┐
                    │           │
                   Yes          No
                    │           │
                    ↓           ↓
   ┌──────────────────┐  ┌──────────────────────────────┐
   │ Check if still   │  │ Create new visualizer        │
   │ running          │  │ config.create_visualizer()   │
   └──────────────────┘  └──────────────────────────────┘
           ↓                      ↓
     ┌─────┴─────┐         ┌──────────────────────────┐
     │           │         │ Start async              │
    Yes          No        │ start_viewer(async=True) │
     │           │         └──────────────────────────┘
     ↓           ↓                ↓
   ┌──────┐  ┌────────┐    ┌──────────────────────────┐
   │Reuse!│  │Remove  │    │ Background ping thread   │
   │Return│  │& create│    │ (sets _ready for Fiji)   │
   │viewer│  │new     │    └──────────────────────────┘
   └──────┘  └────────┘           ↓
                          ┌──────────────────────────┐
                          │ Store in cache           │
                          │ _visualizers[key] = vis  │
                          └──────────────────────────┘
                                   ↓
                          ┌──────────────────────────┐
                          │ Return viewer            │
                          └──────────────────────────┘

Shutdown Sequence
~~~~~~~~~~~~~~~~~

**Graceful Shutdown**:

.. code-block:: python

   # Send shutdown command via control channel
   control_socket.send_json({'type': 'shutdown'})

   # Wait for process to terminate
   process.join(timeout=5.0)

   # Close ZMQ sockets
   publisher.close()
   control_socket.close()

**Force Kill**:

.. code-block:: python

   # Find processes on port
   pids = _find_pids_on_port(port)

   # Kill each process
   for pid in pids:
       os.kill(pid, signal.SIGTERM)

**Port Cleanup**:

- All sockets use ``LINGER=0`` to free ports immediately
- Shared memory is unlinked after use
- Orchestrator removes dead viewers from cache

Design Decisions
----------------

Why Centralized Management?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Image browser and pipeline execution both need viewers

**Old Approach**: Each component managed its own viewers

**Issues**:

- Duplicate viewer instances on same port
- Blocking operations during viewer startup
- Inconsistent viewer state across components

**New Approach**: Orchestrator manages all viewers

**Benefits**:

- Single source of truth for viewer state
- Automatic reuse across components
- Consistent async startup pattern
- Type-safe viewer creation

Why Batch Streaming?
~~~~~~~~~~~~~~~~~~~~~

**Problem**: Sending images individually creates separate hyperstacks

**Root Cause**: Fiji groups images by ``(step_name, well)`` per batch

**Solution**: Collect all images first, then stream as single batch

**Benefits**:

- Proper hyperstack construction with all dimensions
- Fewer ZMQ messages (better performance)
- Clearer user intent (all selected images → one hyperstack)

Why Store Metadata for Fiji?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Progressive hyperstack building requires merging new images with existing ones

**Challenge**: ImageJ hyperstacks lose original metadata (channel names, z-indices, etc.)

**Attempted Solution**: Extract images from existing hyperstack

**Issue**: Extraction produces synthetic sequential indices, breaking merge logic

**Final Solution**: Store original metadata alongside hyperstacks

**Trade-off**: Higher memory usage, but enables progressive building

Why Type-Safe Config Detection?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Old Approach**: ``hasattr(config, 'napari_port')``

**Issues**:

- Fragile (breaks if attribute renamed)
- No type checking
- Ambiguous for configs with both ports

**New Approach**: ``isinstance(config, NapariStreamingConfig)``

**Benefits**:

- Type-safe (IDE autocomplete, type checkers)
- Explicit and clear
- Follows Python best practices

Implementation Details
----------------------

Viewer Detection
~~~~~~~~~~~~~~~~

**Port Scanning**:

.. code-block:: python

   def _scan_ports_parallel(self, ports):
       """Scan multiple ports in parallel to detect viewers."""
       with ThreadPoolExecutor(max_workers=10) as executor:
           futures = {executor.submit(self._ping_port, port): port
                     for port in ports}

           detected = []
           for future in as_completed(futures):
               port = futures[future]
               if future.result():
                   detected.append(port)

           return detected

   def _ping_port(self, port):
       """Try to ping a port to see if viewer is running."""
       try:
           control_socket = zmq.Context().socket(zmq.REQ)
           control_socket.setsockopt(zmq.LINGER, 0)
           control_socket.setsockopt(zmq.RCVTIMEO, 1000)
           control_socket.connect(f"tcp://127.0.0.1:{port + 1000}")

           control_socket.send_json({'type': 'ping'})
           response = control_socket.recv_json()

           return response.get('type') == 'pong'
       except:
           return False
       finally:
           control_socket.close()

**Usage**: Image browser scans ports on window open to detect external viewers

Hyperstack Coordinate Extraction
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Purpose**: Build coordinate lookup for merging images

**Code**:

.. code-block:: python

   def _extract_coordinates(self, metadata):
       """Extract (channel, z, time) coordinates from metadata."""
       # Get component lists from microscope handler
       channel_components = handler.get_channel_components()
       slice_components = handler.get_slice_components()
       frame_components = handler.get_frame_components()

       # Build coordinate tuples
       c_key = tuple(metadata.get(comp, 1) for comp in channel_components)
       z_key = tuple(metadata.get(comp, 1) for comp in slice_components)
       t_key = tuple(metadata.get(comp, 1) for comp in frame_components)

       return (c_key, z_key, t_key)

**Why Tuples**: Hashable for use as dict keys in coordinate lookup

Error Handling
~~~~~~~~~~~~~~

**Viewer Startup Failures**:

.. code-block:: python

   try:
       vis.start_viewer(async_mode=True)
   except Exception as e:
       logger.error(f"Failed to start viewer: {e}")
       # Don't cache failed viewer
       return None

**ZMQ Communication Failures**:

.. code-block:: python

   try:
       control_socket.send_json({'type': 'ping'})
       response = control_socket.recv_json()
   except zmq.Again:
       logger.warning("Viewer not responding to ping (timeout)")
       return False
   except Exception as e:
       logger.error(f"Communication error: {e}")
       return False

**Shared Memory Cleanup**:

.. code-block:: python

   try:
       shm.close()
       shm.unlink()
   except FileNotFoundError:
       # Already cleaned up
       pass
   except Exception as e:
       logger.warning(f"Failed to cleanup shared memory: {e}")

See Also
--------

- :doc:`../guides/viewer_management` - User guide for viewers
- :doc:`napari_integration_architecture` - Legacy Napari-specific docs
- :doc:`zmq_execution_system` - ZMQ pattern details

