Viewer Management (Napari & Fiji)
==================================

Overview
--------

OpenHCS implements a sophisticated cross-process viewer management system that enables:

- **Unified viewer management**: Single orchestrator manages both Napari and Fiji viewers
- **Viewer reuse across contexts**: Image browser can use viewers started by pipelines and vice versa
- **Parallel viewer startup**: Multiple viewers can start simultaneously without blocking
- **Persistent viewers**: Viewers survive parent process termination
- **Automatic reconnection**: Detects and connects to existing viewers before creating new ones
- **Progressive hyperstack building**: Images accumulate into hyperstacks (Fiji matches Napari behavior)
- **Batch streaming**: Multiple images sent as single batch for proper hyperstack construction

This guide explains how the viewer management system works and how to use it effectively.

Architecture Components
-----------------------

Orchestrator (Centralized Viewer Management)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Location**: ``openhcs/core/orchestrator/orchestrator.py``

**Key Features**:

- **Single source of truth**: All viewers tracked in ``orchestrator._visualizers`` dict
- **Shared infrastructure**: Pipeline execution and image browser use same viewer instances
- **Type-safe creation**: Uses ``isinstance()`` checks for NapariStreamingConfig/FijiStreamingConfig
- **Automatic reuse**: Checks if viewer already exists before creating new one
- **Async startup with handshake**: Starts viewers asynchronously and pings them to set ready state

**Key Data Structure**:

.. code-block:: python

   # Viewers tracked by (backend_name, port) key
   orchestrator._visualizers = {
       ('napari', 5555): NapariStreamVisualizer(...),
       ('fiji', 5556): FijiStreamVisualizer(...),
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
       # Determine key based on config type
       if isinstance(config, NapariStreamingConfig):
           key = ('napari', config.napari_port)
       elif isinstance(config, FijiStreamingConfig):
           key = ('fiji', config.fiji_port)

       # Check if viewer already exists and is running
       if key in self._visualizers:
           vis = self._visualizers[key]
           if vis.is_running:
               return vis  # Reuse existing viewer

       # Create new viewer
       vis = config.create_visualizer(self.filemanager, vis_config)
       vis.start_viewer(async_mode=True)

       # Ping server in background thread (required for Fiji)
       # This sets _ready = True so server processes data messages

       # Store in cache
       self._visualizers[key] = vis
       return vis

NapariStreamVisualizer
~~~~~~~~~~~~~~~~~~~~~~

**Location**: ``openhcs/runtime/napari_stream_visualizer.py``

**Key Features**:

- Manages Napari viewer processes in separate Python processes (avoids Qt conflicts)
- Uses ZMQ (ZeroMQ) for inter-process communication
- Supports both synchronous and asynchronous startup modes
- Can detect and connect to existing viewers on the same port

**Key Properties**:

- ``is_running``: Property that checks actual process state
- ``_connected_to_existing``: Flag indicating connection to external viewer
- ``napari_port``: Port for data streaming (control port is ``napari_port + 1000``)

**Key Methods**:

.. code-block:: python

   # Start viewer (async by default)
   visualizer.start_viewer(async_mode=True)

   # Try to connect to existing viewer
   visualizer._try_connect_to_existing_viewer(port)

   # Kill unresponsive viewers
   visualizer._kill_processes_on_port(port)

   # Clean shutdown
   visualizer.stop_viewer()

FijiStreamVisualizer
~~~~~~~~~~~~~~~~~~~~

**Location**: ``openhcs/runtime/fiji_stream_visualizer.py``

**Key Features**:

- Manages Fiji/ImageJ viewer processes via PyImageJ
- Uses same ZMQ pattern as Napari (data + control channels)
- Builds ImageJ hyperstacks with proper dimension mapping
- Supports progressive hyperstack building (images accumulate)

**Key Properties**:

- ``is_running``: Property that checks actual process state
- ``fiji_port``: Port for data streaming (control port is ``fiji_port + 1000``)

**Hyperstack Building**:

.. code-block:: python

   # FijiViewerServer stores metadata for progressive building
   self.hyperstacks = {}  # window_key -> ImagePlus
   self.hyperstack_metadata = {}  # window_key -> list of image dicts

   # When new images arrive:
   # 1. Check if hyperstack exists for (step_name, well)
   # 2. If exists, merge new images with stored metadata
   # 3. Rebuild hyperstack with all images (existing + new)
   # 4. Store updated metadata for future merges

Image Browser
~~~~~~~~~~~~~

**Location**: ``openhcs/pyqt_gui/widgets/image_browser.py``

**Key Features**:

- Browse images from plate metadata with folder tree and table view
- Stream to Napari and/or Fiji with live configuration
- Enable/disable viewers independently via checkboxes
- Batch streaming for proper hyperstack construction
- Manage viewer instances (view status, kill viewers)
- Auto-scan for viewers on window open

**Dual Viewer Support**:

.. code-block:: python

   # Napari streaming (enabled by default)
   self.napari_enable_checkbox = QCheckBox("Enable Napari Streaming")
   self.napari_config_form = ParameterFormManager(LazyNapariStreamingConfig)

   # Fiji streaming (disabled by default)
   self.fiji_enable_checkbox = QCheckBox("Enable Fiji Streaming")
   self.fiji_config_form = ParameterFormManager(LazyFijiStreamingConfig)

**Viewer Management** (Delegated to Orchestrator):

- No local viewer tracking - queries ``orchestrator._visualizers``
- ``refresh_napari_instances()``: Scans orchestrator cache and external ports
- ``_kill_viewer_on_port()``: Removes from orchestrator cache and kills process
- ``get_or_create_visualizer()``: Delegates to orchestrator for viewer creation

**Batch Streaming**:

.. code-block:: python

   def view_selected_in_napari(self):
       # Collect all selected filenames
       filenames = [...]

       # Load all images and stream as batch
       self._load_and_stream_batch_to_napari(filenames)

   def _load_and_stream_batch_to_napari(self, filenames):
       # Load all images
       image_data_list = [filemanager.load(f) for f in filenames]

       # Resolve config once
       napari_config = resolve_lazy_configurations(...)

       # Get or create viewer (reuses existing)
       viewer = orchestrator.get_or_create_visualizer(napari_config)

       # Stream entire batch (builds hyperstack)
       filemanager.save_batch(
           image_data_list, filenames,
           Backend.NAPARI_STREAM.value,
           napari_port=viewer.napari_port,
           step_name='image_browser'
       )

**Double-Click Behavior**:

- Napari only enabled → streams to Napari
- Fiji only enabled → streams to Fiji
- Both enabled → streams to both simultaneously
- Neither enabled → shows informative message

Viewer Lifecycle
----------------

Startup Sequence (Orchestrator-Managed)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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

Cross-Process Communication
~~~~~~~~~~~~~~~~~~~~~~~~~~~

**ZMQ Channels**:

1. **Data Port** (e.g., 5555): SUB socket for receiving images
2. **Control Port** (e.g., 6555 = 5555+1000): REP socket for handshake

**Handshake Protocol**:

.. code-block:: python

   # Client sends ping
   {'type': 'ping'}
   
   # Viewer responds with pong
   {'type': 'pong', 'ready': True}

**Image Streaming**:

.. code-block:: python

   # Client sends message via shared memory
   {
       'shm_name': 'psm_abc123',
       'shape': (1024, 1024),
       'dtype': 'uint16',
       'name': 'A01_s001_w1_z001.tif',
       'metadata': {...}
   }

Progressive Hyperstack Building (Fiji)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Fiji hyperstacks were being replaced instead of accumulated

**Solution**: Store original metadata alongside hyperstacks for merging

.. code-block:: python

   # FijiViewerServer maintains metadata cache
   self.hyperstack_metadata = {
       'image_browser_B03': [
           {'data': array1, 'metadata': {'channel': '1', 'z_index': '001', ...}},
           {'data': array2, 'metadata': {'channel': '1', 'z_index': '002', ...}},
       ]
   }

   # When new images arrive for same window_key:
   def _build_single_hyperstack(window_key, new_images, ...):
       # Get existing images from metadata cache
       if window_key in self.hyperstack_metadata:
           existing_images = self.hyperstack_metadata[window_key]

           # Build coordinate lookup
           lookup = {}
           for img in existing_images:
               coords = (c_key, z_key, t_key)  # from metadata
               lookup[coords] = img

           # Add new images (override at same coordinates)
           for img in new_images:
               coords = (c_key, z_key, t_key)
               lookup[coords] = img

           all_images = list(lookup.values())

       # Rebuild hyperstack with all images
       # Close old hyperstack, create new one with expanded dimensions
       # Store updated metadata for next merge

**Behavior**:

- Send image 1 (B03, z=1) → Creates hyperstack with 1 Z slice
- Send image 2 (B03, z=2) → Merges into hyperstack → Now has 2 Z slices
- Send image 3 (B03, channel=2, z=1) → Merges → Now has 2 Z × 2 channels
- Images at same coordinates override previous images

Batch Streaming Architecture
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Sending images individually creates separate hyperstacks

**Solution**: Collect all images first, then stream as single batch

.. code-block:: python

   # OLD: Individual streaming (creates N hyperstacks)
   for filename in selected_files:
       image_data = load(filename)
       filemanager.save_batch([image_data], [filename], ...)  # Batch of 1

   # NEW: Batch streaming (creates 1 hyperstack)
   image_data_list = [load(f) for f in selected_files]
   filemanager.save_batch(image_data_list, selected_files, ...)  # Batch of N

**Why this matters**:

- Fiji groups images by ``(step_name, well)`` to build hyperstacks
- Each ``save_batch()`` call is treated as a complete batch
- Sending individually → each image is a "complete" batch → separate hyperstacks
- Sending as batch → all images in one batch → single hyperstack with all dimensions

**Image Browser Implementation**:

.. code-block:: python

   def view_selected_in_napari(self):
       # Collect ALL filenames first
       filenames = [item.data(UserRole) for item in selected_rows]

       # Stream as single batch
       self._load_and_stream_batch_to_napari(filenames)

   def _load_and_stream_batch_to_napari(self, filenames):
       # Load all images
       image_data_list = []
       for filename in filenames:
           image_data = filemanager.load(filename)
           image_data_list.append(image_data)

       # Stream entire batch at once
       filemanager.save_batch(
           image_data_list,
           filenames,
           Backend.NAPARI_STREAM.value,
           step_name='image_browser',
           ...
       )

Known Limitations
-----------------

Port-Based Killing Only
~~~~~~~~~~~~~~~~~~~~~~~

**Issue**: Image browser can kill any viewer on a port, even external ones

**Why**: Uses port-based killing via ``_kill_processes_on_port()``

**Behavior**:

- Tracked viewers (in orchestrator cache): Clean ZMQ shutdown first, then kill
- External viewers: Direct port-based kill

**Risk**: Might kill wrong processes if multiple processes share a port (rare)

**Mitigation**: Always try ping/pong handshake before killing to verify it's a viewer

External Viewer Detection
~~~~~~~~~~~~~~~~~~~~~~~~~~

**Status**: ✅ **Implemented**

**Solution**: Image browser scans common ports on window open

.. code-block:: python

   # Scan Napari ports (5555-5564) and Fiji ports (5556-5565)
   napari_ports = [5555 + i for i in range(10)]
   fiji_ports = [5556 + i for i in range(10)]

   # Ping each port in parallel to detect viewers
   detected_ports = self._scan_ports_parallel(all_ports)

**Behavior**:

- Shows all detected viewers in instance list (tracked + external)
- External viewers marked as "Port XXXX - ✅ Ready"
- Tracked viewers show type: "Napari Port 5555 - ✅ Ready"

Hyperstack Metadata Memory Usage
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Issue**: Fiji server stores full image data in ``hyperstack_metadata`` dict

**Impact**: Memory usage grows with number of images in hyperstack

**Example**: 100 images × 2048×2048 × 2 bytes = ~800 MB per hyperstack

**Mitigation**:

- Hyperstacks are grouped by ``(step_name, well)`` so memory is bounded per well
- Metadata is cleared when hyperstack window is closed
- Only affects Fiji (Napari doesn't need metadata storage)

**Future Optimization**: Store only metadata, reconstruct images from ImageJ stack when merging

Best Practices
--------------

For Users
~~~~~~~~~

1. **Reuse viewers**: OpenHCS automatically reuses viewers on the same port
2. **Enable viewers selectively**: Use checkboxes to enable only needed viewers (saves resources)
3. **Batch selection**: Select multiple images before clicking "View" for proper hyperstack building
4. **Check status**: Look for ✅ Ready in instance list before expecting immediate display
5. **Kill properly**: Use the image browser's kill button, not OS task manager
6. **Progressive building**: Send images one at a time to same well to build hyperstack incrementally

For Developers
~~~~~~~~~~~~~~

1. **Use orchestrator.get_or_create_visualizer()**: Don't create viewers directly
2. **Always use async_mode=True**: Unless you have a specific reason to block
3. **Batch streaming**: Collect all images first, then call ``save_batch()`` once
4. **Type-safe config detection**: Use ``isinstance(config, NapariStreamingConfig)`` not ``hasattr()``
5. **Set LINGER=0**: On all ZMQ sockets to free ports immediately
6. **Ping for Fiji**: Background ping thread required to set ``_ready = True`` for Fiji servers
7. **Preserve metadata**: Store full component metadata for hyperstack merging (Fiji)

Performance Characteristics
---------------------------

Startup Times
~~~~~~~~~~~~~

- **Single viewer**: ~2-5 seconds (depends on Napari import time)
- **Multiple viewers (sequential)**: N × 2-5 seconds
- **Multiple viewers (parallel)**: ~2-5 seconds (same as single!)

Memory Usage
~~~~~~~~~~~~

- **Per viewer process**: ~200-500 MB (Napari + Qt + NumPy)
- **ZMQ overhead**: Negligible (~1 MB per connection)

Throughput
~~~~~~~~~~

- **Image streaming**: Limited by ZMQ (typically >100 MB/s on localhost)
- **Bottleneck**: Usually Napari rendering, not network

Usage Examples
--------------

Get or Create Viewer (Recommended)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   from openhcs.core.config import NapariStreamingConfig, FijiStreamingConfig

   # Create config
   napari_config = NapariStreamingConfig(
       napari_port=5555,
       persistent=True
   )

   # Get or create viewer (reuses existing if available)
   viewer = orchestrator.get_or_create_visualizer(napari_config)

   # Viewer is already started asynchronously
   # Stream images immediately
   filemanager.save_batch(
       images, paths,
       Backend.NAPARI_STREAM.value,
       napari_port=viewer.napari_port,
       step_name='my_analysis'
   )

Stream to Both Napari and Fiji
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   # Create configs
   napari_config = NapariStreamingConfig(napari_port=5555)
   fiji_config = FijiStreamingConfig(fiji_port=5556)

   # Get or create both viewers
   napari_viewer = orchestrator.get_or_create_visualizer(napari_config)
   fiji_viewer = orchestrator.get_or_create_visualizer(fiji_config)

   # Stream same images to both
   filemanager.save_batch(
       images, paths,
       Backend.NAPARI_STREAM.value,
       napari_port=napari_viewer.napari_port,
       step_name='comparison'
   )

   filemanager.save_batch(
       images, paths,
       Backend.FIJI_STREAM.value,
       fiji_port=fiji_viewer.fiji_port,
       step_name='comparison'
   )

Batch Streaming for Hyperstack Building
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   # Collect all images for a well
   well_images = []
   well_paths = []

   for z in range(1, 11):  # 10 z-slices
       for ch in ['DAPI', 'GFP', 'RFP']:  # 3 channels
           filename = f"B03_s001_w{ch}_z{z:03d}.tif"
           image_data = filemanager.load(filename)
           well_images.append(image_data)
           well_paths.append(filename)

   # Stream as single batch (creates 1 hyperstack with 10Z × 3C)
   viewer = orchestrator.get_or_create_visualizer(fiji_config)
   filemanager.save_batch(
       well_images, well_paths,
       Backend.FIJI_STREAM.value,
       fiji_port=viewer.fiji_port,
       step_name='image_browser',
       microscope_handler=handler
   )

Progressive Hyperstack Building
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   # Send first z-slice
   viewer = orchestrator.get_or_create_visualizer(fiji_config)
   filemanager.save_batch(
       [image_z1], ['B03_s001_w1_z001.tif'],
       Backend.FIJI_STREAM.value,
       fiji_port=viewer.fiji_port,
       step_name='image_browser'
   )
   # → Creates hyperstack with 1 Z slice

   # Later, send second z-slice
   filemanager.save_batch(
       [image_z2], ['B03_s001_w1_z002.tif'],
       Backend.FIJI_STREAM.value,
       fiji_port=viewer.fiji_port,
       step_name='image_browser'
   )
   # → Merges into existing hyperstack → Now has 2 Z slices

   # Later, send different channel
   filemanager.save_batch(
       [image_ch2], ['B03_s001_w2_z001.tif'],
       Backend.FIJI_STREAM.value,
       fiji_port=viewer.fiji_port,
       step_name='image_browser'
   )
   # → Merges into existing hyperstack → Now has 2 Z × 2 channels

Kill Viewer
~~~~~~~~~~~

.. code-block:: python

   # From image browser (removes from orchestrator cache)
   image_browser._kill_viewer_on_port(5555)

   # Direct kill (if you have viewer reference)
   viewer.stop_viewer()  # Graceful shutdown

   # Force kill if unresponsive
   if viewer.is_running:
       viewer._kill_processes_on_port(viewer.napari_port)

Architecture Diagrams
---------------------

Viewer Management Flow
~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: text

   ┌─────────────────────────────────────────────────────────────┐
   │                    User Interaction                          │
   │  (Pipeline Execution / Image Browser / Manual Streaming)    │
   └─────────────────────────────────────────────────────────────┘
                              ↓
   ┌─────────────────────────────────────────────────────────────┐
   │         orchestrator.get_or_create_visualizer(config)       │
   │                                                              │
   │  • Check if viewer exists in _visualizers cache             │
   │  • Reuse if running, create new if not                      │
   │  • Start async with background ping thread                  │
   │  • Store in cache for future reuse                          │
   └─────────────────────────────────────────────────────────────┘
                              ↓
                    ┌─────────┴─────────┐
                    │                   │
                 Napari               Fiji
                    │                   │
                    ↓                   ↓
   ┌──────────────────────┐  ┌──────────────────────┐
   │ NapariStreamVisualizer│  │ FijiStreamVisualizer │
   │                       │  │                      │
   │ • Separate process    │  │ • Separate process   │
   │ • ZMQ data + control  │  │ • ZMQ data + control │
   │ • Auto-reconnect      │  │ • Ping/pong required │
   └──────────────────────┘  └──────────────────────┘
                    │                   │
                    ↓                   ↓
   ┌──────────────────────┐  ┌──────────────────────┐
   │ Napari Viewer        │  │ Fiji/ImageJ Viewer   │
   │                      │  │                      │
   │ • Layer-based        │  │ • Hyperstack-based   │
   │ • Auto-accumulate    │  │ • Progressive build  │
   └──────────────────────┘  └──────────────────────┘

Fiji Hyperstack Building Flow
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: text

   ┌─────────────────────────────────────────────────────────────┐
   │  filemanager.save_batch(images, paths, FIJI_STREAM, ...)    │
   └─────────────────────────────────────────────────────────────┘
                              ↓
   ┌─────────────────────────────────────────────────────────────┐
   │              FijiViewerServer.process_batch()               │
   │                                                              │
   │  • Group images by (step_name, well)                        │
   │  • For each group, call _build_single_hyperstack()          │
   └─────────────────────────────────────────────────────────────┘
                              ↓
   ┌─────────────────────────────────────────────────────────────┐
   │         _build_single_hyperstack(window_key, images)        │
   │                                                              │
   │  1. Check if window_key in hyperstack_metadata              │
   │  2. If exists: merge new images with stored metadata        │
   │  3. Build coordinate lookup: (c, z, t) -> image             │
   │  4. Create ImageJ stack with all images                     │
   │  5. Set dimensions (nChannels, nSlices, nFrames)            │
   │  6. Close old hyperstack, show new one                      │
   │  7. Store updated metadata for future merges                │
   └─────────────────────────────────────────────────────────────┘
                              ↓
   ┌─────────────────────────────────────────────────────────────┐
   │                  ImageJ Hyperstack Window                    │
   │                                                              │
   │  • Title: "step_name_well" (e.g., "image_browser_B03")     │
   │  • Dimensions: C × Z × T                                    │
   │  • Sliders for navigating dimensions                        │
   │  • Composite mode for multi-channel                         │
   └─────────────────────────────────────────────────────────────┘

See Also
--------

- :doc:`../architecture/napari_integration_architecture` - Full architecture details
- :doc:`fiji_viewer_management` - Fiji-specific guide
- :doc:`../architecture/zmq_execution_system` - ZMQ pattern

