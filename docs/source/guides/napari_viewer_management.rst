Napari Viewer Management
=========================

Overview
--------

OpenHCS implements a sophisticated cross-process Napari viewer management system that enables:

- **Viewer reuse across processes**: Image browser can use viewers started by pipelines and vice versa
- **Parallel viewer startup**: Multiple viewers can start simultaneously
- **Persistent viewers**: Viewers survive parent process termination
- **Automatic reconnection**: Detects and connects to existing viewers before creating new ones

This guide explains how the viewer management system works and how to use it effectively.

Architecture Components
-----------------------

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

Image Browser
~~~~~~~~~~~~~

**Location**: ``openhcs/pyqt_gui/widgets/image_browser.py``

**Key Features**:

- Browse images from plate metadata with folder tree and table view
- Click images to stream to Napari with live configuration
- Manage Napari viewer instances (view status, kill viewers)
- Queue images when viewer is starting
- Auto-scan for viewers on window open

**Viewer Management**:

- ``napari_viewers``: Dict mapping port → NapariStreamVisualizer instance
- ``pending_napari_queue``: List of images waiting for viewer to be ready
- ``refresh_napari_instances()``: Update viewer list with status
- ``kill_selected_instances()``: Kill tracked viewers

Viewer Lifecycle
----------------

Startup Sequence
~~~~~~~~~~~~~~~~

.. code-block:: text

   ┌──────────────────────────────────────────────────────────┐
   │ User Action: Start Viewer or Send Image                  │
   └──────────────────────────────────────────────────────────┘
                          ↓
   ┌──────────────────────────────────────────────────────────┐
   │ Check: Is viewer already running on this port?           │
   └──────────────────────────────────────────────────────────┘
                          ↓
                    ┌─────┴─────┐
                    │           │
                   Yes          No
                    │           │
                    ↓           ↓
   ┌──────────────────┐  ┌──────────────────┐
   │ Try ping/pong    │  │ Spawn new        │
   │ handshake        │  │ viewer process   │
   └──────────────────┘  └──────────────────┘
           ↓                      ↓
   ┌──────────────┐        ┌──────────────┐
   │ Responsive?  │        │ Setup ZMQ    │
   └──────────────┘        │ client       │
     ↙           ↘         └──────────────┘
   Yes            No              ↓
    ↓              ↓        ┌──────────────┐
   ┌──────┐   ┌────────┐   │ is_running   │
   │Reuse!│   │Kill &  │   │ = True       │
   │Setup │   │restart │   └──────────────┘
   │ZMQ   │   └────────┘
   └──────┘
      ↓
   ┌──────────────────────────────────────────┐
   │ _connected_to_existing = True            │
   │ is_running = True                        │
   └──────────────────────────────────────────┘

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

is_running Property Logic
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   @property
   def is_running(self) -> bool:
       if not self._is_running:
           return False
       
       # Connected to external viewer? Trust the flag
       if self._connected_to_existing:
           return self._is_running
       
       # Own process? Check if actually alive
       if self.process is None:
           self._is_running = False
           return False
       
       # Check process.is_alive() or process.poll()
       alive = check_process_alive()
       if not alive:
           self._is_running = False
       
       return alive

**Why this matters**:

- When we connect to an external viewer, we don't have a process reference
- We can't check ``process.is_alive()`` on a process we didn't create
- The ``_connected_to_existing`` flag tells us to trust the ``_is_running`` flag

Image Queue System
~~~~~~~~~~~~~~~~~~

**Problem**: User clicks image before viewer finishes starting

**Solution**: Queue images and process when viewer is ready

.. code-block:: python

   # When image is clicked but viewer not ready
   pending_napari_queue.append((filename, image_data, config, port))
   
   # Background thread waits for viewer
   while not viewer.is_running:
       time.sleep(0.5)
   
   # When ready, process queue
   for filename, image_data, config, port in queue:
       stream_to_viewer(...)

Known Limitations
-----------------

Cannot Kill External Viewers
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Issue**: Image browser can only kill viewers it created (tracked viewers)

**Why**: We only have process references for viewers we spawned

**Workaround**: External viewers must be killed manually or by their parent process

**Potential Fix**: Implement port-based killing (use ``lsof``/``netstat`` to find PID)

**Risk**: Port-based killing might kill wrong processes (e.g., OpenHCS itself if it's using the port)

Cannot Detect External Viewers Without Sending Image
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Issue**: Image browser doesn't show external viewers in the instance list

**Why**: We only track viewers we create in ``self.napari_viewers`` dict

**Current Behavior**: External viewers only appear after you try to send an image to that port

**Potential Fix**:

- Scan common ports (5555-5564) on window open
- Try ping/pong handshake on each port
- Add detected viewers to instance list (read-only)

**Implementation Complexity**: Medium - need to avoid freezing UI during port scan

Queue Status Display
~~~~~~~~~~~~~~~~~~~~

**Issue**: When viewer is starting, queue count shows "🚀 Starting..." not "🚀 Starting (X queued)"

**Why**: Queue count is only shown for tracked viewers in ``refresh_napari_instances()``

**Impact**: Minor - user doesn't see how many images are queued until viewer is ready

**Fix**: Already implemented but may have edge cases

Best Practices
--------------

For Users
~~~~~~~~~

1. **Reuse viewers**: If a viewer is already open on a port, OpenHCS will reuse it
2. **Wait for ready**: Don't spam-click images while viewer is starting (they'll queue)
3. **Check status**: Look for ✅ Ready before expecting immediate display
4. **Kill properly**: Use the image browser's kill button, not OS task manager

For Developers
~~~~~~~~~~~~~~

1. **Always use async_mode=True**: Unless you have a specific reason to block
2. **Check is_running**: Before sending images, verify viewer is ready
3. **Handle queuing**: Implement queue system for async operations
4. **Set LINGER=0**: On all ZMQ sockets to free ports immediately
5. **Ping before kill**: Always try to connect before killing processes

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

Start Persistent Viewer
~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer
   
   # Create visualizer
   visualizer = NapariStreamVisualizer(
       filemanager,
       viewer_title="My Analysis",
       napari_port=5555
   )
   
   # Start in background (non-blocking)
   visualizer.start_viewer(async_mode=True)
   
   # Wait for ready
   while not visualizer.is_running:
       time.sleep(0.1)
   
   # Stream images
   filemanager.save_batch(images, paths, 'napari_stream')

Reuse Existing Viewer
~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   # Try to connect to existing viewer
   if visualizer._try_connect_to_existing_viewer(port=5555):
       print("Connected to existing viewer")
   else:
       print("No viewer found, starting new one")
       visualizer.start_viewer(async_mode=True)

Kill Viewer Gracefully
~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   # Try graceful shutdown first
   visualizer.stop_viewer()
   
   # If unresponsive, force kill
   if visualizer.is_running:
       visualizer._kill_processes_on_port(visualizer.napari_port)

See Also
--------

- :doc:`../architecture/napari_integration_architecture` - Full architecture details
- :doc:`../architecture/napari_streaming_system` - Streaming system
- :doc:`../architecture/zmq_execution_system` - ZMQ pattern

