Fiji Viewer Management
=======================

Overview
--------

OpenHCS implements a sophisticated Fiji viewer management system that enables:

- **Viewer reuse across processes**: Image browser can use viewers started by pipelines and vice versa
- **Persistent viewers**: Viewers survive parent process termination
- **Automatic reconnection**: Detects and connects to existing viewers before creating new ones
- **PyImageJ integration**: Native Fiji functionality with automatic hyperstack building

This guide explains how the Fiji viewer management system works and how to use it effectively.

Architecture Components
-----------------------

FijiStreamVisualizer
~~~~~~~~~~~~~~~~~~~~

**Location**: ``openhcs/runtime/fiji_stream_visualizer.py``

**Key Features**:

- Manages Fiji viewer processes in separate Python processes (avoids Qt conflicts)
- Uses ZMQ (ZeroMQ) for inter-process communication
- Supports both synchronous and asynchronous startup modes
- Can detect and connect to existing viewers on the same port

**Key Properties**:

- ``is_running``: Boolean flag indicating viewer state
- ``persistent``: Whether viewer survives parent termination
- ``fiji_port``: Port for data streaming (control port is ``fiji_port + 1000``)
- ``process``: Subprocess or multiprocessing.Process instance

**Key Methods**:

.. code-block:: python

   # Start viewer (async by default)
   visualizer.start_viewer(async_mode=True)
   
   # Wait for server to be ready
   visualizer._wait_for_server_ready()
   
   # Stop viewer (respects persistent flag)
   visualizer.stop_viewer()
   
   # Check if viewer is running
   visualizer.is_viewer_running()

FijiViewerServer
~~~~~~~~~~~~~~~~

**Location**: ``openhcs/runtime/fiji_viewer_server.py``

**Key Features**:

- ZMQ server that receives images from pipeline workers
- PyImageJ integration for native Fiji functionality
- Automatic hyperstack building from component metadata
- Dual-channel ZMQ pattern (control + data)

**Key Methods**:

.. code-block:: python

   # Start server and initialize PyImageJ
   server.start()
   
   # Process control messages (ping/pong)
   server.process_messages()
   
   # Process image messages
   server.process_image_message(message)
   
   # Build hyperstack from images
   server._build_hyperstack(images, display_config)

Viewer Lifecycle
----------------

Startup Sequence
~~~~~~~~~~~~~~~~

.. code-block:: text

   ┌──────────────────────────────────────────────────────────┐
   │ User Action: Start Viewer or Stream Images               │
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
   │              │        │ sockets      │
   └──────────────┘        └──────────────┘
           ↓                      ↓
      ┌────┴────┐          ┌──────────────┐
      │         │          │ Initialize   │
     Yes        No         │ PyImageJ     │
      │         │          └──────────────┘
      ↓         ↓                 ↓
   ┌──────┐  ┌──────┐      ┌──────────────┐
   │ Reuse│  │ Kill │      │ Show Fiji UI │
   │viewer│  │ and  │      └──────────────┘
   └──────┘  │spawn │             ↓
             │ new  │      ┌──────────────┐
             └──────┘      │ Wait for     │
                           │ ping/pong    │
                           └──────────────┘

**Key Points**:

1. **Existing viewer detection**: Ping/pong handshake verifies viewer is responsive
2. **Automatic cleanup**: Unresponsive viewers are killed before spawning new ones
3. **Persistent mode**: Detached subprocesses survive parent termination
4. **Non-persistent mode**: Multiprocessing.Process for test cleanup

Persistent vs Non-Persistent Viewers
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Persistent Viewers** (default for production):

.. code-block:: python

   visualizer = FijiStreamVisualizer(
       filemanager,
       visualizer_config,
       persistent=True,  # Survives parent termination
       fiji_port=5556
   )
   visualizer.start_viewer()

**Characteristics**:

- Uses detached subprocess (``subprocess.Popen`` with ``start_new_session=True``)
- Survives parent process termination
- Logs to ``~/.local/share/openhcs/logs/fiji_detached_port_<port>.log``
- Ideal for interactive development and long-running sessions

**Non-Persistent Viewers** (for testing):

.. code-block:: python

   visualizer = FijiStreamVisualizer(
       filemanager,
       visualizer_config,
       persistent=False,  # Cleaned up with parent
       fiji_port=5556
   )
   visualizer.start_viewer()

**Characteristics**:

- Uses ``multiprocessing.Process``
- Terminated when parent process exits
- Tracked in global variable for test cleanup
- Ideal for automated testing

Shutdown Sequence
~~~~~~~~~~~~~~~~~

.. code-block:: text

   ┌──────────────────────────────────────────────────────────┐
   │ visualizer.stop_viewer()                                 │
   └──────────────────────────────────────────────────────────┘
                          ↓
   ┌──────────────────────────────────────────────────────────┐
   │ Check: Is viewer persistent?                             │
   └──────────────────────────────────────────────────────────┘
                          ↓
                    ┌─────┴─────┐
                    │           │
                   Yes          No
                    │           │
                    ↓           ↓
   ┌──────────────────┐  ┌──────────────────┐
   │ Keep alive       │  │ Terminate        │
   │ (log message)    │  │ process          │
   └──────────────────┘  └──────────────────┘
                                 ↓
                          ┌──────────────┐
                          │ Wait 5s for  │
                          │ graceful exit│
                          └──────────────┘
                                 ↓
                          ┌──────────────┐
                          │ Still alive? │
                          └──────────────┘
                                 ↓
                            ┌────┴────┐
                            │         │
                           Yes        No
                            │         │
                            ↓         ↓
                     ┌──────────┐  ┌──────┐
                     │ Force    │  │ Done │
                     │ kill     │  └──────┘
                     └──────────┘

**Key Points**:

1. **Persistent viewers**: Never terminated by ``stop_viewer()``
2. **Non-persistent viewers**: Graceful termination with 5s timeout
3. **Force kill**: Used if graceful termination fails

Using Fiji Streaming in Pipelines
----------------------------------

Basic Usage
~~~~~~~~~~~

Enable Fiji streaming in pipeline steps using ``FijiStreamingConfig``:

.. code-block:: python

   from openhcs.processing.pipeline import Pipeline, Step
   from openhcs.config.streaming_config import FijiStreamingConfig
   from openhcs.constants.fiji_enums import FijiLUT, FijiDimensionMode
   
   pipeline = Pipeline(
       name="Fiji Visualization Example",
       steps=[
           Step(
               name="Gaussian Blur",
               func=gaussian_blur,
               fiji_streaming_config=FijiStreamingConfig(
                   fiji_port=5556,
                   lut=FijiLUT.GREEN,
                   z_index_mode=FijiDimensionMode.STACK
               )
           )
       ]
   )

**What Happens**:

1. Compiler detects ``FijiStreamingConfig`` during compilation
2. Orchestrator creates ``FijiStreamVisualizer`` before execution
3. Worker processes stream results to Fiji via ZMQ
4. Fiji server builds hyperstacks and displays them

Lazy Configuration
~~~~~~~~~~~~~~~~~~

Use ``LazyFijiStreamingConfig`` to inherit from pipeline-level defaults:

.. code-block:: python

   from openhcs.config.streaming_config import LazyFijiStreamingConfig
   
   # Set pipeline-level defaults
   global_config = GlobalPipelineConfig(
       fiji_streaming_config=FijiStreamingConfig(
           fiji_port=5556,
           lut=FijiLUT.GRAYS,
           z_index_mode=FijiDimensionMode.STACK
       )
   )
   
   # Steps inherit defaults, override as needed
   Step(
       name="Step 1",
       func=process_images,
       fiji_streaming_config=LazyFijiStreamingConfig(
           lut=FijiLUT.GREEN  # Override LUT, inherit other settings
       )
   )

**Benefits**:

- Centralized configuration management
- Per-step overrides without duplication
- Live placeholder updates in UI

Display Configuration
~~~~~~~~~~~~~~~~~~~~~

Control how OpenHCS components map to Fiji dimensions:

.. code-block:: python

   FijiStreamingConfig(
       # Dimension mapping
       channel_mode=FijiDimensionMode.STACK,    # Channels → C dimension
       z_index_mode=FijiDimensionMode.STACK,    # Z-planes → Z dimension
       timepoint_mode=FijiDimensionMode.STACK,  # Timepoints → T dimension
       site_mode=FijiDimensionMode.SEPARATE,    # Sites → separate images
       
       # Display settings
       lut=FijiLUT.GREEN,                       # Color lookup table
       fiji_port=5556,                          # ZMQ port
       fiji_host='localhost'                    # ZMQ host
   )

**Dimension Modes**:

- ``STACK``: Component becomes hyperstack dimension (C, Z, or T)
- ``SLICE``: Component values shown as separate slices
- ``SEPARATE``: Component values shown as separate images

Troubleshooting
---------------

Viewer Won't Start
~~~~~~~~~~~~~~~~~~

**Symptom**: ``start_viewer()`` hangs or times out

**Possible Causes**:

1. **Port already in use**: Another process is using the Fiji port
2. **PyImageJ not installed**: Missing ``openhcs[viz]`` dependencies
3. **Java not available**: PyImageJ requires Java runtime

**Solutions**:

.. code-block:: bash

   # Check if port is in use
   lsof -i :5556
   
   # Install PyImageJ dependencies
   pip install 'openhcs[viz]'
   
   # Verify Java installation
   java -version
   
   # Check Fiji logs
   tail -f ~/.local/share/openhcs/logs/fiji_detached_port_5556.log

Viewer Becomes Unresponsive
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Symptom**: Ping/pong handshake fails, viewer doesn't display new images

**Possible Causes**:

1. **Fiji UI frozen**: ImageJ GUI became unresponsive
2. **Hyperstack building backlog**: Too many images queued
3. **Shared memory leak**: Memory exhaustion (should be fixed in v1.0+)

**Solutions**:

.. code-block:: python

   # Kill unresponsive viewer and spawn new one
   visualizer.stop_viewer()  # For non-persistent
   
   # Or manually kill persistent viewer
   pkill -f "fiji_detached_port_5556"
   
   # Restart viewer
   visualizer.start_viewer()

Images Not Appearing
~~~~~~~~~~~~~~~~~~~~

**Symptom**: Viewer is running but images don't appear

**Possible Causes**:

1. **Wrong port**: Publisher and viewer on different ports
2. **Materialization filtering**: Images not being materialized
3. **ZMQ buffer full**: Non-blocking send dropped images

**Solutions**:

.. code-block:: python

   # Verify port configuration
   logger.info(f"Fiji port: {visualizer.fiji_port}")
   
   # Check if images are being sent
   # Look for "Streamed batch" messages in logs
   
   # Increase buffer size if needed
   publisher.setsockopt(zmq.SNDHWM, 20000)  # Default is 10000

Performance Considerations
--------------------------

Hyperstack Building Latency
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Issue**: Hyperstack building takes ~2 seconds per stack

**Impact**: Fiji viewer processes images slower than Napari

**Mitigation**:

- Non-blocking sends prevent pipeline blocking
- High water mark (10000) buffers slow processing
- Dropped batches logged but don't affect pipeline

**Trade-off**: Fiji provides ImageJ ecosystem access at the cost of slower visualization

Shared Memory Overhead
~~~~~~~~~~~~~~~~~~~~~~

**Issue**: Each image creates a shared memory block

**Impact**: Memory usage scales with batch size

**Mitigation**:

- Publisher closes handles immediately after send
- Receiver unlinks memory after copying
- Proper cleanup prevents memory leaks

**Best Practice**: Use materialization filtering to stream only meaningful outputs

See Also
--------

- :doc:`../architecture/fiji_streaming_system` - Fiji streaming architecture
- :doc:`../architecture/external_integrations_overview` - Integration overview
- :doc:`napari_viewer_management` - Napari viewer management (similar patterns)

