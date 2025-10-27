ZMQ Execution System
====================

Overview
--------

The ZMQ execution system provides location-transparent pipeline execution with real-time progress streaming, graceful cancellation, and process reuse. It enables running OpenHCS pipelines on remote servers (like OMERO) while streaming results back to local viewers.

**The Remote Execution Challenge**: Traditional subprocess execution is fire-and-forget with no bidirectional communication, making remote execution, progress monitoring, and graceful cancellation impossible. This creates fundamental limitations for server-side processing and distributed workflows.

**The OpenHCS Solution**: A ZMQ-based execution pattern with dual-channel architecture (data + control) that provides request/response semantics, real-time progress streaming, and location transparency. The same API works whether the server is a local subprocess or a remote machine.

**Key Innovation**: Code-based transport using ``pickle_to_python`` eliminates pickle files and enum serialization issues while enabling network-safe, human-readable communication that works across process and network boundaries.

Architecture
------------

Dual-Channel Pattern
~~~~~~~~~~~~~~~~~~~~

The system uses two ZMQ channels extracted from the Napari streaming architecture:

**Data Port** (e.g., 7777)
  PUB/SUB socket for streaming progress updates from server to client

**Control Port** (data_port + 1000, e.g., 8777)
  REQ/REP socket for commands (ping, execute, cancel) and responses

This separation ensures progress updates never block command processing and vice versa.

Message Flow
~~~~~~~~~~~~

.. code-block:: text

   Client                          Server
     |                               |
     |-- PING (control) ------------>|
     |<-- PONG (control) ------------|
     |                               |
     |-- EXECUTE (control) --------->|
     |   (pipeline_code,             |
     |    config_code)               |
     |                               |
     |                          [executing]
     |                               |
     |<-- PROGRESS (data) -----------|
     |<-- PROGRESS (data) -----------|
     |<-- PROGRESS (data) -----------|
     |                               |
     |<-- RESULTS (control) ---------|

Core Components
~~~~~~~~~~~~~~~

**ZMQServer (ABC)** - ``openhcs/runtime/zmq_base.py``
  Generic dual-channel server with handshake protocol. Provides base functionality for all ZMQ servers (execution, Napari streaming, etc.).

**ZMQClient (ABC)** - ``openhcs/runtime/zmq_base.py``
  Generic multi-instance client with auto-spawning. Handles server detection, connection management, and automatic server creation.

**ZMQExecutionServer** - ``openhcs/runtime/zmq_execution_server.py``
  Execution-specific server that receives pipeline execution requests, executes them, and streams progress updates.

**ZMQExecutionClient** - ``openhcs/runtime/zmq_execution_client.py``
  High-level client API for pipeline execution with code generation, multi-instance support, and background progress streaming.

Code-Based Transport
--------------------

Unlike traditional subprocess execution (which pickles objects to temp files), the ZMQ pattern uses **code-based transport**:

Transport Process
~~~~~~~~~~~~~~~~~

1. **Client Side**: Convert objects to Python code using ``pickle_to_python``
2. **Network Transfer**: Send code as JSON strings via ZMQ
3. **Server Side**: Execute code to recreate objects
4. **Execution**: Run pipeline with recreated objects

.. code-block:: python

   # Client generates code
   from openhcs.core.serialization import pickle_to_python
   
   pipeline_code = pickle_to_python(pipeline_steps)
   config_code = pickle_to_python(global_config)
   
   # Send as JSON strings
   request = {
       'command': 'execute',
       'pipeline_code': pipeline_code,
       'config_code': config_code,
       'plate_id': plate_id
   }
   
   # Server recreates objects
   exec(pipeline_code, namespace)
   exec(config_code, namespace)
   pipeline_steps = namespace['pipeline_steps']
   global_config = namespace['global_config']

Benefits
~~~~~~~~

**No Temp Files**
  All communication via ZMQ sockets, no filesystem dependencies

**Network-Safe**
  JSON strings work across network boundaries

**Human-Readable**
  Generated code can be inspected and debugged

**No Enum Pickling Errors**
  Code-based transport avoids enum identity issues in multiprocessing

**Location-Transparent**
  Same code works for local subprocess and remote server execution

Server Modes
------------

Persistent Mode (Detached Subprocess)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Server survives parent process termination. Ideal for:

- Remote execution servers
- Shared execution servers (multiple UIs)
- Long-running services

.. code-block:: python

   client = ZMQExecutionClient(port=7777, persistent=True)
   client.connect()
   
   # Server runs as detached subprocess
   # Survives even if client process dies

Server launched via:

.. code-block:: bash

   python -m openhcs.runtime.zmq_execution_server_launcher --port 7777 --persistent

Non-Persistent Mode (Multiprocessing.Process)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Server dies with parent process. Ideal for:

- Testing
- Single-use execution
- UI-managed execution

.. code-block:: python

   client = ZMQExecutionClient(port=7777, persistent=False)
   client.connect()

   # Server runs as multiprocessing.Process
   # Automatically cleaned up when client disconnects

Server Monitoring
-----------------

Worker Process Tracking
~~~~~~~~~~~~~~~~~~~~~~~~

The ZMQ execution server tracks worker processes spawned by the ProcessPoolExecutor and reports their status in pong responses. This enables real-time monitoring of pipeline execution.

**Worker Information Provided:**

- Process ID (PID)
- Process status (running, sleeping, zombie, etc.)
- CPU usage percentage
- Memory usage (MB)
- Process creation time

**Implementation:**

.. code-block:: python

   # Server automatically tracks workers using psutil
   # Client gets worker info via ping
   server_info = client.get_server_info()

   # Response includes worker details
   {
       'type': 'pong',
       'ready': True,
       'active_executions': 2,
       'workers': [
           {
               'pid': 12345,
               'status': 'running',
               'cpu_percent': 95.2,
               'memory_mb': 512.3,
               'create_time': 1696800000.0
           },
           {
               'pid': 12346,
               'status': 'running',
               'cpu_percent': 87.1,
               'memory_mb': 498.7,
               'create_time': 1696800001.0
           }
       ]
   }

**Hierarchical Display in UI:**

The PyQt server manager widget displays workers hierarchically under their parent server:

.. code-block:: text

   Port 7777 - Execution Server    ✅ 2 exec    4 workers
   ├── Worker PID 12345             ⚙️ running   CPU: 95.2% | Mem: 512MB
   ├── Worker PID 12346             ⚙️ running   CPU: 87.1% | Mem: 499MB
   ├── Worker PID 12347             ⚙️ running   CPU: 92.5% | Mem: 505MB
   └── Worker PID 12348             ⚙️ running   CPU: 88.3% | Mem: 501MB

**Worker Detection Logic:**

The server uses ``psutil`` to identify worker processes:

1. Get all descendant processes of the server
2. Filter for Python processes
3. Exclude infrastructure processes (resource_tracker, semaphore_tracker)
4. Exclude Napari viewers (independent processes)
5. Include ProcessPoolExecutor workers

This ensures only actual pipeline workers are tracked, not helper processes or independent viewers.

**Performance Impact:**

Worker detection runs on every ping (typically every 3 seconds during UI refresh). The operation is fast (~1-2ms) and uses DEBUG-level logging to avoid log spam.

Multi-Instance Support
----------------------

The client automatically handles multiple server instances using port-based detection:

Detection Process
~~~~~~~~~~~~~~~~~

1. **Check if port in use**: Socket binding to detect existing servers
2. **Try to connect**: Send ping to verify server is responsive
3. **Spawn if needed**: If no server or unresponsive, spawn new one
4. **Kill unresponsive**: If server exists but doesn't respond, kill and restart

This mirrors the Napari viewer management pattern and ensures robust server lifecycle management.

.. code-block:: python

   # Client handles all server lifecycle automatically
   client = ZMQExecutionClient(port=7777)
   client.connect()  # Detects or spawns server
   
   # Execute pipeline
   response = client.execute_pipeline(...)
   
   # Server persists for reuse
   response2 = client.execute_pipeline(...)

Usage Patterns
--------------

Basic Execution
~~~~~~~~~~~~~~~

.. code-block:: python

   from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
   from openhcs.core.pipeline import Pipeline
   from openhcs.core.config import GlobalPipelineConfig
   
   # Create pipeline and config
   pipeline = Pipeline(...)
   global_config = GlobalPipelineConfig(...)
   
   # Connect to server (spawns if needed)
   client = ZMQExecutionClient(port=7777, persistent=True)
   client.connect()
   
   # Execute pipeline
   response = client.execute_pipeline(
       plate_id="/path/to/plate",
       pipeline_steps=pipeline.steps,
       global_config=global_config
   )
   
   # Check results
   if response['status'] == 'complete':
       print(f"Success! Wells: {len(response['results']['well_results'])}")
   else:
       print(f"Error: {response['message']}")
   
   # Cleanup
   client.disconnect()

Context Manager
~~~~~~~~~~~~~~~

.. code-block:: python

   with ZMQExecutionClient(port=7777) as client:
       response = client.execute_pipeline(...)
       # Automatic cleanup on exit

Progress Monitoring
~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   def on_progress(message):
       print(f"Well {message['well_id']}: {message['step']} - {message['status']}")
   
   client = ZMQExecutionClient(
       port=7777,
       progress_callback=on_progress
   )
   
   # Progress updates streamed in real-time
   response = client.execute_pipeline(...)

Comparison with Subprocess Runner
----------------------------------

.. list-table::
   :header-rows: 1
   :widths: 30 35 35

   * - Feature
     - Subprocess Runner
     - ZMQ Execution
   * - Communication
     - One-way (fire-and-forget)
     - Bidirectional (request/response)
   * - Transport
     - Pickle files
     - Code strings (JSON)
   * - Progress
     - Log file polling
     - Real-time streaming
   * - Cancellation
     - Kill process
     - Graceful cancellation
   * - Multi-instance
     - No
     - Yes (port-based)
   * - Process reuse
     - No
     - Yes (persistent mode)
   * - Location
     - Local only
     - Local or remote
   * - Handshake
     - No
     - Yes (ping/pong)

Integration with OMERO
----------------------

The ZMQ execution system enables server-side execution on OMERO:

.. code-block:: python

   # Client runs locally
   client = ZMQExecutionClient(host='omero-server.example.com', port=7777)
   
   # Server runs on OMERO machine (near data)
   response = client.execute_pipeline(
       plate_id=123,  # OMERO plate ID
       pipeline_steps=steps,
       global_config=config
   )
   
   # Results streamed back to local client
   # Zero data transfer overhead

This pattern eliminates data transfer bottlenecks by processing data where it lives.

Implementation Details
----------------------

Base Classes
~~~~~~~~~~~~

The ZMQ execution system is built on abstract base classes that provide common functionality:

**ZMQServer (ABC)**
  - Dual-channel socket management (data + control)
  - Handshake protocol (ping/pong)
  - Message routing and error handling
  - Graceful shutdown

**ZMQClient (ABC)**
  - Server detection and connection
  - Automatic server spawning
  - Multi-instance management
  - Background progress thread

Execution-Specific Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**ZMQExecutionServer**
  - Handles execute/status/cancel requests
  - Mirrors ``execution_server.py`` pattern
  - Supports both ``config_params`` and ``config_code``
  - Streams progress via data channel

**ZMQExecutionClient**
  - Code generation using ``pickle_to_python``
  - High-level pipeline execution API
  - Progress callback support
  - Automatic cleanup

See Also
--------

- :doc:`napari_streaming_system` - Napari streaming architecture (ZMQ pattern origin)
- :doc:`omero_backend_system` - OMERO integration using ZMQ execution
- :doc:`multiprocessing_coordination_system` - Multiprocessing patterns

