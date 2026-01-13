Log Viewer
==========

The OpenHCS log viewer provides real-time monitoring of pipeline execution, server activity, and system events with advanced features for large log files and distributed execution.

Overview
--------

**Key Features:**

- **Async log loading** - Non-blocking file loading for large logs (10,000+ lines)
- **Background syntax highlighting** - Async highlighting in thread pool, never blocks UI
- **Multi-line text selection** - Select and copy text across multiple log lines
- **Auto-scroll during selection** - Proportional scroll speed when dragging past edges
- **Real-time tailing** - 50ms throttled updates for active logs
- **ZMQ server discovery** - Automatic detection of execution server logs
- **Multi-log support** - View multiple log files simultaneously
- **Search and filter** - Find specific events or error patterns
- **Update throttling** - Minimal UI impact when typing in other windows

Location
--------

**PyQt UI**: Tools → View Logs

**Log Storage**: ``~/.local/share/openhcs/logs/``

Log Types
---------

Application Logs
~~~~~~~~~~~~~~~~

**Format**: ``openhcs_unified_YYYYMMDD_HHMMSS.log``

Contains all application activity:

- Pipeline compilation
- Function registry operations
- Configuration changes
- UI events
- Error traces

**Example**:

.. code-block:: text

   2025-10-08 14:35:21,123 - openhcs.core.pipeline.compiler - INFO - Compiling pipeline: test_pipeline
   2025-10-08 14:35:21,456 - openhcs.core.orchestrator.orchestrator - INFO - Processing well A01
   2025-10-08 14:35:22,789 - openhcs.gpu.registry - DEBUG - Loaded 574 GPU functions

ZMQ Execution Server Logs
~~~~~~~~~~~~~~~~~~~~~~~~~~

**Format**: ``openhcs_zmq_server_port_<PORT>_<TIMESTAMP>.log``

Contains server-specific activity:

- Client connections/disconnections
- Pipeline execution requests
- Worker process management
- Progress streaming
- Error handling

**Example**:

.. code-block:: text

   2025-10-08 14:40:15,234 - openhcs.runtime.zmq_execution_server - INFO - Server started on port 7777
   2025-10-08 14:40:20,567 - openhcs.runtime.zmq_execution_server - INFO - Client connected
   2025-10-08 14:40:21,890 - openhcs.runtime.zmq_execution_server - INFO - Executing pipeline: test_pipeline
   2025-10-08 14:40:25,123 - openhcs.runtime.zmq_execution_server - INFO - 🔍 WORKER DETECTION: Found 4 workers

**Server Discovery**:

The log viewer automatically discovers ZMQ server logs by:

1. Scanning ``~/.local/share/openhcs/logs/`` for server log files
2. Extracting port numbers from filenames
3. Matching ports to active servers in the server manager
4. Displaying server logs hierarchically under their server

Advanced Features
-----------------

Multi-Line Text Selection
~~~~~~~~~~~~~~~~~~~~~~~~~

Select and copy text across multiple log lines with visual highlighting:

**Usage**:

1. Click and drag to select text within or across log lines
2. Selected text is highlighted with system selection color
3. Release mouse to automatically copy selection to clipboard
4. Paste anywhere with Ctrl+V

**Auto-Scroll During Selection**:

When dragging selection past the top or bottom edge of the window:

- **Inside viewport near edge (0-50px)**: Slow proportional scroll (0-100% of base speed)
- **Outside viewport**: Fast scroll proportional to distance (up to 50x base speed)
- **Direction**: Drag up to scroll up, drag down to scroll down
- **Speed**: Increases smoothly with distance from viewport edge

**Example**:

.. code-block:: text

   # Select error trace across multiple lines
   2025-10-08 14:35:21,123 - openhcs.core - ERROR - Pipeline failed
   Traceback (most recent call last):
     File "pipeline.py", line 42, in execute
       result = process_well(well_id)
   ValueError: Invalid well ID: Z99

**Performance**:

- Selection highlighting: <5ms per line
- Auto-scroll: 50ms refresh rate
- Syntax highlighting preserved during selection

Background Syntax Highlighting
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Syntax highlighting runs in a background thread pool and never blocks the UI:

**How It Works**:

1. When a log line becomes visible, request highlighting in background
2. Background worker parses text with regex to extract formatting segments
3. Main thread applies formatting when ready (or paints plain text if not ready)
4. Results are cached for instant reuse on subsequent paints

**Highlighted Elements**:

- **Timestamps**: Gray (``2025-10-08 14:35:21,123``)
- **Log levels**: Bold colored (``ERROR`` = red, ``WARNING`` = yellow, ``INFO`` = blue)
- **Logger names**: Cyan (``openhcs.core.pipeline.compiler``)
- **File paths**: Green (``/path/to/file.py``)
- **Python strings**: Yellow (``"test_pipeline"``)
- **Numbers**: Magenta (``42``, ``3.14``)

**Performance**:

- Parsing: ~1-2ms per line (in background thread)
- Applying formats: <1ms per line (on main thread)
- Cache hit: <0.1ms per line
- UI never blocks waiting for highlighting

Update Throttling
~~~~~~~~~~~~~~~~~

Log updates are throttled to reduce UI load during rapid changes:

**How It Works**:

1. New log lines are buffered in memory
2. UI updates at most every 50ms (20 updates/second)
3. Multiple lines arriving within 50ms are batched into single update
4. Updates are deferred entirely when window is hidden/minimized

**Benefits**:

- Typing in pipeline config remains smooth even with active log viewer
- Rapid log bursts don't cause UI lag
- Background processes don't slow down foreground work

**Performance**:

- Before throttling: ~200ms UI freeze on 100-line burst
- After throttling: <10ms UI impact on 100-line burst
- Latency: 50ms maximum delay for log visibility

Async Log Loading
~~~~~~~~~~~~~~~~~

Large log files (>1MB) are loaded asynchronously to prevent UI freezing:

**How It Works**:

1. File is read asynchronously in chunks
2. Lines are inserted in batches of 1000 with event loop yields
3. UI remains responsive during loading
4. Progress is visible as lines appear incrementally

**Performance**:

- 10,000-line log: ~50ms load time
- 100,000-line log: ~500ms load time
- UI remains responsive during loading
- Batch size: 1000 lines per event loop iteration

Real-Time Tailing
~~~~~~~~~~~~~~~~~

Active logs are automatically tailed with 100ms refresh:

.. code-block:: python

   # Enable tailing
   self.tail_timer = QTimer()
   self.tail_timer.timeout.connect(self.refresh_log)
   self.tail_timer.start(100)  # 100ms refresh
   
   def refresh_log(self):
       """Reload log and scroll to bottom."""
       if self.current_log_path:
           self.load_log(self.current_log_path)
           self.scroll_to_bottom()

**Use Cases**:

- Monitor pipeline execution in real-time
- Watch server activity during debugging
- Track worker process lifecycle

ZMQ Server Log Discovery
~~~~~~~~~~~~~~~~~~~~~~~~~

The log viewer automatically finds and displays ZMQ server logs:

**Discovery Process**:

1. Scan log directory for files matching ``openhcs_zmq_server_port_*``
2. Extract port number from filename
3. Check if server is active (via server manager)
4. Display log in hierarchical tree under server

**Example Tree**:

.. code-block:: text

   Logs
   ├── Application Log (openhcs_unified_20251008_143521.log)
   ├── Port 7777 - Execution Server
   │   └── Server Log (openhcs_zmq_server_port_7777_1696800000.log)
   └── Port 8888 - Execution Server
       └── Server Log (openhcs_zmq_server_port_8888_1696800100.log)

**Benefits**:

- No manual log file hunting
- Clear association between servers and logs
- Easy debugging of multi-server setups

Search and Filter
~~~~~~~~~~~~~~~~~

Find specific events or patterns:

.. code-block:: python

   # Search for errors
   self.search_box.setText("ERROR")
   
   # Search for specific well
   self.search_box.setText("well A01")
   
   # Search for worker activity
   self.search_box.setText("WORKER DETECTION")

**Features**:

- Case-insensitive search
- Regex support
- Highlight all matches
- Jump to next/previous match

Common Use Cases
----------------

Debugging Pipeline Failures
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

1. Open log viewer
2. Load latest application log
3. Search for "ERROR" or "Traceback"
4. Examine stack trace and context

Monitoring Server Activity
~~~~~~~~~~~~~~~~~~~~~~~~~~

1. Open log viewer
2. Select ZMQ server log from tree
3. Enable real-time tailing
4. Watch worker creation, execution, and cleanup

Analyzing Performance
~~~~~~~~~~~~~~~~~~~~~

1. Open log viewer
2. Search for timing logs (e.g., "Processing well")
3. Compare timestamps between wells
4. Identify bottlenecks

Troubleshooting Worker Issues
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

1. Open ZMQ server log
2. Search for "WORKER DETECTION"
3. Check worker PIDs, CPU%, memory usage
4. Verify workers are being created and cleaned up

See Also
--------

- :doc:`../development/ui-patterns` - UI performance optimizations
