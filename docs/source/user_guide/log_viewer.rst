Log Viewer
==========

The OpenHCS log viewer provides real-time monitoring of pipeline execution, server activity, and system events with advanced features for large log files and distributed execution.

Overview
--------

**Key Features:**

- **Async log loading** - Non-blocking file loading for large logs (10,000+ lines)
- **Lazy syntax highlighting** - Only highlights visible text blocks
- **Real-time tailing** - 100ms refresh for active logs
- **ZMQ server discovery** - Automatic detection of execution server logs
- **Multi-log support** - View multiple log files simultaneously
- **Search and filter** - Find specific events or error patterns

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

Async Log Loading
~~~~~~~~~~~~~~~~~

Large log files (>1MB) are loaded asynchronously to prevent UI freezing:

.. code-block:: python

   # Implementation (simplified)
   def load_log_async(self, path):
       """Load log file without blocking UI."""
       
       # Start async load
       QTimer.singleShot(0, lambda: self._load_file_content(path))
       
       # Show loading indicator
       self.text_edit.setPlainText("Loading log file...")
       
   def _load_file_content(self, path):
       """Actual file loading (runs in event loop)."""
       with open(path, 'r') as f:
           content = f.read()
       
       # Update UI
       self.text_edit.setPlainText(content)
       self.scroll_to_bottom()

**Performance**:

- 10,000-line log: ~50ms load time
- 100,000-line log: ~500ms load time
- UI remains responsive during loading

Lazy Syntax Highlighting
~~~~~~~~~~~~~~~~~~~~~~~~~

Qt's ``QSyntaxHighlighter`` only processes visible text blocks, making highlighting instant regardless of file size:

.. code-block:: python

   class LogHighlighter(QSyntaxHighlighter):
       """Highlights log levels, timestamps, and errors."""
       
       def highlightBlock(self, text):
           """Called only for visible blocks."""
           
           # ERROR level - red
           if 'ERROR' in text:
               self.setFormat(0, len(text), self.error_format)
           
           # WARNING level - yellow
           elif 'WARNING' in text:
               self.setFormat(0, len(text), self.warning_format)
           
           # INFO level - default
           elif 'INFO' in text:
               self.setFormat(0, len(text), self.info_format)

**How It Works**:

1. User scrolls to a section of the log
2. Qt calls ``highlightBlock()`` only for visible lines
3. Invisible lines are skipped entirely
4. Scrolling triggers re-highlighting of new visible blocks

**Performance**:

- Highlighting 50 visible lines: ~5ms
- Total file size: irrelevant (only visible blocks processed)
- Scrolling remains smooth even with 100,000+ line logs

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

- :doc:`../architecture/zmq_execution_system` - ZMQ server architecture
- :doc:`../development/ui-patterns` - UI performance optimizations

