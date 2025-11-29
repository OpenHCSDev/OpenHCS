ZMQ Execution Service (Extracted)
=================================

**ZMQ client lifecycle and plate execution service extracted from PlateManagerWidget.**

*Module: openhcs.pyqt_gui.widgets.shared.services.zmq_execution_service*

Background: UI-Execution Boundary
---------------------------------

Pipeline execution in OpenHCS happens on a ZMQ server—a separate process that runs
pipelines and reports progress. The UI is a client that submits jobs and polls for
status. This separation is essential for long-running microscopy workflows that
can span hours or days.

But managing this client-server relationship from a UI widget creates tangled code.
The widget needs to handle connection lifecycle, job submission, progress polling,
graceful vs force shutdown, and state reconciliation when the server restarts. These
concerns have nothing to do with displaying widgets or handling user input.

What This Service Does
----------------------

``ZMQExecutionService`` extracts all ZMQ client management from the UI layer. It owns
the ``ZMQExecutionClient`` instance and handles:

- **Connection lifecycle** - Creating and destroying ZMQ connections
- **Job submission** - Sending compiled orchestrators to the server
- **Progress polling** - Monitoring job status and forwarding updates
- **Shutdown coordination** - Graceful (wait for step) vs force (immediate) termination

The host widget remains responsible only for displaying status and handling user
actions. When the user clicks "Run", the widget calls ``run_plates()``. When they
click "Stop", it calls ``stop_execution()``. All the complexity of ZMQ communication
is hidden inside the service.

ExecutionHost Protocol
----------------------

Like ``CompilationService``, this service uses a Protocol to define the host interface.
The service needs access to host state (orchestrators, execution IDs) and needs to
call back for status updates:

.. code-block:: python

    from typing import Protocol
    
    class ExecutionHost(Protocol):
        """Protocol for the widget that hosts ZMQ execution."""
        
        # State attributes
        execution_state: str
        plate_execution_ids: Dict[str, str]
        plate_execution_states: Dict[str, str]
        orchestrators: Dict[str, Any]
        plate_compiled_data: Dict[str, Any]
        global_config: Any
        current_execution_id: Optional[str]
        
        # Signal emission methods
        def emit_status(self, msg: str) -> None: ...
        def emit_error(self, msg: str) -> None: ...
        def emit_orchestrator_state(self, plate_path: str, state: str) -> None: ...
        def emit_execution_complete(self, result: dict, plate_path: str) -> None: ...
        def emit_clear_logs(self) -> None: ...
        def update_button_states(self) -> None: ...
        def update_item_list(self) -> None: ...
        
        # Execution completion hooks
        def on_plate_completed(self, plate_path: str, status: str, result: dict) -> None: ...
        def on_all_plates_completed(self, completed: int, failed: int) -> None: ...

Using the Service
-----------------

The pattern mirrors ``CompilationService``. Create the service with a host reference,
then call async methods to trigger execution:

.. code-block:: python

    from openhcs.pyqt_gui.widgets.shared.services.zmq_execution_service import (
        ZMQExecutionService, ExecutionHost
    )

    class MyWidget(QWidget, ExecutionHost):
        def __init__(self):
            super().__init__()
            self.execution_service = ZMQExecutionService(host=self, port=7777)

        async def run_selected(self):
            ready = self._get_ready_plates()
            await self.execution_service.run_plates(ready)

The Three Core Methods
~~~~~~~~~~~~~~~~~~~~~~

The service exposes a deliberately minimal API—just three methods that cover all
execution scenarios:

.. code-block:: python

    async def run_plates(self, ready_items: List[Dict]) -> None:
        """Run plates using ZMQ execution client."""

    async def stop_execution(self, graceful: bool = True) -> None:
        """Stop current execution (graceful or force)."""

    async def shutdown(self) -> None:
        """Cleanup and disconnect ZMQ client."""

Execution Flow
--------------

When ``run_plates()`` is called, the service orchestrates a complex sequence of
operations. Understanding this flow helps debug execution issues:

1. **Cleanup** - Disconnect any existing client (prevents resource leaks)
2. **Client Creation** - Create new ``ZMQExecutionClient`` with progress callback
3. **Submission** - Submit each plate's orchestrator to the server
4. **Polling** - Periodically check execution status, invoke callbacks
5. **Completion** - Report final results via host callbacks

.. code-block:: python

    async def run_plates(self, ready_items: List[Dict]) -> None:
        # Cleanup old client
        await self._disconnect_client(loop)
        
        # Create new client
        self.zmq_client = ZMQExecutionClient(
            port=self.port,
            persistent=True,
            progress_callback=self._on_progress
        )
        
        # Submit each plate
        for item in ready_items:
            orchestrator = self.host.orchestrators[item['path']]
            execution_id = await self.zmq_client.submit(
                orchestrator=orchestrator,
                global_config=self.host.global_config
            )
            self.host.plate_execution_ids[item['path']] = execution_id
        
        # Start polling
        await self._poll_until_complete()

Progress Callbacks
------------------

The service provides progress updates via internal callbacks:

.. code-block:: python

    def _on_progress(self, progress_data: dict) -> None:
        """Handle progress update from ZMQ client."""
        plate_path = progress_data.get('plate_path')
        status = progress_data.get('status')
        
        self.host.emit_status(f"Plate {plate_path}: {status}")
        
        if status == 'completed':
            self.host.on_plate_completed(plate_path, status, progress_data)

Shutdown Handling
-----------------

.. code-block:: python

    async def stop_execution(self, graceful: bool = True) -> None:
        """
        Stop current execution.
        
        Args:
            graceful: If True, wait for current step to complete.
                     If False, force immediate termination.
        """
        if graceful:
            await self.zmq_client.request_stop()
        else:
            await self.zmq_client.force_stop()
        
        self.host.update_button_states()

Integration with PlateManager
-----------------------------

.. code-block:: python

    class PlateManagerWidget(AbstractManagerWidget, ExecutionHost):
        def __init__(self):
            super().__init__()
            self._execution_service = ZMQExecutionService(host=self)
        
        # ExecutionHost protocol implementation
        def on_plate_completed(self, plate_path: str, status: str, result: dict):
            self._update_plate_status(plate_path, status)
            self.update_item_list()
        
        async def action_run(self):
            ready = self._get_ready_plates()
            await self._execution_service.run_plates(ready)

See Also
--------

- :doc:`compilation_service` - Compilation service for preparing pipelines
- :doc:`zmq_execution_system` - Core ZMQ execution architecture
- :doc:`abstract_manager_widget` - ABC that PlateManager inherits from
- :doc:`plate_manager_services` - Other PlateManager service extractions

