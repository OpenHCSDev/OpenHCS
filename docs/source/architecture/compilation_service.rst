Compilation Service
===================

**Remote pipeline compilation service using ZMQ execution server.**

*Module: openhcs.pyqt_gui.widgets.shared.services.compilation_service*

Overview
--------

The ``CompilationService`` manages pipeline compilation by submitting compilation jobs
to the ZMQ execution server. This architecture separates compilation from the UI
process, enabling consistent execution environments and better resource management.

The service works in conjunction with ``ZMQClientService`` to manage connections to
the execution server, sharing the same client instance with ``ZMQExecutionService``
for compile/run workflows.

Architecture
------------

.. code-block:: text

   ┌─────────────────┐     ┌──────────────────┐     ┌─────────────────┐
   │   PlateManager  │────▶│ CompilationService│────▶│ZMQClientService│
   │    (UI Layer)   │     │  (Business Logic)│     │ (Connection Mgr)│
   └─────────────────┘     └──────────────────┘     └────────┬────────┘
                                                             │
                                    ┌────────────────────────┘
                                    │
                             ┌──────▼──────┐
                             │ ZMQ Server  │
                             │(Compilation)│
                             └─────────────┘

Key Components
~~~~~~~~~~~~~~

**CompilationService**
   - Validates pipeline definitions
   - Submits compilation jobs to ZMQ server
   - Polls for compilation completion
   - Reports progress via host callbacks

**ZMQClientService** (shared)
   - Manages ZMQ client lifecycle
   - Shared between CompilationService and ZMQExecutionService
   - Ensures consistent connection state

**CompilationHost Protocol**
   - Defines interface between service and UI widget
   - Provides access to plate data and pipeline definitions
   - Receives progress and error callbacks

CompilationHost Protocol
--------------------------

The service uses a Protocol to define the interface with the host widget:

.. code-block:: python

    from typing import Protocol, runtime_checkable
    from typing import Dict, List, Any

    @runtime_checkable
    class CompilationHost(Protocol):
        """Protocol for widgets that host the compilation service."""
        
        # State attributes the service needs
        global_config: Any
        orchestrators: Dict[str, Any]
        plate_configs: Dict[str, Dict]
        plate_compiled_data: Dict[str, Any]
        
        # Progress/status callbacks
        def emit_progress_started(self, count: int) -> None: ...
        def emit_progress_updated(self, value: int) -> None: ...
        def emit_progress_finished(self) -> None: ...
        def emit_orchestrator_state(self, plate_path: str, state: str) -> None: ...
        def emit_compilation_error(self, plate_name: str, error: str) -> None: ...
        def emit_status(self, msg: str) -> None: ...
        def get_pipeline_definition(self, plate_path: str) -> List: ...
        def update_button_states(self) -> None: ...

Using the Service
-----------------

The service requires a ``ZMQClientService`` instance for connection management:

.. code-block:: python

    from openhcs.pyqt_gui.widgets.shared.services.compilation_service import (
        CompilationService, CompilationHost
    )
    from openhcs.pyqt_gui.widgets.shared.services.zmq_client_service import (
        ZMQClientService
    )

    class MyWidget(QWidget, CompilationHost):
        def __init__(self):
            super().__init__()
            # Create shared client service (can be shared with ZMQExecutionService)
            self._zmq_client_service = ZMQClientService(port=7777)
            self._compilation_service = CompilationService(
                host=self,
                client_service=self._zmq_client_service
            )

        async def compile_selected(self):
            selected = [{'path': '/plate/1', 'name': 'Plate 1'}, ...]
            await self._compilation_service.compile_plates(selected)

Main Methods
~~~~~~~~~~~~

.. code-block:: python

    async def compile_plates(self, selected_items: List[Dict]) -> None:
        """
        Compile pipelines for selected plates via ZMQ server.
        
        Args:
            selected_items: List of plate data dicts with 'path' and 'name' keys
        """

    def __init__(self, host: CompilationHost, client_service: ZMQClientService) -> None:
        """
        Initialize compilation service.
        
        Args:
            host: Widget implementing CompilationHost protocol
            client_service: Shared ZMQ client service for server communication
        """

Compilation Flow
----------------

1. **Connection Setup** - Uses shared ``ZMQClientService`` to connect to server
2. **Progress Initialization** - Calls ``emit_progress_started(count)``
3. **Per-Plate Compilation**:

   - Get pipeline definition from host via ``get_pipeline_definition()``
   - Retrieve pipeline configuration from ObjectState
   - Submit compile job to ZMQ server via ``submit_compile()``
   - Poll for completion via ``wait_for_completion()``
   - Store compiled orchestrator data
   - Update progress

4. **Progress Completion** - Calls ``emit_progress_finished()``

Internal Methods
----------------

.. code-block:: python

    def _get_pipeline_config(self, plate_path: str) -> Dict[str, Any]:
        """Retrieve pipeline configuration from ObjectState for the given plate."""
    
    def _set_orchestrator_state(self, plate_path: str, state: str) -> None:
        """Update orchestrator state via host callback."""
    
    def _validate_pipeline_steps(self, steps: List) -> None:
        """Validate that all steps have func attributes."""

Error Handling
--------------

Compilation errors are reported via the host's ``emit_compilation_error`` callback:

.. code-block:: python

    try:
        # Submit compilation job
        compile_id = await zmq_client.submit_compile(orchestrator_data, global_config)
        # Wait for completion
        result = await zmq_client.wait_for_completion(compile_id)
    except Exception as e:
        self.host.emit_compilation_error(plate_data['name'], str(e))
        logger.exception(f"Compilation failed for {plate_data['name']}")

Requirements
~~~~~~~~~~~~

- **ZMQ Server Running**: Compilation requires the ZMQ execution server to be running
- **Shared Client Service**: Must use same ``ZMQClientService`` instance as ``ZMQExecutionService``
- **ObjectState Access**: Pipeline configurations are read from ObjectState, not live orchestrators

Integration with PlateManager
-----------------------------

In ``PlateManagerWidget``:

.. code-block:: python

    class PlateManagerWidget(AbstractManagerWidget, CompilationHost):
        def __init__(self):
            super().__init__()
            # Create shared client service for both compilation and execution
            self._zmq_client_service = ZMQClientService(port=7777)
            
            # Initialize services with shared client
            self._compilation_service = CompilationService(
                host=self,
                client_service=self._zmq_client_service
            )
            self._execution_service = ZMQExecutionService(
                host=self,
                port=7777,
                client_service=self._zmq_client_service
            )
        
        # CompilationHost protocol implementation
        def emit_progress_started(self, count: int) -> None:
            self.progress_bar.setMaximum(count)
            self.progress_bar.show()
        
        def emit_compilation_error(self, plate_name: str, error: str) -> None:
            self.error_log.append(f"❌ {plate_name}: {error}")
        
        def get_pipeline_definition(self, plate_path: str) -> List:
            return self.plate_configs.get(plate_path, {}).get('steps', [])
        
        async def action_compile(self):
            """Compile selected plates."""
            selected = self._get_selected_plate_items()
            await self._compilation_service.compile_plates(selected)

Migration from Local Compilation
--------------------------------

Previous versions compiled pipelines locally using ``_get_or_create_orchestrator()``,
``_fix_step_ids()``, and ``_compile_pipeline()`` methods. These have been removed
in favor of remote compilation:

**Old Approach (Removed)**:

- Local orchestrator creation and caching
- Direct pipeline compilation in UI process
- Step ID fixing and validation
- Local context setup for worker threads

**New Approach**:

- Remote compilation on ZMQ server
- Shared ``ZMQClientService`` for connection management
- Pipeline config read from ObjectState
- ``submit_compile()`` / ``wait_for_completion()`` pattern

Benefits of Remote Compilation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

1. **Consistent Environment** - Compilation happens in same environment as execution
2. **Resource Sharing** - Single ``ZMQClientService`` reduces connection overhead
3. **Simplified UI** - UI process doesn't need compilation dependencies
4. **Better Error Reporting** - Server-side errors include full context

See Also
--------

- :doc:`zmq_execution_service_extracted` - Execution service (shares ZMQClientService)
- :doc:`abstract_manager_widget` - ABC that PlateManager inherits from
- :doc:`plate_manager_services` - Other PlateManager service extractions
- :doc:`pipeline_compilation_system` - Core pipeline compilation architecture
