Compilation Service
===================

**Pipeline compilation service extracted from PlateManagerWidget.**

*Module: openhcs.pyqt_gui.widgets.shared.services.compilation_service*

Why Extract Compilation Logic?
------------------------------

The original ``PlateManagerWidget`` was over 2,500 lines, mixing UI concerns with
business logic. Compilation—the process of turning a pipeline definition into an
executable orchestrator—is inherently complex, involving:

- Creating and caching orchestrator instances
- Setting up the context system for worker threads
- Validating pipeline step configurations
- Expanding variable components into iteration sets
- Progress tracking for long-running compilations

None of this requires UI knowledge. By extracting it into ``CompilationService``,
we achieve:

1. **Testability** - The service can be unit tested without Qt
2. **Reusability** - Other UI components can use the same compilation logic
3. **Maintainability** - UI and business logic evolve independently
4. **Clarity** - Each class has a single, well-defined responsibility

The Protocol Pattern
--------------------

The key architectural insight is using a Protocol to define the interface between
service and host. The service doesn't care *what* the host is—it only cares that
the host provides certain attributes and callbacks. This is dependency inversion:
the service depends on an abstraction, not a concrete widget class.

The Protocol is ``@runtime_checkable``, meaning ``isinstance(obj, CompilationHost)``
works. This enables fail-loud validation when the service is created:

.. code-block:: python

    from typing import Protocol, runtime_checkable
    
    @runtime_checkable
    class CompilationHost(Protocol):
        """Protocol for widgets that host the compilation service."""
        
        # State attributes the service needs
        global_config: Any
        orchestrators: Dict[str, PipelineOrchestrator]
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

Creating the service is straightforward—pass a host that implements the Protocol.
The service stores a reference to the host and calls its methods during compilation:

.. code-block:: python

    from openhcs.pyqt_gui.widgets.shared.services.compilation_service import (
        CompilationService, CompilationHost
    )

    class MyWidget(QWidget, CompilationHost):
        def __init__(self):
            super().__init__()
            self.compilation_service = CompilationService(host=self)

        async def compile_selected(self):
            selected = [{'path': '/plate/1', 'name': 'Plate 1'}, ...]
            await self.compilation_service.compile_plates(selected)

Main Methods
~~~~~~~~~~~~

.. code-block:: python

    async def compile_plates(self, selected_items: List[Dict]) -> None:
        """
        Compile pipelines for selected plates.
        
        Args:
            selected_items: List of plate data dicts with 'path' and 'name' keys
        """

Compilation Flow
----------------

1. **Context Setup** - Ensures global config context is available in worker thread
2. **Progress Initialization** - Calls ``emit_progress_started(count)``
3. **Per-Plate Compilation**:

   - Get pipeline definition from host
   - Validate step func attributes
   - Get or create orchestrator
   - Initialize pipeline
   - Compile with variable components
   - Update progress

4. **Progress Completion** - Calls ``emit_progress_finished()``

Internal Methods
----------------

.. code-block:: python

    async def _get_or_create_orchestrator(self, plate_path: str) -> PipelineOrchestrator:
        """Get existing orchestrator or create new one."""
    
    def _validate_pipeline_steps(self, steps: List) -> None:
        """Validate that all steps have func attributes."""
    
    async def _initialize_and_compile(self, orchestrator, steps, plate_data) -> None:
        """Initialize pipeline and compile with variable components."""

Error Handling
--------------

Compilation errors are reported via the host's ``emit_compilation_error`` callback:

.. code-block:: python

    try:
        await self._initialize_and_compile(orchestrator, steps, plate_data)
    except Exception as e:
        self.host.emit_compilation_error(plate_data['name'], str(e))
        logger.exception(f"Compilation failed for {plate_data['name']}")

Integration with PlateManager
-----------------------------

In ``PlateManagerWidget``:

.. code-block:: python

    class PlateManagerWidget(AbstractManagerWidget, CompilationHost):
        def __init__(self):
            super().__init__()
            self._compilation_service = CompilationService(host=self)
        
        # CompilationHost protocol implementation
        def emit_progress_started(self, count: int) -> None:
            self.progress_bar.setMaximum(count)
            self.progress_bar.show()
        
        def emit_compilation_error(self, plate_name: str, error: str) -> None:
            self.error_log.append(f"❌ {plate_name}: {error}")
        
        async def action_compile(self):
            """Compile selected plates."""
            selected = self._get_selected_plate_items()
            await self._compilation_service.compile_plates(selected)

See Also
--------

- :doc:`zmq_execution_service_extracted` - Execution service for running compiled pipelines
- :doc:`abstract_manager_widget` - ABC that PlateManager inherits from
- :doc:`plate_manager_services` - Other PlateManager service extractions
- :doc:`pipeline_compilation_system` - Core pipeline compilation architecture

