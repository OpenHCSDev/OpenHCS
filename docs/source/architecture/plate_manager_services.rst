PlateManager Services Architecture
===================================

Overview
--------

The PlateManager widget delegates business logic to two protocol-based services:

- ``CompilationService`` (~205 lines): Orchestrator initialization and pipeline compilation
- ``ZMQExecutionService`` (~305 lines): ZMQ client lifecycle and execution polling

This service extraction reduces widget complexity by separating concerns and enables
testability through protocol-based interfaces.

CompilationService
------------------

**Location**: ``openhcs/pyqt_gui/widgets/shared/services/compilation_service.py``

**Purpose**: Manages orchestrator initialization and pipeline compilation.

**Protocol Interface**:

.. code-block:: python

    from typing import Protocol

    class CompilationHost(Protocol):
        """Protocol for widgets that host compilation operations."""
        
        def get_global_config(self) -> GlobalPipelineConfig:
            """Get global pipeline configuration."""
            ...
        
        def get_pipeline_data(self) -> Dict[str, List[AbstractStep]]:
            """Get pipeline data (plate_path -> steps)."""
            ...
        
        def set_orchestrator(self, orchestrator: PipelineOrchestrator) -> None:
            """Set the orchestrator instance."""
            ...
        
        def on_compilation_success(self) -> None:
            """Called when compilation succeeds."""
            ...
        
        def on_compilation_error(self, error: str) -> None:
            """Called when compilation fails."""
            ...

**Usage**:

.. code-block:: python

    from openhcs.pyqt_gui.widgets.shared.services.compilation_service import (
        CompilationService,
        CompilationHost
    )

    class PlateManagerWidget(AbstractManagerWidget, CompilationHost):
        def __init__(self):
            super().__init__()
            self.compilation_service = CompilationService()
        
        def action_compile(self):
            """Compile button handler."""
            self.compilation_service.compile_plates(self)
        
        # Implement CompilationHost protocol
        def get_global_config(self) -> GlobalPipelineConfig:
            return self.global_config
        
        def get_pipeline_data(self) -> Dict[str, List[AbstractStep]]:
            return self.pipeline_data
        
        def set_orchestrator(self, orchestrator: PipelineOrchestrator) -> None:
            self.orchestrator = orchestrator
        
        def on_compilation_success(self) -> None:
            self.status_label.setText("Compilation successful")
        
        def on_compilation_error(self, error: str) -> None:
            QMessageBox.critical(self, "Compilation Error", error)

**Key Methods**:

- ``compile_plates(host: CompilationHost)``: Main compilation entry point
- ``_validate_pipeline_steps(pipeline_data)``: Validate pipeline structure
- ``_get_or_create_orchestrator(host)``: Initialize or reuse orchestrator

ZMQExecutionService
-------------------

**Location**: ``openhcs/pyqt_gui/widgets/shared/services/zmq_execution_service.py``

**Purpose**: Manages ZMQ client lifecycle, execution polling, and progress updates.

**Protocol Interface**:

.. code-block:: python

    from typing import Protocol

    class ExecutionHost(Protocol):
        """Protocol for widgets that host execution operations."""
        
        def get_orchestrator(self) -> Optional[PipelineOrchestrator]:
            """Get the orchestrator instance."""
            ...
        
        def on_execution_started(self) -> None:
            """Called when execution starts."""
            ...
        
        def on_execution_progress(self, progress: float, status: str) -> None:
            """Called on progress updates."""
            ...
        
        def on_execution_complete(self) -> None:
            """Called when execution completes."""
            ...
        
        def on_execution_error(self, error: str) -> None:
            """Called when execution fails."""
            ...

**Usage**:

.. code-block:: python

    from openhcs.pyqt_gui.widgets.shared.services.zmq_execution_service import (
        ZMQExecutionService,
        ExecutionHost
    )

    class PlateManagerWidget(AbstractManagerWidget, ExecutionHost):
        def __init__(self):
            super().__init__()
            self.execution_service = ZMQExecutionService()
        
        def action_run(self):
            """Run button handler."""
            self.execution_service.run_plates(self)
        
        def action_stop(self):
            """Stop button handler."""
            self.execution_service.stop_execution(self)
        
        # Implement ExecutionHost protocol
        def get_orchestrator(self) -> Optional[PipelineOrchestrator]:
            return self.orchestrator
        
        def on_execution_started(self) -> None:
            self.run_button.setEnabled(False)
            self.stop_button.setEnabled(True)
        
        def on_execution_progress(self, progress: float, status: str) -> None:
            self.progress_bar.setValue(int(progress * 100))
            self.status_label.setText(status)
        
        def on_execution_complete(self) -> None:
            self.run_button.setEnabled(True)
            self.stop_button.setEnabled(False)
            QMessageBox.information(self, "Success", "Execution complete")
        
        def on_execution_error(self, error: str) -> None:
            QMessageBox.critical(self, "Execution Error", error)

**Key Methods**:

- ``run_plates(host: ExecutionHost)``: Start execution with ZMQ polling
- ``stop_execution(host: ExecutionHost)``: Stop execution and cleanup
- ``disconnect(host: ExecutionHost)``: Disconnect ZMQ client
- ``_poll_execution_status(host)``: Poll for progress updates (runs in timer)

Architecture Benefits
---------------------

**Separation of Concerns**:

- Widget focuses on UI state and user interactions
- Services handle business logic and external communication
- Clear boundaries via protocol interfaces

**Testability**:

- Services can be tested independently with mock hosts
- Protocol interfaces enable dependency injection
- No tight coupling to specific widget implementations

**Reusability**:

- Services can be used by any widget implementing the protocol
- Consistent behavior across different UI contexts
- Easy to add new hosts (e.g., TUI, CLI)

See Also
--------

- :doc:`abstract_manager_widget` - ABC for manager widgets
- :doc:`ui_services_architecture` - ParameterFormManager services
- :doc:`gui_performance_patterns` - Cross-window preview system

