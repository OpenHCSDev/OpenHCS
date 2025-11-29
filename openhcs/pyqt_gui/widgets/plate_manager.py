"""
Plate Manager Widget for PyQt6

Manages plate selection, initialization, and execution with full feature parity
to the Textual TUI version. Uses hybrid approach: extracted business logic + clean PyQt6 UI.
"""

import logging
import os
import asyncio
import traceback
from dataclasses import fields
from typing import List, Dict, Optional, Any, Callable, Tuple
from pathlib import Path

from PyQt6.QtWidgets import QApplication
from PyQt6.QtCore import Qt, pyqtSignal

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator, OrchestratorState
from openhcs.core.path_cache import PathCacheKey
from openhcs.io.filemanager import FileManager
from openhcs.io.base import _create_storage_registry
from openhcs.config_framework import LiveContextResolver
from openhcs.config_framework.lazy_factory import (
    ensure_global_config_context,
    rebuild_lazy_config_with_new_global_reference
)
from openhcs.config_framework.global_config import (
    set_global_config_for_editing,
    get_current_global_config
)
from openhcs.config_framework.context_manager import config_context
from openhcs.core.config_cache import _sync_save_config
from openhcs.core.xdg_paths import get_config_file_path
from openhcs.debug.pickle_to_python import generate_complete_orchestrator_code
from openhcs.processing.backends.analysis.consolidate_analysis_results import consolidate_multi_plate_summaries
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.windows.config_window import ConfigWindow
from openhcs.pyqt_gui.windows.plate_viewer_window import PlateViewerWindow
from openhcs.pyqt_gui.services.simple_code_editor import SimpleCodeEditorService
from openhcs.pyqt_gui.widgets.shared.abstract_manager_widget import AbstractManagerWidget
from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
from openhcs.pyqt_gui.widgets.shared.services.zmq_execution_service import ZMQExecutionService
from openhcs.pyqt_gui.widgets.shared.services.compilation_service import CompilationService
from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService

logger = logging.getLogger(__name__)


class PlateManagerWidget(AbstractManagerWidget):
    """
    PyQt6 Plate Manager Widget.

    Manages plate selection, initialization, compilation, and execution.
    Preserves all business logic from Textual version with clean PyQt6 UI.

    Uses CrossWindowPreviewMixin for reactive preview labels showing orchestrator
    config states (num_workers, well_filter, streaming configs, etc.).
    """

    TITLE = "Plate Manager"
    BUTTON_GRID_COLUMNS = 4  # 2x4 grid for 8 buttons
    BUTTON_CONFIGS = [
        ("Add", "add_plate", "Add new plate directory"),
        ("Del", "del_plate", "Delete selected plates"),
        ("Edit", "edit_config", "Edit plate configuration"),
        ("Init", "init_plate", "Initialize selected plates"),
        ("Compile", "compile_plate", "Compile plate pipelines"),
        ("Run", "run_plate", "Run/Stop plate execution"),
        ("Code", "code_plate", "Generate Python code"),
        ("Viewer", "view_metadata", "View plate metadata"),
    ]
    ACTION_REGISTRY = {
        "add_plate": "action_add", "del_plate": "action_delete",
        "edit_config": "action_edit_config", "init_plate": "action_init_plate",
        "compile_plate": "action_compile_plate", "code_plate": "action_code_plate",
        "view_metadata": "action_view_metadata",
    }
    DYNAMIC_ACTIONS = {"run_plate": "_resolve_run_action"}
    ITEM_NAME_SINGULAR = "plate"
    ITEM_NAME_PLURAL = "plates"
    ITEM_HOOKS = {
        'id_accessor': 'path', 'backing_attr': 'plates',
        'selection_attr': 'selected_plate_path', 'selection_signal': 'plate_selected',
        'selection_emit_id': True, 'selection_clear_value': '',
        'items_changed_signal': None, 'list_item_data': 'item',
        'preserve_selection_pred': lambda self: bool(self.orchestrators),
    }

    # Signals
    plate_selected = pyqtSignal(str)
    status_message = pyqtSignal(str)
    orchestrator_state_changed = pyqtSignal(str, str)
    orchestrator_config_changed = pyqtSignal(str, object)
    global_config_changed = pyqtSignal()
    pipeline_data_changed = pyqtSignal()
    clear_subprocess_logs = pyqtSignal()
    progress_started = pyqtSignal(int)
    progress_updated = pyqtSignal(int)
    progress_finished = pyqtSignal()
    compilation_error = pyqtSignal(str, str)
    initialization_error = pyqtSignal(str, str)
    execution_error = pyqtSignal(str)
    _execution_complete_signal = pyqtSignal(dict, str)
    _execution_error_signal = pyqtSignal(str)
    
    def __init__(self, service_adapter, color_scheme: Optional[PyQt6ColorScheme] = None,
                 gui_config=None, parent=None):
        """
        Initialize the plate manager widget.

        Args:
            service_adapter: PyQt service adapter for dialogs and operations
            color_scheme: Color scheme for styling (optional, uses service adapter if None)
            gui_config: GUI configuration (optional, for API compatibility with ABC)
            parent: Parent widget
        """
        # Plate-specific state (BEFORE super().__init__)
        self.global_config = service_adapter.get_global_config()
        self.pipeline_editor = None  # Will be set by main window

        # Business logic state (extracted from Textual version)
        self.plates: List[Dict] = []  # List of plate dictionaries
        self.selected_plate_path: str = ""
        self.orchestrators: Dict[str, PipelineOrchestrator] = {}
        self.plate_configs: Dict[str, Dict] = {}
        self.plate_compiled_data: Dict[str, tuple] = {}  # Store compiled pipeline data
        self.current_execution_id: Optional[str] = None  # Track current execution ID for cancellation
        self.execution_state = "idle"

        # Track per-plate execution state
        self.plate_execution_ids: Dict[str, str] = {}  # plate_path -> execution_id
        self.plate_execution_states: Dict[str, str] = {}  # plate_path -> "queued" | "running" | "completed" | "failed"

        # Extracted services (Phase 1, 2)
        self._zmq_service = ZMQExecutionService(self, port=7777)
        self._compilation_service = CompilationService(self)

        # Initialize base class (creates style_generator, event_bus, item_list, buttons, status_label internally)
        # Also auto-processes PREVIEW_FIELD_CONFIGS declaratively
        super().__init__(service_adapter, color_scheme, gui_config, parent)

        # Setup UI (after base and subclass state is ready)
        self.setup_ui()
        self.setup_connections()
        self.update_button_states()

        # Connect internal signals for thread-safe completion handling
        self._execution_complete_signal.connect(self._on_execution_complete)
        self._execution_error_signal.connect(self._on_execution_error)

        logger.debug("Plate manager widget initialized")

    def cleanup(self):
        """Cleanup resources before widget destruction."""
        logger.info("🧹 Cleaning up PlateManagerWidget resources...")
        self._zmq_service.disconnect()
        logger.info("✅ PlateManagerWidget cleanup completed")

    # ExecutionHost interface
    def emit_status(self, msg: str) -> None: self.status_message.emit(msg)
    def emit_error(self, msg: str) -> None: self.execution_error.emit(msg)
    def emit_orchestrator_state(self, plate_path: str, state: str) -> None: self.orchestrator_state_changed.emit(plate_path, state)
    def emit_execution_complete(self, result: dict, plate_path: str) -> None: self._execution_complete_signal.emit(result, plate_path)
    def emit_clear_logs(self) -> None: self.clear_subprocess_logs.emit()

    # CompilationHost interface
    def emit_progress_started(self, count: int) -> None: self.progress_started.emit(count)
    def emit_progress_updated(self, value: int) -> None: self.progress_updated.emit(value)
    def emit_progress_finished(self) -> None: self.progress_finished.emit()
    def emit_compilation_error(self, plate_name: str, error: str) -> None: self.compilation_error.emit(plate_name, error)
    def get_pipeline_definition(self, plate_path: str) -> List: return self._get_current_pipeline_definition(plate_path)

    def on_plate_completed(self, plate_path: str, status: str, result: dict) -> None:
        self._execution_complete_signal.emit(result, plate_path)

    def on_all_plates_completed(self, completed_count: int, failed_count: int) -> None:
        self._zmq_service.disconnect()
        self.execution_state = "idle"
        self.current_execution_id = None
        if completed_count > 1 and self.global_config.analysis_consolidation_config.enabled:
            try:
                self._consolidate_multi_plate_results()
                self.status_message.emit(f"All done: {completed_count} completed, {failed_count} failed. Global summary created.")
            except Exception as e:
                logger.error(f"Failed to create global summary: {e}", exc_info=True)
                self.status_message.emit(f"All done: {completed_count} completed, {failed_count} failed. Global summary failed.")
        else:
            self.status_message.emit(f"All done: {completed_count} completed, {failed_count} failed")
        self.update_button_states()

    # Declarative preview field configuration (processed automatically in ABC.__init__)
    PREVIEW_FIELD_CONFIGS = [
        'napari_streaming_config',  # Uses CONFIG_INDICATORS['napari_streaming_config'] = 'NAP'
        'fiji_streaming_config',    # Uses CONFIG_INDICATORS['fiji_streaming_config'] = 'FIJI'
        'step_materialization_config',  # Uses CONFIG_INDICATORS['step_materialization_config'] = 'MAT'
        ('num_workers', lambda v: f'W:{v if v is not None else 0}'),
        ('sequential_processing_config.sequential_components',
         lambda v: f'Seq:{",".join(c.value for c in v)}' if v else None),
        ('vfs_config.materialization_backend', lambda v: f'{v.value.upper()}'),
        ('path_planning_config.output_dir_suffix', lambda p: f'output={p}'),
        ('path_planning_config.well_filter', lambda wf: f'wf={len(wf)}' if wf else None),
        ('path_planning_config.sub_dir', lambda sub: f'subdir={sub}'),
    ]

    # ========== CrossWindowPreviewMixin Hooks ==========

    def _handle_full_preview_refresh(self) -> None:
        """Refresh all preview labels."""
        logger.info("🔄 PlateManager._handle_full_preview_refresh: refreshing preview labels")
        self.update_item_list()

    def _update_single_plate_item(self, plate_path: str):
        """Update a single plate item's preview text without rebuilding the list."""
        # Find the item in the list
        for i in range(self.item_list.count()):
            item = self.item_list.item(i)
            plate_data = item.data(Qt.ItemDataRole.UserRole)
            if plate_data and plate_data.get('path') == plate_path:
                # Rebuild just this item's display text
                plate = plate_data
                display_text = self._format_plate_item_with_preview_text(plate)
                item.setText(display_text)
                # Height is automatically calculated by MultilinePreviewItemDelegate.sizeHint()

                break

    def format_item_for_display(self, item: Dict, live_ctx=None) -> Tuple[str, str]:
        """Format plate item for display with preview (required abstract method)."""
        return (self._format_plate_item_with_preview_text(item), item['path'])

    def _format_plate_item_with_preview_text(self, plate: Dict) -> str:
        """Format plate item with status and config preview labels."""
        status_prefix, preview_labels = "", []
        if plate['path'] in self.orchestrators:
            orchestrator = self.orchestrators[plate['path']]
            state_map = {
                OrchestratorState.READY: "✓ Init", OrchestratorState.COMPILED: "✓ Compiled",
                OrchestratorState.COMPLETED: "✅ Complete", OrchestratorState.INIT_FAILED: "❌ Init Failed",
                OrchestratorState.COMPILE_FAILED: "❌ Compile Failed", OrchestratorState.EXEC_FAILED: "❌ Exec Failed",
            }
            if orchestrator.state == OrchestratorState.EXECUTING:
                exec_state = self.plate_execution_states.get(plate['path'])
                status_prefix = {"queued": "⏳ Queued", "running": "🔄 Running"}.get(exec_state, "🔄 Executing")
            else:
                status_prefix = state_map.get(orchestrator.state, "")
            preview_labels = self._build_config_preview_labels(orchestrator)

        line1 = f"{status_prefix} ▶ {plate['name']}" if status_prefix else f"▶ {plate['name']}"
        line2 = f"  {plate['path']}"
        if preview_labels:
            return f"{line1}\n{line2}\n  └─ configs=[{', '.join(preview_labels)}]"
        return f"{line1}\n{line2}"

    def _build_config_preview_labels(self, orchestrator: PipelineOrchestrator) -> List[str]:
        """Build preview labels for orchestrator config using ABC template."""
        try:
            pipeline_config = orchestrator.pipeline_config
            live_context_snapshot = ParameterFormManager.collect_live_context(
                scope_filter=orchestrator.plate_path
            )

            return self._build_preview_labels(
                item=orchestrator,
                config_source=pipeline_config,
                live_context_snapshot=live_context_snapshot,
            )
        except Exception as e:
            logger.error(f"Error building config preview labels: {e}\n{traceback.format_exc()}")
            return []

    # REMOVED: _build_effective_config_fallback - over-engineering
    # LiveContextResolver handles None value resolution through context stack [global, pipeline]

    def setup_connections(self):
        """Setup signal/slot connections (base class + plate-specific)."""
        self._setup_connections()
        self.orchestrator_state_changed.connect(self.on_orchestrator_state_changed)
        self.progress_started.connect(self._on_progress_started)
        self.progress_updated.connect(self._on_progress_updated)
        self.progress_finished.connect(self._on_progress_finished)
        self.compilation_error.connect(self._handle_compilation_error)
        self.initialization_error.connect(self._handle_initialization_error)
        self.execution_error.connect(self._handle_execution_error)
        self._execution_complete_signal.connect(self._on_execution_complete)
        self._execution_error_signal.connect(self._on_execution_error)

    def _resolve_run_action(self) -> str:
        """Resolve run/stop action based on current state.
        """
        return "action_stop_execution" if self.is_any_plate_running() else "action_run_plate"

    def _update_orchestrator_global_config(self, orchestrator, new_global_config):
        """Update orchestrator global config reference and rebuild pipeline config if needed."""
        ensure_global_config_context(GlobalPipelineConfig, new_global_config)

        current_config = orchestrator.pipeline_config or PipelineConfig()
        orchestrator.pipeline_config = rebuild_lazy_config_with_new_global_reference(
            current_config, new_global_config, GlobalPipelineConfig
        )
        logger.info(f"Rebuilt orchestrator-specific config for plate: {orchestrator.plate_path}")

        effective_config = orchestrator.get_effective_config()
        self.orchestrator_config_changed.emit(str(orchestrator.plate_path), effective_config)

    # ========== Business Logic Methods ==========

    def action_add_plate(self):
        """Handle Add Plate button."""
        # Use cached directory dialog with multi-selection support
        selected_paths = self.service_adapter.show_cached_directory_dialog(
            cache_key=PathCacheKey.PLATE_IMPORT,
            title="Select Plate Directory",
            fallback_path=Path.home(),
            allow_multiple=True
        )

        if selected_paths:
            self.add_plate_callback(selected_paths)
    
    def add_plate_callback(self, selected_paths: List[Path]):
        """
        Handle plate directory selection (extracted from Textual version).

        Args:
            selected_paths: List of selected directory paths
        """
        if not selected_paths:
            self.status_message.emit("Plate selection cancelled")
            return

        added_plates = []
        last_added_path = None

        for selected_path in selected_paths:
            # Check if plate already exists
            if any(plate['path'] == str(selected_path) for plate in self.plates):
                continue

            # Add the plate to the list
            plate_name = selected_path.name
            plate_path = str(selected_path)
            plate_entry = {
                'name': plate_name,
                'path': plate_path,
            }

            self.plates.append(plate_entry)
            added_plates.append(plate_name)
            last_added_path = plate_path

        if added_plates:
            self.update_item_list()
            # Select the last added plate to ensure pipeline assignment works correctly
            if last_added_path:
                self.selected_plate_path = last_added_path
                self.plate_selected.emit(last_added_path)
            self.status_message.emit(f"Added {len(added_plates)} plate(s): {', '.join(added_plates)}")
        else:
            self.status_message.emit("No new plates added (duplicates skipped)")

    # action_delete_plate() REMOVED - now uses ABC's action_delete() template with _perform_delete() hook

    def _validate_plates_for_operation(self, plates, operation_type):
        """Unified functional validator for all plate operations."""
        # Functional validation mapping
        validators = {
            'init': lambda p: True,  # Init can work on any plates
            'compile': lambda p: (
                self.orchestrators.get(p['path']) and
                self._get_current_pipeline_definition(p['path'])
            ),
            'run': lambda p: (
                self.orchestrators.get(p['path']) and
                self.orchestrators[p['path']].state in ['COMPILED', 'COMPLETED']
            )
        }

        # Functional pattern: filter invalid plates in one pass
        validator = validators.get(operation_type, lambda p: True)
        return [p for p in plates if not validator(p)]

    def _ensure_context(self):
        """Ensure global config context is set up (for worker threads)."""
        ensure_global_config_context(GlobalPipelineConfig, self.global_config)

    async def action_init_plate(self):
        """Handle Initialize Plate button with unified validation."""
        self._ensure_context()
        selected_items = self.get_selected_items()
        self._validate_plates_for_operation(selected_items, 'init')
        self.progress_started.emit(len(selected_items))

        async def init_single_plate(i, plate):
            plate_path = plate['path']
            plate_registry = _create_storage_registry()

            orchestrator = PipelineOrchestrator(
                plate_path=plate_path,
                storage_registry=plate_registry
            )
            saved_config = self.plate_configs.get(str(plate_path))
            if saved_config:
                orchestrator.apply_pipeline_config(saved_config)

            def do_init():
                self._ensure_context()
                return orchestrator.initialize()

            try:
                await asyncio.get_event_loop().run_in_executor(None, do_init)
                self.orchestrators[plate_path] = orchestrator
                self.orchestrator_state_changed.emit(plate_path, "READY")
                if not self.selected_plate_path:
                    self.selected_plate_path = plate_path
                    self.plate_selected.emit(plate_path)
            except Exception as e:
                logger.error(f"Failed to initialize plate {plate_path}: {e}", exc_info=True)
                failed = PipelineOrchestrator(plate_path=plate_path, storage_registry=plate_registry)
                failed._state = OrchestratorState.INIT_FAILED
                self.orchestrators[plate_path] = failed
                self.orchestrator_state_changed.emit(plate_path, OrchestratorState.INIT_FAILED.value)
                self.initialization_error.emit(plate['name'], str(e))

            self.progress_updated.emit(i + 1)

        await asyncio.gather(*[init_single_plate(i, p) for i, p in enumerate(selected_items)])

        self.progress_finished.emit()

        # Count successes and failures
        success_count = len([p for p in selected_items if self.orchestrators.get(p['path']) and self.orchestrators[p['path']].state == OrchestratorState.READY])
        error_count = len([p for p in selected_items if self.orchestrators.get(p['path']) and self.orchestrators[p['path']].state == OrchestratorState.INIT_FAILED])

        msg = f"Successfully initialized {success_count} plate(s)" if error_count == 0 else f"Initialized {success_count} plate(s), {error_count} error(s)"
        self.status_message.emit(msg)

    def action_edit_config(self):
        """Handle Edit Config button - per-orchestrator PipelineConfig editing."""
        selected_items = self.get_selected_items()
        if not selected_items:
            self.service_adapter.show_error_dialog("No plates selected for configuration.")
            return

        selected_orchestrators = [
            self.orchestrators[item['path']] for item in selected_items
            if item['path'] in self.orchestrators
        ]
        if not selected_orchestrators:
            self.service_adapter.show_error_dialog("No initialized orchestrators selected.")
            return

        representative_orchestrator = selected_orchestrators[0]
        current_plate_config = representative_orchestrator.pipeline_config

        def handle_config_save(new_config: PipelineConfig) -> None:
            logger.debug(f"🔍 CONFIG SAVE - new_config type: {type(new_config)}")
            for field in fields(new_config):
                raw_value = object.__getattribute__(new_config, field.name)
                logger.debug(f"🔍 CONFIG SAVE - new_config.{field.name} = {raw_value}")

            for orchestrator in selected_orchestrators:
                plate_key = str(orchestrator.plate_path)
                self.plate_configs[plate_key] = new_config
                # Direct synchronous call - no async needed
                orchestrator.apply_pipeline_config(new_config)
                # Emit signal for UI components to refresh
                effective_config = orchestrator.get_effective_config()
                self.orchestrator_config_changed.emit(str(orchestrator.plate_path), effective_config)

            # Auto-sync handles context restoration automatically when pipeline_config is accessed
            if self.selected_plate_path and self.selected_plate_path in self.orchestrators:
                logger.debug(f"Orchestrator context automatically maintained after config save: {self.selected_plate_path}")

            count = len(selected_orchestrators)
            # Success message dialog removed for test automation compatibility

        # Open configuration window using PipelineConfig (not GlobalPipelineConfig)
        # PipelineConfig already imported from openhcs.core.config
        self._open_config_window(
            config_class=PipelineConfig,
            current_config=current_plate_config,
            on_save_callback=handle_config_save,
            orchestrator=representative_orchestrator  # Pass orchestrator for context persistence
        )

    def _open_config_window(self, config_class, current_config, on_save_callback, orchestrator=None):
        """Open configuration window with specified config class and current config."""
        scope_id = str(orchestrator.plate_path) if orchestrator else None
        config_window = ConfigWindow(
            config_class, current_config, on_save_callback,
            self.color_scheme, self, scope_id=scope_id
        )
        config_window.show()
        config_window.raise_()
        config_window.activateWindow()

    def action_edit_global_config(self):
        """Handle global configuration editing - affects all orchestrators."""
        current_global_config = self.service_adapter.get_global_config() or GlobalPipelineConfig()

        def handle_global_config_save(new_config: GlobalPipelineConfig) -> None:
            self.service_adapter.set_global_config(new_config)
            set_global_config_for_editing(GlobalPipelineConfig, new_config)
            self._save_global_config_to_cache(new_config)
            for orchestrator in self.orchestrators.values():
                self._update_orchestrator_global_config(orchestrator, new_config)
            self.service_adapter.show_info_dialog("Global configuration applied to all orchestrators")

        self._open_config_window(
            config_class=GlobalPipelineConfig,
            current_config=current_global_config,
            on_save_callback=handle_global_config_save
        )

    def _save_global_config_to_cache(self, config: GlobalPipelineConfig):
        """Save global config to cache for persistence between sessions."""
        try:
            cache_file = get_config_file_path("global_config.config")
            success = _sync_save_config(config, cache_file)

            if success:
                logger.info("Global config saved to cache for session persistence")
            else:
                logger.error("Failed to save global config to cache - sync save returned False")
        except Exception as e:
            logger.error(f"Failed to save global config to cache: {e}")
            # Don't show error dialog as this is not critical for immediate functionality

    async def action_compile_plate(self):
        """Handle Compile Plate button - compile pipelines for selected plates."""
        selected_items = self.get_selected_items()

        if not selected_items:
            logger.warning("No plates available for compilation")
            return

        # Unified validation using functional validator
        invalid_plates = self._validate_plates_for_operation(selected_items, 'compile')

        # Let validation failures bubble up as status messages
        if invalid_plates:
            invalid_names = [p['name'] for p in invalid_plates]
            self.status_message.emit(f"Cannot compile invalid plates: {', '.join(invalid_names)}")
            return

        # Delegate to compilation service
        await self._compilation_service.compile_plates(selected_items)

    async def action_run_plate(self):
        """Handle Run Plate button - execute compiled plates using ZMQ."""
        selected_items = self.get_selected_items()
        if not selected_items:
            self.execution_error.emit("No plates selected to run.")
            return

        ready_items = [item for item in selected_items if item.get('path') in self.plate_compiled_data]
        if not ready_items:
            self.execution_error.emit("Selected plates are not compiled. Please compile first.")
            return

        await self._zmq_service.run_plates(ready_items)

    def _on_execution_complete(self, result, plate_path):
        """Handle execution completion for a single plate (called from main thread via signal)."""
        try:
            status = result.get('status')
            logger.info(f"Plate {plate_path} completed with status: {status}")

            # Update plate state and orchestrator
            if status == 'complete':
                self.plate_execution_states[plate_path] = "completed"
                self.status_message.emit(f"✓ Completed {plate_path}")
                new_state = OrchestratorState.COMPLETED
            elif status == 'cancelled':
                self.plate_execution_states[plate_path] = "failed"
                self.status_message.emit(f"✗ Cancelled {plate_path}")
                new_state = OrchestratorState.READY
            else:
                self.plate_execution_states[plate_path] = "failed"
                self.execution_error.emit(f"Execution failed for {plate_path}: {result.get('message', 'Unknown error')}")
                new_state = OrchestratorState.EXEC_FAILED

            if plate_path in self.orchestrators:
                self.orchestrators[plate_path]._state = new_state
                self.orchestrator_state_changed.emit(plate_path, new_state.value)

            # Reset execution state to idle and update button states
            # This ensures Stop/Force Kill button returns to "Run" state
            self.execution_state = "idle"
            self.current_execution_id = None
            self.update_button_states()

        except Exception as e:
            logger.error(f"Error handling execution completion: {e}", exc_info=True)

    def _consolidate_multi_plate_results(self):
        """Consolidate results from multiple completed plates into a global summary."""
        summary_paths, plate_names = [], []
        path_config = self.global_config.path_planning_config
        analysis_config = self.global_config.analysis_consolidation_config

        for plate_path_str, state in self.plate_execution_states.items():
            if state != "completed":
                continue
            plate_path = Path(plate_path_str)
            base = Path(path_config.global_output_folder) if path_config.global_output_folder else plate_path.parent
            output_plate_root = base / f"{plate_path.name}{path_config.output_dir_suffix}"

            materialization_path = self.global_config.materialization_results_path
            results_dir = Path(materialization_path) if Path(materialization_path).is_absolute() else output_plate_root / materialization_path
            summary_path = results_dir / analysis_config.output_filename

            if summary_path.exists():
                summary_paths.append(str(summary_path))
                plate_names.append(output_plate_root.name)
            else:
                logger.warning(f"No summary found for plate {plate_path} at {summary_path}")

        if len(summary_paths) < 2:
            return

        global_output_dir = Path(path_config.global_output_folder) if path_config.global_output_folder else Path(summary_paths[0]).parent.parent.parent
        global_summary_path = global_output_dir / analysis_config.global_summary_filename

        logger.info(f"Consolidating {len(summary_paths)} summaries to {global_summary_path}")
        consolidate_multi_plate_summaries(
            summary_paths=summary_paths,
            output_path=str(global_summary_path),
            plate_names=plate_names
        )
        logger.info(f"✅ Global summary created: {global_summary_path}")

    def _on_execution_error(self, error_msg):
        """Handle execution error (called from main thread via signal)."""
        self.execution_error.emit(f"Execution error: {error_msg}")
        self.execution_state = "idle"
        self.current_execution_id = None
        self.update_button_states()

    def action_stop_execution(self):
        """Handle Stop Execution via ZMQ.

        First click: Graceful shutdown, button changes to "Force Kill"
        Second click: Force shutdown
        """
        logger.info("🛑 action_stop_execution CALLED")

        if self._zmq_service.zmq_client is None:
            logger.warning("No active ZMQ execution to stop")
            return

        is_force_kill = self.buttons["run_plate"].text() == "Force Kill"

        # Change button to "Force Kill" IMMEDIATELY (before any async operations)
        if not is_force_kill:
            logger.info("🛑 Stop button pressed - changing to Force Kill")
            self.execution_state = "force_kill_ready"
            self.update_button_states()
            QApplication.processEvents()

        self._zmq_service.stop_execution(force=is_force_kill)
    
    def action_code_plate(self):
        """Generate Python code for selected plates and their pipelines (Tier 3)."""
        logger.debug("Code button pressed - generating Python code for plates")

        selected_items = self.get_selected_items()
        if not selected_items:
            if self.plates:
                logger.info("Code button pressed with no selection, falling back to all plates.")
                selected_items = list(self.plates)
            else:
                logger.info("Code button pressed with no plates configured; generating empty template.")
                selected_items = []

        try:
            # Collect plate paths, pipeline data, and per-plate pipeline configs
            plate_paths = []
            pipeline_data = {}
            per_plate_configs = {}  # Store pipeline config for each plate

            for plate_data in selected_items:
                plate_path = plate_data['path']
                plate_paths.append(plate_path)

                # Get pipeline definition for this plate
                definition_pipeline = self._get_current_pipeline_definition(plate_path)
                if not definition_pipeline:
                    logger.warning(f"No pipeline defined for {plate_data['name']}, using empty pipeline")
                    definition_pipeline = []

                pipeline_data[plate_path] = definition_pipeline

                # Get the actual pipeline config from this plate's orchestrator
                if plate_path in self.orchestrators:
                    orchestrator = self.orchestrators[plate_path]
                    per_plate_configs[plate_path] = orchestrator.pipeline_config

            python_code = generate_complete_orchestrator_code(
                plate_paths=plate_paths,
                pipeline_data=pipeline_data,
                global_config=self.global_config,
                per_plate_configs=per_plate_configs or None,
                clean_mode=True
            )

            editor_service = SimpleCodeEditorService(self)
            use_external = os.environ.get('OPENHCS_USE_EXTERNAL_EDITOR', '').lower() in ('1', 'true', 'yes')
            code_data = {
                'clean_mode': True, 'plate_paths': plate_paths,
                'pipeline_data': pipeline_data, 'global_config': self.global_config,
                'per_plate_configs': per_plate_configs
            }
            editor_service.edit_code(
                initial_content=python_code, title="Edit Orchestrator Configuration",
                callback=self._handle_edited_code, use_external=use_external,
                code_type='orchestrator', code_data=code_data
            )

        except Exception as e:
            logger.error(f"Failed to generate plate code: {e}")
            self.service_adapter.show_error_dialog(f"Failed to generate code: {str(e)}")

    # _patch_lazy_constructors() moved to AbstractManagerWidget

    def _ensure_plate_entries_from_code(self, plate_paths: List[str]) -> None:
        """Ensure that any plates referenced in orchestrator code exist in the UI list."""
        if not plate_paths:
            return

        existing_paths = {str(plate['path']) for plate in self.plates}
        added_count = 0

        for plate_path in plate_paths:
            plate_str = str(plate_path)
            if plate_str in existing_paths:
                continue

            plate_name = Path(plate_str).name or plate_str
            self.plates.append({'name': plate_name, 'path': plate_str})
            existing_paths.add(plate_str)
            added_count += 1
            logger.info(f"Added plate '{plate_name}' from orchestrator code")

        if added_count:
            if self.item_list:
                self.update_item_list()
            status_message = f"Added {added_count} plate(s) from orchestrator code"
            self.status_message.emit(status_message)
            logger.info(status_message)

    def _get_orchestrator_for_path(self, plate_path: str):
        """Return orchestrator instance for the provided plate path string."""
        plate_key = str(plate_path)
        if plate_key in self.orchestrators:
            return self.orchestrators[plate_key]

        for key, orchestrator in self.orchestrators.items():
            if str(key) == plate_key:
                return orchestrator
        return None

    # === Code Execution Hooks (ABC _handle_edited_code template) ===

    def _pre_code_execution(self) -> None:
        """Open pipeline editor window before processing orchestrator code."""
        main_window = self._find_main_window()
        if main_window and hasattr(main_window, 'show_pipeline_editor'):
            main_window.show_pipeline_editor()

    def _apply_executed_code(self, namespace: dict) -> bool:
        """Extract orchestrator variables from namespace and apply to widget state."""
        if 'plate_paths' not in namespace or 'pipeline_data' not in namespace:
            return False

        new_plate_paths = namespace['plate_paths']
        new_pipeline_data = namespace['pipeline_data']
        self._ensure_plate_entries_from_code(new_plate_paths)

        # Update global config if present
        if 'global_config' in namespace:
            self._apply_global_config_from_code(namespace['global_config'])

        # Handle per-plate configs (preferred) or single pipeline_config (legacy)
        if 'per_plate_configs' in namespace:
            self._apply_per_plate_configs_from_code(namespace['per_plate_configs'])
        elif 'pipeline_config' in namespace:
            self._apply_legacy_pipeline_config_from_code(namespace['pipeline_config'], new_plate_paths)

        # Update pipeline data for ALL affected plates
        self._apply_pipeline_data_from_code(new_pipeline_data)

        return True

    def _apply_global_config_from_code(self, new_global_config) -> None:
        """Apply global config from executed code."""
        self.global_config = new_global_config

        # Apply to all orchestrators
        for orchestrator in self.orchestrators.values():
            self._update_orchestrator_global_config(orchestrator, new_global_config)

        # Update service adapter
        self.service_adapter.set_global_config(new_global_config)
        self.global_config_changed.emit()

        # Broadcast to event bus
        self._broadcast_to_event_bus('config', new_global_config)

    def _apply_per_plate_configs_from_code(self, per_plate_configs: dict) -> None:
        """Apply per-plate pipeline configs from executed code."""
        last_pipeline_config = None
        for plate_path_str, new_pipeline_config in per_plate_configs.items():
            plate_key = str(plate_path_str)
            self.plate_configs[plate_key] = new_pipeline_config

            orchestrator = self._get_orchestrator_for_path(plate_key)
            if orchestrator:
                orchestrator.apply_pipeline_config(new_pipeline_config)
                effective_config = orchestrator.get_effective_config()
                self.orchestrator_config_changed.emit(str(orchestrator.plate_path), effective_config)
                logger.debug(f"Applied per-plate pipeline config to orchestrator: {orchestrator.plate_path}")
            else:
                logger.info(f"Stored pipeline config for {plate_key}; will apply when initialized.")

            last_pipeline_config = new_pipeline_config

        # Broadcast last config to event bus
        if last_pipeline_config:
            self._broadcast_to_event_bus('config', last_pipeline_config)

    def _apply_legacy_pipeline_config_from_code(self, new_pipeline_config, plate_paths: list) -> None:
        """Apply legacy single pipeline_config to all plates."""
        # Broadcast to event bus
        self._broadcast_to_event_bus('config', new_pipeline_config)

        # Apply to all affected orchestrators
        for plate_path in plate_paths:
            if plate_path in self.orchestrators:
                orchestrator = self.orchestrators[plate_path]
                orchestrator.apply_pipeline_config(new_pipeline_config)
                effective_config = orchestrator.get_effective_config()
                self.orchestrator_config_changed.emit(str(plate_path), effective_config)
                logger.debug(f"Applied tier 3 pipeline config to orchestrator: {plate_path}")

    def _apply_pipeline_data_from_code(self, new_pipeline_data: dict) -> None:
        """Apply pipeline data for ALL affected plates with proper state invalidation."""
        if not self.pipeline_editor or not hasattr(self.pipeline_editor, 'plate_pipelines'):
            logger.warning("No pipeline editor available to update pipeline data")
            self.pipeline_data_changed.emit()
            return

        current_plate = getattr(self.pipeline_editor, 'current_plate', None)

        for plate_path, new_steps in new_pipeline_data.items():
            # Update pipeline data in the pipeline editor
            self.pipeline_editor.plate_pipelines[plate_path] = new_steps
            logger.debug(f"Updated pipeline for {plate_path} with {len(new_steps)} steps")

            # Invalidate orchestrator state
            self._invalidate_orchestrator_compilation_state(plate_path)

            # If this is the currently displayed plate, trigger UI cascade
            if plate_path == current_plate:
                self.pipeline_editor.pipeline_steps = new_steps
                self.pipeline_editor.update_item_list()
                self.pipeline_editor.pipeline_changed.emit(new_steps)
                self._broadcast_to_event_bus('pipeline', new_steps)
                logger.debug(f"Triggered UI cascade refresh for current plate: {plate_path}")

        self.pipeline_data_changed.emit()

    # _broadcast_config_to_event_bus() and _broadcast_pipeline_to_event_bus() REMOVED
    # Now using ABC's generic _broadcast_to_event_bus(event_type, data)

    def _invalidate_orchestrator_compilation_state(self, plate_path: str):
        """Invalidate compilation state for an orchestrator when its pipeline changes.

        This ensures that tier 3 changes properly invalidate ALL affected orchestrators,
        not just the currently visible one.

        Args:
            plate_path: Path of the plate whose orchestrator state should be invalidated
        """
        # Clear compiled data from simple state
        if plate_path in self.plate_compiled_data:
            del self.plate_compiled_data[plate_path]
            logger.debug(f"Cleared compiled data for {plate_path}")

        orchestrator = self.orchestrators.get(plate_path)
        if orchestrator and orchestrator.state == OrchestratorState.COMPILED:
            orchestrator._state = OrchestratorState.READY
            self.orchestrator_state_changed.emit(plate_path, "READY")

    def action_view_metadata(self):
        """View plate images and metadata in tabbed window."""
        selected_items = self.get_selected_items()
        if not selected_items:
            self.service_adapter.show_error_dialog("No plates selected.")
            return

        for item in selected_items:
            plate_path = item['path']

            # Check if orchestrator is initialized
            if plate_path not in self.orchestrators:
                self.service_adapter.show_error_dialog(f"Plate must be initialized to view: {plate_path}")
                continue

            orchestrator = self.orchestrators[plate_path]

            try:
                # Create plate viewer window with tabs (Image Browser + Metadata)
                viewer = PlateViewerWindow(
                    orchestrator=orchestrator,
                    color_scheme=self.color_scheme,
                    parent=self
                )
                viewer.show()  # Use show() instead of exec() to allow multiple windows
            except Exception as e:
                logger.error(f"Failed to open plate viewer for {plate_path}: {e}", exc_info=True)
                self.service_adapter.show_error_dialog(f"Failed to open plate viewer: {str(e)}")

    # ========== UI Helper Methods ==========

    # update_item_list() REMOVED - uses ABC template with list update hooks

    def get_selected_orchestrator(self):
        """
        Get the orchestrator for the currently selected plate.

        Returns:
            PipelineOrchestrator or None if no plate selected or not initialized
        """
        if self.selected_plate_path and self.selected_plate_path in self.orchestrators:
            return self.orchestrators[self.selected_plate_path]
        return None
    
    def update_button_states(self):
        """Update button enabled/disabled states based on selection."""
        selected_plates = self.get_selected_items()
        has_selection = len(selected_plates) > 0
        def _plate_is_initialized(plate_dict):
            orchestrator = self.orchestrators.get(plate_dict['path'])
            return orchestrator and orchestrator.state != OrchestratorState.CREATED

        has_initialized = any(_plate_is_initialized(plate) for plate in selected_plates)
        has_compiled = any(plate['path'] in self.plate_compiled_data for plate in selected_plates)
        is_running = self.is_any_plate_running()

        # Update button states (logic extracted from Textual version)
        self.buttons["del_plate"].setEnabled(has_selection and not is_running)
        self.buttons["edit_config"].setEnabled(has_initialized and not is_running)
        self.buttons["init_plate"].setEnabled(has_selection and not is_running)
        self.buttons["compile_plate"].setEnabled(has_initialized and not is_running)
        # Code button available even without initialized plates so users can edit templates
        self.buttons["code_plate"].setEnabled(not is_running)
        self.buttons["view_metadata"].setEnabled(has_initialized and not is_running)

        # Run button - enabled if plates are compiled or if currently running (for stop)
        if self.execution_state == "stopping":
            # Stopping state - keep button as "Stop" but disable it
            self.buttons["run_plate"].setEnabled(False)
            self.buttons["run_plate"].setText("Stop")
        elif self.execution_state == "force_kill_ready":
            # Force kill ready state - button is "Force Kill" and enabled
            self.buttons["run_plate"].setEnabled(True)
            self.buttons["run_plate"].setText("Force Kill")
        elif is_running:
            # Running state - button is "Stop" and enabled
            self.buttons["run_plate"].setEnabled(True)
            self.buttons["run_plate"].setText("Stop")
        else:
            # Idle state - button is "Run" and enabled if plates are compiled
            self.buttons["run_plate"].setEnabled(has_compiled)
            self.buttons["run_plate"].setText("Run")
    
    def is_any_plate_running(self) -> bool:
        """
        Check if any plate is currently running.

        Returns:
            True if any plate is running, False otherwise
        """
        # Consider "running", "stopping", and "force_kill_ready" states as "busy"
        return self.execution_state in ("running", "stopping", "force_kill_ready")
    
    # Event handlers (on_selection_changed, on_plates_reordered, on_item_double_clicked)
    # provided by AbstractManagerWidget base class
    # Plate-specific behavior implemented via abstract hooks below
    
    def on_orchestrator_state_changed(self, plate_path: str, state: str):
        """
        Handle orchestrator state changes.
        
        Args:
            plate_path: Path of the plate
            state: New orchestrator state
        """
        self.update_item_list()
        logger.debug(f"Orchestrator state changed: {plate_path} -> {state}")
    
    def on_config_changed(self, new_config: GlobalPipelineConfig):
        """
        Handle global configuration changes.

        Args:
            new_config: New global configuration
        """
        self.global_config = new_config

        # Apply new global config to all existing orchestrators
        # This rebuilds their pipeline configs preserving concrete values
        for orchestrator in self.orchestrators.values():
            self._update_orchestrator_global_config(orchestrator, new_config)

        # REMOVED: Thread-local modification - dual-axis resolver handles orchestrator context automatically

        logger.info(f"Applied new global config to {len(self.orchestrators)} orchestrators")

        # SIMPLIFIED: Dual-axis resolver handles placeholder updates automatically

    # REMOVED: _refresh_all_parameter_form_placeholders and _refresh_widget_parameter_forms
    # SIMPLIFIED: Dual-axis resolver handles placeholder updates automatically

    # ========== Helper Methods ==========

    def _get_current_pipeline_definition(self, plate_path: str) -> List:
        """
        Get the current pipeline definition for a plate.

        Args:
            plate_path: Path to the plate

        Returns:
            List of pipeline steps or empty list if no pipeline
        """
        if not self.pipeline_editor:
            logger.warning("No pipeline editor reference - using empty pipeline")
            return []

        # Get pipeline for specific plate (same logic as Textual TUI)
        if hasattr(self.pipeline_editor, 'plate_pipelines') and plate_path in self.pipeline_editor.plate_pipelines:
            pipeline_steps = self.pipeline_editor.plate_pipelines[plate_path]
            logger.debug(f"Found pipeline for plate {plate_path} with {len(pipeline_steps)} steps")
            return pipeline_steps
        else:
            logger.debug(f"No pipeline found for plate {plate_path}, using empty pipeline")
            return []

    def set_pipeline_editor(self, pipeline_editor):
        """
        Set the pipeline editor reference.

        Args:
            pipeline_editor: Pipeline editor widget instance
        """
        self.pipeline_editor = pipeline_editor
        logger.debug("Pipeline editor reference set in plate manager")

    # _find_main_window() moved to AbstractManagerWidget

    def _on_progress_started(self, max_value: int):
        """Handle progress started signal - route to status bar."""
        # Progress is now displayed in the status bar instead of a separate widget
        # This method is kept for signal compatibility but doesn't need to do anything
        pass

    def _on_progress_updated(self, value: int):
        """Handle progress updated signal - route to status bar."""
        # Progress is now displayed in the status bar instead of a separate widget
        # This method is kept for signal compatibility but doesn't need to do anything
        pass

    def _on_progress_finished(self):
        """Handle progress finished signal - route to status bar."""
        # Progress is now displayed in the status bar instead of a separate widget
        # This method is kept for signal compatibility but doesn't need to do anything
        pass

    # ========== Abstract Hook Implementations (AbstractManagerWidget ABC) ==========

    # === CRUD Hooks ===

    def action_add(self) -> None:
        """Add plates via directory chooser."""
        self.action_add_plate()

    def _validate_delete(self, items: List[Any]) -> bool:
        """Check if delete is allowed - no running plates (required abstract method)."""
        if self.is_any_plate_running():
            self.service_adapter.show_error_dialog(
                "Cannot delete plates while execution is in progress.\n"
                "Please stop execution first."
            )
            return False
        return True

    def _perform_delete(self, items: List[Any]) -> None:
        """Remove plates from backing list and cleanup orchestrators (required abstract method)."""
        paths_to_delete = {plate['path'] for plate in items}
        self.plates = [p for p in self.plates if p['path'] not in paths_to_delete]

        # Clean up orchestrators for deleted plates
        for path in paths_to_delete:
            if path in self.orchestrators:
                del self.orchestrators[path]

        if self.selected_plate_path in paths_to_delete:
            self.selected_plate_path = ""
            # Notify pipeline editor that no plate is selected (mirrors Textual TUI)
            self.plate_selected.emit("")

    def _show_item_editor(self, item: Any) -> None:
        """Show config window for plate (required abstract method)."""
        self.action_edit_config()  # Delegate to existing implementation

    # === List Update Hooks (domain-specific) ===

    def _format_list_item(self, item: Any, index: int, context: Any) -> str:
        """Format plate for list display."""
        return self._format_plate_item_with_preview_text(item)

    def _get_list_item_tooltip(self, item: Any) -> str:
        """Get plate tooltip with orchestrator status."""
        if item['path'] in self.orchestrators:
            orchestrator = self.orchestrators[item['path']]
            return f"Status: {orchestrator.state.value}"
        return ""

    def _post_update_list(self) -> None:
        """Auto-select first plate if no selection."""
        if self.plates and not self.selected_plate_path:
            self.item_list.setCurrentRow(0)

    # === Config Resolution Hook ===

    def _get_context_stack_for_resolution(self, item: Any) -> List[Any]:
        """Build 2-element context stack for PlateManager.

        Args:
            item: PipelineOrchestrator - the orchestrator being displayed/edited

        Returns:
            [global_config, pipeline_config] - LiveContextResolver will merge live values internally
        """
        from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator

        # Item is the orchestrator
        if isinstance(item, PipelineOrchestrator):
            pipeline_config = item.pipeline_config
        else:
            # Fallback: assume it's a pipeline_config directly (shouldn't happen with proper refactor)
            pipeline_config = item

        # Return raw objects - LiveContextResolver handles merging live values internally
        return [get_current_global_config(GlobalPipelineConfig), pipeline_config]

    # === CrossWindowPreviewMixin Hook ===

    def _get_current_orchestrator(self):
        """Get orchestrator for current plate (required abstract method)."""
        return self.orchestrators.get(self.selected_plate_path)

    # ========== End Abstract Hook Implementations ==========

    def _handle_compilation_error(self, plate_name: str, error_message: str):
        """Handle compilation error on main thread (slot)."""
        self.service_adapter.show_error_dialog(f"Compilation failed for {plate_name}: {error_message}")

    def _handle_initialization_error(self, plate_name: str, error_message: str):
        """Handle initialization error on main thread (slot)."""
        self.service_adapter.show_error_dialog(f"Failed to initialize {plate_name}: {error_message}")

    def _handle_execution_error(self, error_message: str):
        """Handle execution error on main thread (slot)."""
        self.service_adapter.show_error_dialog(error_message)
