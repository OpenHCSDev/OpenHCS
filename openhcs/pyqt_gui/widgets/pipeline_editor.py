"""
Pipeline Editor Widget for PyQt6

Pipeline step management with full feature parity to Textual TUI version.
Uses hybrid approach: extracted business logic + clean PyQt6 UI.
"""

import logging
import inspect
import copy
from typing import List, Dict, Optional, Callable, Tuple, Any, Iterable, Set
from pathlib import Path

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QListWidget,
    QListWidgetItem, QLabel, QSplitter
)
from PyQt6.QtCore import Qt, pyqtSignal, QTimer
from PyQt6.QtGui import QFont, QColor

from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.config import GlobalPipelineConfig
from openhcs.io.filemanager import FileManager
from openhcs.core.steps.function_step import FunctionStep
# Mixin imports REMOVED - now in ABC (handle_selection_change_with_prevention, CrossWindowPreviewMixin)
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.config import PyQtGUIConfig, get_default_pyqt_gui_config
from openhcs.config_framework import LiveContextResolver

# Import shared list widget components (single source of truth)
from openhcs.pyqt_gui.widgets.shared.reorderable_list_widget import ReorderableListWidget
from openhcs.pyqt_gui.widgets.shared.list_item_delegate import MultilinePreviewItemDelegate
from openhcs.pyqt_gui.widgets.config_preview_formatters import CONFIG_INDICATORS
from openhcs.core.config import ProcessingConfig

# Import ABC base class (Phase 4 migration)
from openhcs.pyqt_gui.widgets.shared.abstract_manager_widget import AbstractManagerWidget

from openhcs.utils.performance_monitor import timer

logger = logging.getLogger(__name__)


class PipelineEditorWidget(AbstractManagerWidget):
    """
    PyQt6 Pipeline Editor Widget.

    Manages pipeline steps with add, edit, delete, load, save functionality.
    Preserves all business logic from Textual version with clean PyQt6 UI.
    """

    # Declarative UI configuration
    TITLE = "Pipeline Editor"
    BUTTON_GRID_COLUMNS = 0  # Single row (1 x N grid)
    BUTTON_CONFIGS = [
        ("Add", "add_step", "Add new pipeline step"),
        ("Del", "del_step", "Delete selected steps"),
        ("Edit", "edit_step", "Edit selected step"),
        ("Auto", "auto_load_pipeline", "Load basic_pipeline.py"),
        ("Code", "code_pipeline", "Edit pipeline as Python code"),
    ]
    ACTION_REGISTRY = {
        "add_step": "action_add",  # Uses action_add() which delegates to action_add_step()
        "del_step": "action_delete",  # Uses ABC template with _perform_delete() hook
        "edit_step": "action_edit",  # Uses ABC template with _show_item_editor() hook
        "auto_load_pipeline": "action_auto_load_pipeline",
        "code_pipeline": "action_code_pipeline",
    }
    ITEM_NAME_SINGULAR = "step"
    ITEM_NAME_PLURAL = "steps"

    # Declarative item hooks (replaces 9 trivial method overrides)
    ITEM_HOOKS = {
        'id_accessor': ('attr', 'name'),          # getattr(item, 'name')
        'backing_attr': 'pipeline_steps',         # self.pipeline_steps
        'selection_attr': 'selected_step',        # self.selected_step = ...
        'selection_signal': 'step_selected',      # self.step_selected.emit(...)
        'selection_emit_id': False,               # emit the full step object
        'selection_clear_value': None,            # emit None when cleared
        'items_changed_signal': 'pipeline_changed',  # emit on changes
        'preserve_selection_pred': lambda self: bool(self.pipeline_steps),
        'list_item_data': 'index',                # store index, not item
    }

    # Declarative item hooks (replaces 9 trivial method overrides)
    ITEM_HOOKS = {
        'id_accessor': ('attr', 'name'),          # getattr(item, 'name', '')
        'backing_attr': 'pipeline_steps',         # self.pipeline_steps
        'selection_attr': 'selected_step',        # self.selected_step = ...
        'selection_signal': 'step_selected',      # self.step_selected.emit(...)
        'selection_emit_id': False,               # emit the full step object
        'selection_clear_value': None,            # emit None when cleared
        'items_changed_signal': 'pipeline_changed',  # self.pipeline_changed.emit(...)
        'preserve_selection_pred': lambda self: bool(self.pipeline_steps),
        'list_item_data': 'index',                # store the step index
    }

    # Declarative preview field configuration (processed automatically in ABC.__init__)
    PREVIEW_FIELD_CONFIGS = [
        'napari_streaming_config',  # Uses CONFIG_INDICATORS['napari_streaming_config'] = 'NAP'
        'fiji_streaming_config',    # Uses CONFIG_INDICATORS['fiji_streaming_config'] = 'FIJI'
        'step_materialization_config',  # Uses CONFIG_INDICATORS['step_materialization_config'] = 'MAT'
    ]

    STEP_SCOPE_ATTR = "_pipeline_scope_token"

    # Signals
    pipeline_changed = pyqtSignal(list)  # List[FunctionStep]
    step_selected = pyqtSignal(object)  # FunctionStep
    status_message = pyqtSignal(str)  # status message
    
    def __init__(self, service_adapter, color_scheme: Optional[PyQt6ColorScheme] = None,
                 gui_config: Optional[PyQtGUIConfig] = None, parent=None):
        """
        Initialize the pipeline editor widget.

        Args:
            service_adapter: PyQt service adapter for dialogs and operations
            color_scheme: Color scheme for styling (optional, uses service adapter if None)
            gui_config: GUI configuration (optional, for DualEditorWindow)
            parent: Parent widget
        """
        # Step-specific state (BEFORE super().__init__)
        self.pipeline_steps: List[FunctionStep] = []
        self.current_plate: str = ""
        self.selected_step: str = ""
        self.plate_pipelines: Dict[str, List[FunctionStep]] = {}  # Per-plate pipeline storage

        # Reference to plate manager (set externally)
        # Note: orchestrator is looked up dynamically via _get_current_orchestrator()
        self.plate_manager = None

        # Step scope management
        self._preview_step_cache: Dict[int, FunctionStep] = {}
        self._preview_step_cache_token: Optional[int] = None
        self._next_scope_token = 0  # Counter for generating unique step scope tokens

        # Initialize base class (creates style_generator, event_bus, item_list, buttons, status_label internally)
        # Also auto-processes PREVIEW_FIELD_CONFIGS declaratively
        super().__init__(service_adapter, color_scheme, gui_config, parent)

        # Setup UI (after base and subclass state is ready)
        self.setup_ui()
        self.setup_connections()
        self.update_button_states()

        logger.debug("Pipeline editor widget initialized")

    # UI infrastructure provided by AbstractManagerWidget base class
    # Step-specific customizations via hooks below

    def setup_connections(self):
        """Setup signal/slot connections (base class + step-specific)."""
        # Call base class connection setup (handles item list selection, double-click, reordering, status)
        self._setup_connections()

        # Step-specific signal
        self.pipeline_changed.connect(self.on_pipeline_changed)
    
    # ========== Business Logic Methods (Extracted from Textual) ==========
    
    def format_item_for_display(self, step: FunctionStep, live_context_snapshot=None) -> Tuple[str, str]:
        """
        Format step for display in the list with constructor value preview.

        Args:
            step: FunctionStep to format
            live_context_snapshot: Optional pre-collected LiveContextSnapshot (for performance)

        Returns:
            Tuple of (display_text, step_name)
        """
        step_for_display = self._get_step_preview_instance(step, live_context_snapshot)
        step_name = getattr(step_for_display, 'name', 'Unknown Step')
        processing_cfg = getattr(step_for_display, 'processing_config', None)

        # Build preview of key constructor values
        preview_parts = []

        # Function preview
        func = getattr(step_for_display, 'func', None)
        if func:
            if isinstance(func, list) and func:
                # Count enabled functions (filter out None/disabled)
                enabled_funcs = [f for f in func if f is not None]
                preview_parts.append(f"func=[{len(enabled_funcs)} functions]")
            elif callable(func):
                func_name = getattr(func, '__name__', str(func))
                preview_parts.append(f"func={func_name}")
            elif isinstance(func, dict):
                # Show dict keys with metadata names (like groupby selector)
                orchestrator = self._get_current_orchestrator()
                group_by = getattr(step_for_display.processing_config, 'group_by', None) if hasattr(step_for_display, 'processing_config') else None

                dict_items = []
                for key in sorted(func.keys()):
                    if orchestrator and group_by:
                        metadata_name = orchestrator.metadata_cache.get_component_metadata(group_by, key)
                        if metadata_name:
                            dict_items.append(f"{key}|{metadata_name}")
                        else:
                            dict_items.append(key)
                    else:
                        dict_items.append(key)

                preview_parts.append(f"func={{{', '.join(dict_items)}}}")

        # Variable components preview
        var_components = getattr(step_for_display, 'variable_components', None)
        if var_components is None and processing_cfg is not None:
            var_components = getattr(processing_cfg, 'variable_components', None)
        if var_components:
            if len(var_components) == 1:
                comp_name = getattr(var_components[0], 'name', str(var_components[0]))
                preview_parts.append(f"components=[{comp_name}]")
            else:
                comp_names = [getattr(c, 'name', str(c)) for c in var_components[:2]]
                if len(var_components) > 2:
                    comp_names.append(f"+{len(var_components)-2} more")
                preview_parts.append(f"components=[{', '.join(comp_names)}]")

        # Group by preview
        group_by = getattr(step_for_display, 'group_by', None)
        if (group_by is None or getattr(group_by, 'value', None) is None) and processing_cfg is not None:
            group_by = getattr(processing_cfg, 'group_by', None)
        if group_by and group_by.value is not None:  # Check for GroupBy.NONE
            group_name = getattr(group_by, 'name', str(group_by))
            preview_parts.append(f"group_by={group_name}")

        # Input source preview (access from processing_config)
        input_source = getattr(step_for_display.processing_config, 'input_source', None) if hasattr(step_for_display, 'processing_config') else None
        if input_source:
            source_name = getattr(input_source, 'name', str(input_source))
            if source_name != 'PREVIOUS_STEP':  # Only show if not default
                preview_parts.append(f"input={source_name}")

        # Optional configurations preview - use ABC's unified preview label builder
        # CRITICAL: Must resolve through context hierarchy (Global -> Pipeline -> Step)
        # to match the same resolution that step editor placeholders use
        # Uses the same API as PlateManager for consistency
        config_labels = self._build_preview_labels(
            item=step_for_display,  # Semantic item for context stack
            config_source=step_for_display,
            live_context_snapshot=live_context_snapshot,
        )

        if config_labels:
            preview_parts.append(f"configs=[{','.join(config_labels)}]")

        # Build display text
        if preview_parts:
            preview = " | ".join(preview_parts)
            display_text = f"▶ {step_name}  ({preview})"
        else:
            display_text = f"▶ {step_name}"

        return display_text, step_name

    def _create_step_tooltip(self, step: FunctionStep) -> str:
        """Create detailed tooltip for a step showing all constructor values."""
        step_name = getattr(step, 'name', 'Unknown Step')
        tooltip_lines = [f"Step: {step_name}"]

        # Function details
        func = getattr(step, 'func', None)
        if func:
            if isinstance(func, list):
                if len(func) == 1:
                    func_name = getattr(func[0], '__name__', str(func[0]))
                    tooltip_lines.append(f"Function: {func_name}")
                else:
                    func_names = [getattr(f, '__name__', str(f)) for f in func[:3]]
                    if len(func) > 3:
                        func_names.append(f"... +{len(func)-3} more")
                    tooltip_lines.append(f"Functions: {', '.join(func_names)}")
            elif callable(func):
                func_name = getattr(func, '__name__', str(func))
                tooltip_lines.append(f"Function: {func_name}")
            elif isinstance(func, dict):
                tooltip_lines.append(f"Function: Dictionary with {len(func)} routing keys")
        else:
            tooltip_lines.append("Function: None")

        # Variable components
        var_components = getattr(step, 'variable_components', None)
        if var_components:
            comp_names = [getattr(c, 'name', str(c)) for c in var_components]
            tooltip_lines.append(f"Variable Components: [{', '.join(comp_names)}]")
        else:
            tooltip_lines.append("Variable Components: None")

        # Group by
        group_by = getattr(step, 'group_by', None)
        if group_by and group_by.value is not None:  # Check for GroupBy.NONE
            group_name = getattr(group_by, 'name', str(group_by))
            tooltip_lines.append(f"Group By: {group_name}")
        else:
            tooltip_lines.append("Group By: None")

        # Input source (access from processing_config)
        input_source = getattr(step.processing_config, 'input_source', None) if hasattr(step, 'processing_config') else None
        if input_source:
            source_name = getattr(input_source, 'name', str(input_source))
            tooltip_lines.append(f"Input Source: {source_name}")
        else:
            tooltip_lines.append("Input Source: None")

        # Additional configurations with details - generic introspection-based approach
        config_details = []

        # Helper to format config details based on type
        def format_config_detail(config_attr: str, config) -> str:
            """Format config detail string based on config type."""
            if config_attr == 'step_materialization_config':
                return "• Materialization Config: Enabled"
            elif config_attr == 'napari_streaming_config':
                port = getattr(config, 'port', 'default')
                return f"• Napari Streaming: Port {port}"
            elif config_attr == 'fiji_streaming_config':
                return "• Fiji Streaming: Enabled"
            elif config_attr == 'step_well_filter_config':
                well_filter = getattr(config, 'well_filter', 'default')
                return f"• Well Filter: {well_filter}"
            else:
                # Generic fallback for unknown config types
                return f"• {config_attr.replace('_', ' ').title()}: Enabled"

        # Use the unified preview field API to get config attributes
        from openhcs.pyqt_gui.widgets.config_preview_formatters import CONFIG_INDICATORS
        for config_attr in CONFIG_INDICATORS.keys():
            if hasattr(step, config_attr):
                config = getattr(step, config_attr, None)
                if config:
                    # Check if config has 'enabled' field - if so, check it; otherwise just check existence
                    should_show = config.enabled if hasattr(config, 'enabled') else True
                    if should_show:
                        config_details.append(format_config_detail(config_attr, config))

        if config_details:
            tooltip_lines.append("")  # Empty line separator
            tooltip_lines.extend(config_details)

        return '\n'.join(tooltip_lines)

    def action_add_step(self):
        """Handle Add Step button (adapted from Textual version)."""

        from openhcs.core.steps.function_step import FunctionStep
        from openhcs.pyqt_gui.windows.dual_editor_window import DualEditorWindow

        # Get orchestrator for step creation
        orchestrator = self._get_current_orchestrator()

        # Create new step
        step_name = f"Step_{len(self.pipeline_steps) + 1}"
        new_step = FunctionStep(
            func=[],  # Start with empty function list
            name=step_name
        )
        self._ensure_step_scope_token(new_step)



        def handle_save(edited_step):
            """Handle step save from editor."""
            # Check if step already exists in pipeline (for Shift+Click saves)
            if edited_step not in self.pipeline_steps:
                self.pipeline_steps.append(edited_step)
                self._ensure_step_scope_token(edited_step)
                self.status_message.emit(f"Added new step: {edited_step.name}")
            else:
                # Step already exists, just update the display
                self.status_message.emit(f"Updated step: {edited_step.name}")

            self.update_item_list()
            self.pipeline_changed.emit(self.pipeline_steps)

        # Create and show editor dialog within the correct config context
        orchestrator = self._get_current_orchestrator()

        # SIMPLIFIED: Orchestrator context is automatically available through type-based registry
        # No need for explicit context management - dual-axis resolver handles it automatically
        if not orchestrator:
            logger.info("No orchestrator found for step editor context, This should not happen.")

        editor = DualEditorWindow(
            step_data=new_step,
            is_new=True,
            on_save_callback=handle_save,
            orchestrator=orchestrator,
            gui_config=self.gui_config,
            parent=self
        )
        # Set original step for change detection
        editor.set_original_step_for_change_detection()

        # Connect orchestrator config changes to step editor for live placeholder updates
        # This ensures the step editor's placeholders update when pipeline config is saved
        if self.plate_manager and hasattr(self.plate_manager, 'orchestrator_config_changed'):
            self.plate_manager.orchestrator_config_changed.connect(editor.on_orchestrator_config_changed)
            logger.debug("Connected orchestrator_config_changed signal to step editor")

        editor.show()
        editor.raise_()
        editor.activateWindow()

    # action_delete_step() REMOVED - now uses ABC's action_delete() template with _perform_delete() hook
    # action_edit_step() REMOVED - now uses ABC's action_edit() template with _show_item_editor() hook

    def action_auto_load_pipeline(self):
        """Handle Auto button - load basic_pipeline.py automatically."""
        if not self.current_plate:
            self.service_adapter.show_error_dialog("No plate selected")
            return

        try:
            # Use module import to find basic_pipeline.py
            import openhcs.tests.basic_pipeline as basic_pipeline_module
            import inspect

            # Get the source code from the module
            python_code = inspect.getsource(basic_pipeline_module)

            # Execute the code to get pipeline_steps (same as _handle_edited_pipeline_code)
            namespace = {}
            with self._patch_lazy_constructors():
                exec(python_code, namespace)

            # Get the pipeline_steps from the namespace
            if 'pipeline_steps' in namespace:
                new_pipeline_steps = namespace['pipeline_steps']
                # Update the pipeline with new steps
                self.pipeline_steps = new_pipeline_steps
                self._normalize_step_scope_tokens()
                self.update_item_list()
                self.pipeline_changed.emit(self.pipeline_steps)
                self.status_message.emit(f"Auto-loaded {len(new_pipeline_steps)} steps from basic_pipeline.py")
            else:
                raise ValueError("No 'pipeline_steps = [...]' assignment found in basic_pipeline.py")

        except Exception as e:
            import traceback
            logger.error(f"Failed to auto-load basic_pipeline.py: {e}")
            logger.error(f"Full traceback:\n{traceback.format_exc()}")
            self.service_adapter.show_error_dialog(f"Failed to auto-load pipeline: {str(e)}")
    
    def action_code_pipeline(self):
        """Handle Code Pipeline button - edit pipeline as Python code."""
        logger.debug("Code button pressed - opening code editor")

        if not self.current_plate:
            self.service_adapter.show_error_dialog("No plate selected")
            return

        try:
            # Use complete pipeline steps code generation
            from openhcs.debug.pickle_to_python import generate_complete_pipeline_steps_code

            # Generate complete pipeline steps code with imports
            python_code = generate_complete_pipeline_steps_code(
                pipeline_steps=list(self.pipeline_steps),
                clean_mode=True
            )

            # Create simple code editor service
            from openhcs.pyqt_gui.services.simple_code_editor import SimpleCodeEditorService
            editor_service = SimpleCodeEditorService(self)

            # Check if user wants external editor (check environment variable)
            import os
            use_external = os.environ.get('OPENHCS_USE_EXTERNAL_EDITOR', '').lower() in ('1', 'true', 'yes')

            # Launch editor with callback - uses ABC _handle_edited_code template
            editor_service.edit_code(
                initial_content=python_code,
                title="Edit Pipeline Steps",
                callback=self._handle_edited_code,  # ABC template method
                use_external=use_external,
                code_type='pipeline',
                code_data={'clean_mode': True}
            )

        except Exception as e:
            logger.error(f"Failed to open pipeline code editor: {e}")
            self.service_adapter.show_error_dialog(f"Failed to open code editor: {str(e)}")

    # === Code Execution Hooks (ABC _handle_edited_code template) ===

    def _handle_code_execution_error(self, code: str, error: Exception, namespace: dict) -> Optional[dict]:
        """Handle old-format step constructors by retrying with migration patch."""
        error_msg = str(error)
        if "unexpected keyword argument" in error_msg and ("group_by" in error_msg or "variable_components" in error_msg):
            logger.info(f"Detected old-format step constructor, retrying with migration patch: {error}")
            new_namespace = {}
            from openhcs.io.pipeline_migration import patch_step_constructors_for_migration
            with self._patch_lazy_constructors(), patch_step_constructors_for_migration():
                exec(code, new_namespace)
            return new_namespace
        return None  # Re-raise error

    def _apply_executed_code(self, namespace: dict) -> bool:
        """Extract pipeline_steps from namespace and apply to widget state."""
        if 'pipeline_steps' not in namespace:
            return False

        new_pipeline_steps = namespace['pipeline_steps']
        self.pipeline_steps = new_pipeline_steps
        self._normalize_step_scope_tokens()
        self.update_item_list()
        self.pipeline_changed.emit(self.pipeline_steps)
        self.status_message.emit(f"Pipeline updated with {len(new_pipeline_steps)} steps")

        # Broadcast to global event bus for ALL windows to receive
        self._broadcast_to_event_bus('pipeline', new_pipeline_steps)
        return True

    def _get_code_missing_error_message(self) -> str:
        """Error message when pipeline_steps variable is missing."""
        return "No 'pipeline_steps = [...]' assignment found in edited code"

    # _patch_lazy_constructors() and _post_code_execution() provided by ABC

    def load_pipeline_from_file(self, file_path: Path):
        """
        Load pipeline from file with automatic migration for backward compatibility.

        Args:
            file_path: Path to pipeline file
        """
        try:
            # Use migration utility to load with backward compatibility
            from openhcs.io.pipeline_migration import load_pipeline_with_migration

            steps = load_pipeline_with_migration(file_path)

            if steps is not None:
                self.pipeline_steps = steps
                self._normalize_step_scope_tokens()
                self.update_item_list()
                self.pipeline_changed.emit(self.pipeline_steps)
                self.status_message.emit(f"Loaded {len(steps)} steps from {file_path.name}")
            else:
                self.status_message.emit(f"Invalid pipeline format in {file_path.name}")

        except Exception as e:
            logger.error(f"Failed to load pipeline: {e}")
            self.service_adapter.show_error_dialog(f"Failed to load pipeline: {e}")
    
    def save_pipeline_to_file(self, file_path: Path):
        """
        Save pipeline to file (extracted from Textual version).
        
        Args:
            file_path: Path to save pipeline
        """
        try:
            import dill as pickle
            with open(file_path, 'wb') as f:
                pickle.dump(list(self.pipeline_steps), f)
            self.status_message.emit(f"Saved pipeline to {file_path.name}")
            
        except Exception as e:
            logger.error(f"Failed to save pipeline: {e}")
            self.service_adapter.show_error_dialog(f"Failed to save pipeline: {e}")
    
    def save_pipeline_for_plate(self, plate_path: str, pipeline: List[FunctionStep]):
        """
        Save pipeline for specific plate (extracted from Textual version).
        
        Args:
            plate_path: Path of the plate
            pipeline: Pipeline steps to save
        """
        self.plate_pipelines[plate_path] = pipeline
        logger.debug(f"Saved pipeline for plate: {plate_path}")
    
    def set_current_plate(self, plate_path: str):
        """
        Set current plate and load its pipeline (extracted from Textual version).

        Args:
            plate_path: Path of the current plate
        """
        logger.info(f"🔔 RECEIVED set_current_plate signal: {plate_path}")
        self.current_plate = plate_path

        # Load pipeline for the new plate
        if plate_path:
            plate_pipeline = self.plate_pipelines.get(plate_path, [])
            self.pipeline_steps = plate_pipeline
            logger.info(f"  → Loaded {len(plate_pipeline)} steps for plate")
        else:
            self.pipeline_steps = []
            logger.info(f"  → No plate selected, cleared pipeline")

        self._normalize_step_scope_tokens()

        self.update_item_list()
        self.update_button_states()
        logger.info(f"  → Pipeline editor updated for plate: {plate_path}")

    # _broadcast_to_event_bus() REMOVED - now using ABC's generic _broadcast_to_event_bus(event_type, data)

    def on_orchestrator_config_changed(self, plate_path: str, effective_config):
        """
        Handle orchestrator configuration changes for placeholder refresh.

        Args:
            plate_path: Path of the plate whose orchestrator config changed
            effective_config: The orchestrator's new effective configuration
        """
        # Only refresh if this is for the current plate
        if plate_path == self.current_plate:
            logger.debug(f"Refreshing placeholders for orchestrator config change: {plate_path}")

            # SIMPLIFIED: Orchestrator context is automatically available through type-based registry
            # No need for explicit context management - dual-axis resolver handles it automatically
            orchestrator = self._get_current_orchestrator()
            if orchestrator:
                # Trigger refresh of any open configuration windows or step forms
                # The type-based registry ensures they resolve against the updated orchestrator config
                logger.debug(f"Step forms will now resolve against updated orchestrator config for: {plate_path}")
            else:
                logger.debug(f"No orchestrator found for config refresh: {plate_path}")

    # _resolve_config_attr() DELETED - use base class version
    # Step-specific context stack provided via _get_context_stack_for_resolution() hook

    def _build_step_scope_id(self, step: FunctionStep) -> Optional[str]:
        """Return the hierarchical scope id for a step editor instance."""
        token = self._ensure_step_scope_token(step)
        plate_scope = self.current_plate or "no_plate"
        return f"{plate_scope}::{token}"

    def _ensure_step_scope_token(self, step: FunctionStep) -> str:
        token = getattr(step, self.STEP_SCOPE_ATTR, None)
        if not token:
            token = f"step_{self._next_scope_token}"
            self._next_scope_token += 1
            setattr(step, self.STEP_SCOPE_ATTR, token)
        return token

    def _transfer_scope_token(self, source_step: FunctionStep, target_step: FunctionStep) -> None:
        token = getattr(source_step, self.STEP_SCOPE_ATTR, None)
        if token:
            setattr(target_step, self.STEP_SCOPE_ATTR, token)

    def _normalize_step_scope_tokens(self) -> None:
        for step in self.pipeline_steps:
            self._ensure_step_scope_token(step)

    # _merge_with_live_values() DELETED - use _merge_with_live_values() from base class

    def _get_step_preview_instance(self, step: FunctionStep, live_context_snapshot) -> FunctionStep:
        """Return a step instance that includes any live overrides for previews."""
        if live_context_snapshot is None:
            return step

        token = getattr(live_context_snapshot, 'token', None)
        if token is None:
            return step

        if self._preview_step_cache_token != token:
            self._preview_step_cache.clear()
            self._preview_step_cache_token = token

        cache_key = id(step)
        cached_step = self._preview_step_cache.get(cache_key)
        if cached_step is not None:
            return cached_step

        scope_id = self._build_step_scope_id(step)
        if not scope_id:
            self._preview_step_cache[cache_key] = step
            return step

        scoped_values = getattr(live_context_snapshot, 'scoped_values', {}) or {}
        scope_entries = scoped_values.get(scope_id)
        if not scope_entries:
            self._preview_step_cache[cache_key] = step
            return step

        step_live_values = scope_entries.get(type(step))
        if not step_live_values:
            self._preview_step_cache[cache_key] = step
            return step

        merged_step = self._merge_with_live_values(step, step_live_values)
        self._preview_step_cache[cache_key] = merged_step
        return merged_step

    def _handle_full_preview_refresh(self) -> None:
        """Refresh all step preview labels."""
        self.update_item_list()

    def _refresh_step_items_by_index(self, indices: Iterable[int], live_context_snapshot=None) -> None:
        if not indices:
            return

        if live_context_snapshot is None:
            from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

            if not self.current_plate:
                return
            live_context_snapshot = ParameterFormManager.collect_live_context(scope_filter=self.current_plate)

        for step_index in sorted(set(indices)):
            if step_index < 0 or step_index >= len(self.pipeline_steps):
                continue
            item = self.item_list.item(step_index)
            if item is None:
                continue
            step = self.pipeline_steps[step_index]
            old_text = item.text()
            display_text, _ = self.format_item_for_display(step, live_context_snapshot)
            if item.text() != display_text:
                item.setText(display_text)
            item.setData(Qt.ItemDataRole.UserRole, step_index)
            item.setData(Qt.ItemDataRole.UserRole + 1, not step.enabled)
            item.setToolTip(self._create_step_tooltip(step))

    # ========== UI Helper Methods ==========

    # update_item_list() REMOVED - uses ABC template with list update hooks

    def update_button_states(self):
        """Update button enabled/disabled states based on mathematical constraints (mirrors Textual TUI)."""
        has_plate = bool(self.current_plate)
        is_initialized = self._is_current_plate_initialized()
        has_steps = len(self.pipeline_steps) > 0
        has_selection = len(self.get_selected_items()) > 0

        # Mathematical constraints (mirrors Textual TUI logic):
        # - Pipeline editing requires initialization
        # - Step operations require steps to exist
        # - Edit requires valid selection
        self.buttons["add_step"].setEnabled(has_plate and is_initialized)
        self.buttons["auto_load_pipeline"].setEnabled(has_plate and is_initialized)
        self.buttons["del_step"].setEnabled(has_steps)
        self.buttons["edit_step"].setEnabled(has_steps and has_selection)
        self.buttons["code_pipeline"].setEnabled(has_plate and is_initialized)  # Same as add button - orchestrator init is sufficient
    
    # Event handlers (update_status, on_selection_changed, on_item_double_clicked, on_steps_reordered)
    # DELETED - provided by AbstractManagerWidget base class
    # Step-specific behavior implemented via abstract hooks (see end of file)

    def on_pipeline_changed(self, steps: List[FunctionStep]):
        """
        Handle pipeline changes.
        
        Args:
            steps: New pipeline steps
        """
        # Save pipeline to current plate if one is selected
        if self.current_plate:
            self.save_pipeline_for_plate(self.current_plate, steps)
        
        logger.debug(f"Pipeline changed: {len(steps)} steps")

    def _is_current_plate_initialized(self) -> bool:
        """Check if current plate has an initialized orchestrator (mirrors Textual TUI)."""
        if not self.current_plate:
            return False

        # Get plate manager from main window
        main_window = self._find_main_window()
        if not main_window:
            return False

        # Get plate manager widget from floating windows
        plate_manager_window = main_window.floating_windows.get("plate_manager")
        if not plate_manager_window:
            return False

        layout = plate_manager_window.layout()
        if not layout or layout.count() == 0:
            return False

        plate_manager_widget = layout.itemAt(0).widget()
        if not hasattr(plate_manager_widget, 'orchestrators'):
            return False

        orchestrator = plate_manager_widget.orchestrators.get(self.current_plate)
        if orchestrator is None:
            return False

        # Check if orchestrator is in an initialized state (mirrors Textual TUI logic)
        from openhcs.constants.constants import OrchestratorState
        return orchestrator.state in [OrchestratorState.READY, OrchestratorState.COMPILED,
                                     OrchestratorState.COMPLETED, OrchestratorState.COMPILE_FAILED,
                                     OrchestratorState.EXEC_FAILED]



    def _get_current_orchestrator(self) -> Optional[PipelineOrchestrator]:
        """Get the orchestrator for the currently selected plate."""
        if not self.current_plate:
            return None
        main_window = self._find_main_window()
        if not main_window:
            return None
        plate_manager_window = main_window.floating_windows.get("plate_manager")
        if not plate_manager_window:
            return None
        layout = plate_manager_window.layout()
        if not layout or layout.count() == 0:
            return None
        plate_manager_widget = layout.itemAt(0).widget()
        if not hasattr(plate_manager_widget, 'orchestrators'):
            return None
        return plate_manager_widget.orchestrators.get(self.current_plate)


    # _find_main_window() moved to AbstractManagerWidget

    def on_config_changed(self, new_config: GlobalPipelineConfig):
        """
        Handle global configuration changes.

        Args:
            new_config: New global configuration
        """
        self.global_config = new_config

        # CRITICAL FIX: Refresh all placeholders when global config changes
        # This ensures pipeline config editor shows updated inherited values
        if hasattr(self, 'form_manager') and self.form_manager:
            self.form_manager.refresh_placeholder_text()
            logger.info("Refreshed pipeline config placeholders after global config change")

    # ========== Abstract Hook Implementations (AbstractManagerWidget ABC) ==========

    # === CRUD Hooks ===

    def action_add(self) -> None:
        """Add steps via dialog (required abstract method)."""
        self.action_add_step()  # Delegate to existing implementation

    def _perform_delete(self, items: List[Any]) -> None:
        """Remove steps from backing list (required abstract method)."""
        # Build set of steps to delete (by identity, not equality)
        steps_to_delete = set(id(step) for step in items)
        self.pipeline_steps = [s for s in self.pipeline_steps if id(s) not in steps_to_delete]
        self._normalize_step_scope_tokens()

        if self.selected_step in [getattr(step, 'name', '') for step in items]:
            self.selected_step = ""

    def _show_item_editor(self, item: Any) -> None:
        """Show DualEditorWindow for step (required abstract method)."""
        step_to_edit = item

        from openhcs.pyqt_gui.windows.dual_editor_window import DualEditorWindow

        def handle_save(edited_step):
            """Handle step save from editor."""
            # Find and replace the step in the pipeline
            for i, step in enumerate(self.pipeline_steps):
                if step is step_to_edit:
                    self._transfer_scope_token(step_to_edit, edited_step)
                    self.pipeline_steps[i] = edited_step
                    break

            # Update the display
            self.update_item_list()
            self.pipeline_changed.emit(self.pipeline_steps)
            self.status_message.emit(f"Updated step: {edited_step.name}")

        orchestrator = self._get_current_orchestrator()

        editor = DualEditorWindow(
            step_data=step_to_edit,
            is_new=False,
            on_save_callback=handle_save,
            orchestrator=orchestrator,
            gui_config=self.gui_config,
            parent=self
        )
        # Set original step for change detection
        editor.set_original_step_for_change_detection()

        # Connect orchestrator config changes to step editor for live placeholder updates
        if self.plate_manager and hasattr(self.plate_manager, 'orchestrator_config_changed'):
            self.plate_manager.orchestrator_config_changed.connect(editor.on_orchestrator_config_changed)
            logger.debug("Connected orchestrator_config_changed signal to step editor")

        editor.show()
        editor.raise_()
        editor.activateWindow()

    # === List Update Hooks (domain-specific) ===

    def _format_list_item(self, item: Any, index: int, context: Any) -> str:
        """Format step for list display."""
        display_text, _ = self.format_item_for_display(item, context)
        return display_text

    def _get_list_item_tooltip(self, item: Any) -> str:
        """Get step tooltip."""
        return self._create_step_tooltip(item)

    def _get_list_item_extra_data(self, item: Any, index: int) -> Dict[int, Any]:
        """Get enabled flag in UserRole+1."""
        return {1: not item.enabled}

    def _get_list_placeholder(self) -> Optional[Tuple[str, Any]]:
        """Return placeholder when no orchestrator."""
        orchestrator = self._get_current_orchestrator()
        if not orchestrator:
            return ("No plate selected - select a plate to view pipeline", None)
        return None

    def _pre_update_list(self) -> Any:
        """Normalize scope tokens and collect live context."""
        self._normalize_step_scope_tokens()
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        return ParameterFormManager.collect_live_context(scope_filter=self.current_plate)

    def _post_reorder(self) -> None:
        """Additional cleanup after reorder - normalize tokens and emit signal."""
        self._normalize_step_scope_tokens()
        self.pipeline_changed.emit(self.pipeline_steps)

    # === Config Resolution Hook (domain-specific) ===

    def _get_context_stack_for_resolution(self, item: Any) -> List[Any]:
        """Build 3-element context stack for PipelineEditor (required abstract method)."""
        from openhcs.config_framework.global_config import get_current_global_config

        orchestrator = self._get_current_orchestrator()
        if not orchestrator:
            return []

        # Return 3-element stack: [global, pipeline_config, step]
        return [
            get_current_global_config(GlobalPipelineConfig),
            orchestrator.pipeline_config,
            item  # step
        ]

    # === CrossWindowPreviewMixin Hook ===
    # _get_current_orchestrator() is implemented above (line ~795) - does actual lookup from plate manager
    # _configure_preview_fields() REMOVED - now uses declarative PREVIEW_FIELD_CONFIGS (line ~99)

    # ========== End Abstract Hook Implementations ==========

    def closeEvent(self, event):
        """Handle widget close event to disconnect signals and prevent memory leaks."""
        # Unregister from cross-window refresh signals
        from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService
        LiveContextService.disconnect_listener(self._on_live_context_changed)
        logger.debug("Pipeline editor: Unregistered from cross-window refresh signals")

        # Call parent closeEvent
        super().closeEvent(event)
