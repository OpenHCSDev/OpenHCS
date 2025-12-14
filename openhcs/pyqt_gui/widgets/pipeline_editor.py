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
from openhcs.pyqt_gui.widgets.shared.scope_visual_config import ListItemType
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.config import PyQtGUIConfig, get_default_pyqt_gui_config
from openhcs.config_framework.object_state import ObjectState, ObjectStateRegistry
from openhcs.pyqt_gui.widgets.shared.services.scope_token_service import ScopeTokenService

# Import shared list widget components (single source of truth)
from openhcs.pyqt_gui.widgets.shared.reorderable_list_widget import ReorderableListWidget
from openhcs.pyqt_gui.widgets.shared.list_item_delegate import MultilinePreviewItemDelegate, StyledText
from openhcs.config_framework.lazy_factory import PREVIEW_LABEL_REGISTRY
from openhcs.core.config import ProcessingConfig

# Import ABC base class (Phase 4 migration)
from openhcs.pyqt_gui.widgets.shared.abstract_manager_widget import AbstractManagerWidget, ListItemFormat

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
        'id_accessor': ('attr', 'name'),          # getattr(item, 'name', '')
        'backing_attr': 'pipeline_steps',         # self.pipeline_steps
        'selection_attr': 'selected_step',        # self.selected_step = ...
        'selection_signal': 'step_selected',      # self.step_selected.emit(...)
        'selection_emit_id': False,               # emit the full step object
        'selection_clear_value': None,            # emit None when cleared
        'items_changed_signal': 'pipeline_changed',  # self.pipeline_changed.emit(...)
        'preserve_selection_pred': lambda self: bool(self.pipeline_steps),
        'list_item_data': 'item',                 # store the step object
        'scope_item_type': ListItemType.STEP,
        'scope_id_builder': lambda item, idx, w: w._build_step_scope_id(item),
    }

    # Declarative preview field configuration (processed automatically in ABC.__init__)
    # Labels auto-discovered from PREVIEW_LABEL_REGISTRY (set via @global_pipeline_config(preview_label=...))
    PREVIEW_FIELD_CONFIGS = [
        'napari_streaming_config',       # preview_label='NAP'
        'fiji_streaming_config',         # preview_label='FIJI'
        'step_materialization_config',   # preview_label='MAT'
    ]

    # Declarative list item format (replaces imperative format_item_for_display logic)
    LIST_ITEM_FORMAT = ListItemFormat(
        first_line=('func',),  # func= shown after step name
        preview_line=(
            'processing_config.variable_components',
            'processing_config.group_by',
            'processing_config.input_source',
        ),
        show_config_indicators=True,
        formatters={
            'func': '_format_func_preview',  # Method name for complex formatting
            'processing_config.input_source': '_format_input_source_preview',
        },
    )

    # === Declarative Field Formatters ===
    def _format_func_preview(self, func, state=None) -> Optional[str]:
        """Format func field for preview.

        Shows function names for the pattern:
        - Single callable: func=my_func
        - Tuple (func, kwargs): func=my_func
        - List chain: func=[func1, func2, func3]
        - Dict pattern: func={DAPI: func1, GFP: func2} (uses metadata for key names)

        Args:
            func: The func value to format
            state: Optional ObjectState to get group_by for dict key metadata lookup
        """
        if isinstance(func, tuple) and len(func) >= 1:
            # (func, kwargs) pattern - extract function name
            func_name = self._get_func_name(func)
            return f"func={func_name}"
        elif isinstance(func, list) and func:
            # Show actual function names
            func_names = [self._get_func_name(f) for f in func if f is not None]
            return f"func=[{', '.join(func_names)}]"
        elif callable(func):
            func_name = getattr(func, '__name__', str(func))
            return f"func={func_name}"
        elif isinstance(func, dict):
            # Use orchestrator's metadata cache for key→name mapping if available
            orchestrator = self._get_current_orchestrator()
            metadata_cache = orchestrator.metadata_cache if orchestrator else None

            # Get group_by from ObjectState to determine component type for metadata lookup
            group_by = None
            if state:
                group_by = state.get_resolved_value('processing_config.group_by')

            # Build {display_name: func_name} entries
            entries = []
            for key in sorted(func.keys()):
                # Try to get display name from metadata cache using step's group_by
                display_name = None
                if group_by and metadata_cache:
                    display_name = metadata_cache.get_component_metadata(group_by, str(key))
                if display_name is None:
                    display_name = str(key)
                func_name = self._get_func_name(func[key])
                entries.append(f"{display_name}: {func_name}")
            return f"func={{{', '.join(entries)}}}"
        return None

    def _get_func_name(self, func_entry) -> str:
        """Extract function name from various func entry formats."""
        if isinstance(func_entry, tuple) and len(func_entry) >= 1:
            # (func, kwargs) pattern
            return getattr(func_entry[0], '__name__', str(func_entry[0]))
        elif isinstance(func_entry, list) and func_entry:
            # Chain pattern - show first→last
            first = self._get_func_name(func_entry[0])
            if len(func_entry) > 1:
                last = self._get_func_name(func_entry[-1])
                return f"{first}→{last}"
            return first
        elif callable(func_entry):
            return getattr(func_entry, '__name__', str(func_entry))
        return str(func_entry)

    def _format_input_source_preview(self, input_source) -> Optional[str]:
        """Format input_source field (only show if not default)."""
        source_name = getattr(input_source, 'name', str(input_source))
        if source_name != 'PREVIOUS_STEP':
            return f"input={source_name}"
        return None  # Skip default value



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

        Uses ObjectState for resolved values (no context stack rebuild).
        Returns StyledText with segments for per-field dirty/sig-diff styling.

        Args:
            step: FunctionStep to format
            live_context_snapshot: IGNORED - kept for API compatibility

        Returns:
            Tuple of (StyledText with segments, step_name)
        """
        step_name: str = getattr(step, 'name', 'Unknown Step') or 'Unknown Step'

        # Use declarative format from LIST_ITEM_FORMAT
        styled = self._build_item_display_from_format(
            item=step,
            item_name=step_name,
        )
        return styled, step_name

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

        # Use registry to discover preview configs - iterate step's fields
        from dataclasses import fields, is_dataclass
        if is_dataclass(step):
            for f in fields(step):
                config = object.__getattribute__(step, f.name)
                if config is None:
                    continue
                config_type = type(config)
                # Check if type is in registry (or any base)
                in_registry = config_type in PREVIEW_LABEL_REGISTRY or any(
                    b in PREVIEW_LABEL_REGISTRY for b in config_type.__mro__[1:]
                )
                if not in_registry:
                    continue
                # Check enabled field if exists
                if is_dataclass(config) and 'enabled' in {ff.name for ff in fields(config)}:
                    if not config.enabled:
                        continue
                config_details.append(format_config_detail(f.name, config))

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
        plate_scope = self.current_plate or "no_plate"
        ScopeTokenService.ensure_token(plate_scope, new_step)

        # CRITICAL: Register ObjectState BEFORE opening editor
        # StepParameterEditor expects ObjectState to exist in registry
        self._register_step_state(new_step)

        def handle_save(edited_step):
            """Handle step save from editor."""
            # Check if step already exists in pipeline (for Shift+Click saves)
            if edited_step not in self.pipeline_steps:
                self.pipeline_steps.append(edited_step)
                ScopeTokenService.ensure_token(plate_scope, edited_step)
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

            # Use ABC template for unified code execution (handles registration sync)
            self._handle_edited_code(python_code)
            self.status_message.emit(f"Auto-loaded {len(self.pipeline_steps)} steps from basic_pipeline.py")

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

        # Save pipeline to plate_pipelines dict for current plate
        # This ensures set_current_plate() can reload it later
        if self.current_plate:
            self.plate_pipelines[self.current_plate] = self.pipeline_steps
            logger.debug(f"Saved pipeline ({len(self.pipeline_steps)} steps) for plate: {self.current_plate}")

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

                # Save pipeline to plate_pipelines dict for current plate
                # This ensures set_current_plate() can reload it later
                if self.current_plate:
                    self.plate_pipelines[self.current_plate] = self.pipeline_steps
                    logger.debug(f"Saved pipeline ({len(self.pipeline_steps)} steps) for plate: {self.current_plate}")

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

        # DON'T unregister ObjectStates when switching plates - they should stay
        # registered until the step editor is closed. Switching plates just changes
        # the view, it doesn't delete the step editors.

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

        # CRITICAL: Force cleanup of flash subscriptions when switching plates
        # This ensures FlashElements don't point to stale QListWidgetItems
        # from the previous plate's list widget
        self._cleanup_flash_subscriptions()

        self.update_item_list()

        # CRITICAL: Invalidate flash overlay cache after rebuilding list
        # This forces geometry recalculation for the new list items
        from openhcs.pyqt_gui.widgets.shared.flash_mixin import WindowFlashOverlay
        WindowFlashOverlay.invalidate_cache_for_widget(self)

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

    # _resolve_config_attr() DELETED - use base class version (uses ObjectState)

    def _build_step_scope_id(self, step: FunctionStep) -> str:
        """Return the hierarchical scope id for a step: plate::step_N."""
        plate_scope = self.current_plate or "no_plate"
        return ScopeTokenService.build_scope_id(plate_scope, step)

    # ========== Time-Travel Hooks (ABC overrides) ==========

    def _get_item_insert_index(self, item: Any, scope_key: str) -> Optional[int]:
        """Get correct position for step re-insertion during time-travel."""
        # Token format is e.g. "functionstep_3" - parse index from it
        token = getattr(item, '_scope_token', None)
        if token:
            parts = token.rsplit('_', 1)
            if len(parts) == 2 and parts[1].isdigit():
                return min(int(parts[1]), len(self.pipeline_steps))
        return None

    def _normalize_step_scope_tokens(self) -> None:
        """Ensure all steps have tokens and are registered."""
        plate_scope = self.current_plate or "no_plate"
        ScopeTokenService.seed_from_objects(plate_scope, self.pipeline_steps)
        for step in self.pipeline_steps:
            self._register_step_state(step)

    def _register_step_state(self, step: FunctionStep) -> None:
        """Register ObjectState for a step (creates if not exists)."""
        scope_id = self._build_step_scope_id(step)

        # Check if already registered
        existing = ObjectStateRegistry.get_by_scope(scope_id)
        if existing:
            return

        # Get context (PipelineConfig from orchestrator)
        orchestrator = self._get_current_orchestrator()
        context_obj = orchestrator.pipeline_config if orchestrator else None

        state = ObjectState(
            object_instance=step,
            scope_id=scope_id,
            parent_state=ObjectStateRegistry.get_by_scope(str(self.current_plate)) if self.current_plate else None,
            # func is hidden from ParameterFormManager via _ui_special_fields but included in ObjectState
        )
        ObjectStateRegistry.register(state)
        logger.debug(f"Registered ObjectState for step: {scope_id}")

    def _unregister_step_state(self, step: FunctionStep) -> None:
        """Unregister ObjectState for a step and all its nested functions."""
        scope_id = self._build_step_scope_id(step)

        # Cascade unregister: step + all nested functions (prevents memory leak)
        count = ObjectStateRegistry.unregister_scope_and_descendants(scope_id)
        logger.debug(f"Cascade unregistered {count} ObjectState(s) for deleted step: {scope_id}")

    # _merge_with_live_values() DELETED - use _merge_with_live_values() from base class
    # _get_step_preview_instance() DELETED - ObjectState provides resolved values directly

    def _handle_full_preview_refresh(self) -> None:
        """Refresh all step preview labels."""
        self.update_item_list()

    def _refresh_step_items_by_index(self, indices: Iterable[int], live_context_snapshot=None) -> None:
        """Refresh specific step items by index. Uses ObjectState for values."""
        if not indices or not self.current_plate:
            return

        for step_index in sorted(set(indices)):
            if step_index < 0 or step_index >= len(self.pipeline_steps):
                continue
            item = self.item_list.item(step_index)
            if item is None:
                continue
            step = self.pipeline_steps[step_index]
            display_text, _ = self.format_item_for_display(step)
            if item.text() != display_text:
                item.setText(display_text)
            item.setData(Qt.ItemDataRole.UserRole, step_index)
            item.setData(Qt.ItemDataRole.UserRole + 1, not step.enabled)
            item.setToolTip(self._create_step_tooltip(step))
            self._set_item_styling_roles(item, display_text, step)  # ABC helper

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
        # Unregister ObjectStates for deleted steps
        for step in items:
            self._unregister_step_state(step)

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

        plate_scope = self.current_plate or "no_plate"

        # Find step's current position in pipeline for border pattern
        step_index = None
        for i, step in enumerate(self.pipeline_steps):
            if step is step_to_edit:
                step_index = i
                break

        def handle_save(edited_step):
            """Handle step save from editor."""
            # Find and replace the step in the pipeline
            for i, step in enumerate(self.pipeline_steps):
                if step is step_to_edit:
                    # Transfer scope token from old to new step
                    prefix = ScopeTokenService._get_prefix(step_to_edit)
                    ScopeTokenService.get_generator(plate_scope, prefix).transfer(step_to_edit, edited_step)
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
            parent=self,
            step_index=step_index  # Pass actual position for border pattern
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

    def _format_item_content(self, item: Any, index: int, context: Any) -> str:
        """Format step for list display (dirty marker added by ABC)."""
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
        """Normalize scope tokens before list update.

        ObjectState provides resolved values directly - no need to collect
        LiveContextSnapshot. Just ensure scope tokens are normalized.
        """
        self._normalize_step_scope_tokens()
        return None  # ObjectState provides values, no context needed

    def _post_reorder(self) -> None:
        """Additional cleanup after reorder - normalize tokens and emit signal."""
        self._normalize_step_scope_tokens()
        self.pipeline_changed.emit(self.pipeline_steps)
        # Broadcast to global event bus so open step editors update their colors
        self._broadcast_to_event_bus('pipeline', self.pipeline_steps)

    # === Config Resolution Hook (domain-specific) ===

    def _get_scope_for_item(self, item: Any) -> str:
        """PipelineEditor: scope = plate::step_token."""
        scope = self._build_step_scope_id(item) or ''
        logger.debug(f"⚡ FLASH_DEBUG _get_scope_for_item: item={item}, scope={scope}")
        return scope

    # === CrossWindowPreviewMixin Hook ===
    # _get_current_orchestrator() is implemented above (line ~795) - does actual lookup from plate manager
    # _configure_preview_fields() REMOVED - now uses declarative PREVIEW_FIELD_CONFIGS (line ~99)

    # ========== End Abstract Hook Implementations ==========

    def closeEvent(self, event):
        """Handle widget close event to disconnect signals and prevent memory leaks."""
        # Unregister from cross-window refresh signals
        ObjectStateRegistry.disconnect_listener(self._on_live_context_changed)
        logger.debug("Pipeline editor: Unregistered from cross-window refresh signals")

        # Call parent closeEvent
        super().closeEvent(event)
