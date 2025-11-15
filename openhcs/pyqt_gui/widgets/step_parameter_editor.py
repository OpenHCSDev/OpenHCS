"""
Step Parameter Editor Widget for PyQt6 GUI.

Mirrors the Textual TUI StepParameterEditorWidget with type hint-based form generation.
Handles FunctionStep parameter editing with nested dataclass support.
"""

import logging
from typing import Any, Optional
from pathlib import Path

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QLabel,
    QScrollArea, QSplitter, QTreeWidget, QTreeWidgetItem
)
from PyQt6.QtCore import Qt, pyqtSignal

from openhcs.core.steps.function_step import FunctionStep
from openhcs.introspection.signature_analyzer import SignatureAnalyzer
from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
from openhcs.pyqt_gui.widgets.shared.config_hierarchy_tree import ConfigHierarchyTreeHelper
from openhcs.pyqt_gui.widgets.shared.collapsible_splitter_helper import CollapsibleSplitterHelper
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.config import PyQtGUIConfig, get_default_pyqt_gui_config
# REMOVED: LazyDataclassFactory import - no longer needed since step editor
# uses existing lazy dataclass instances from the step
from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
from openhcs.ui.shared.code_editor_form_updater import CodeEditorFormUpdater

logger = logging.getLogger(__name__)


class StepParameterEditorWidget(QWidget):
    """
    Step parameter editor using dynamic form generation.
    
    Mirrors Textual TUI implementation - builds forms based on FunctionStep 
    constructor signature with nested dataclass support.
    """
    
    # Signals
    step_parameter_changed = pyqtSignal()
    
    def __init__(self, step: FunctionStep, service_adapter=None, color_scheme: Optional[PyQt6ColorScheme] = None,
                 gui_config: Optional[PyQtGUIConfig] = None, parent=None, pipeline_config=None, scope_id: Optional[str] = None):
        super().__init__(parent)

        # Initialize color scheme and GUI config
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.gui_config = gui_config or get_default_pyqt_gui_config()
        self.style_generator = StyleSheetGenerator(self.color_scheme)

        self.step = step
        self.service_adapter = service_adapter
        self.pipeline_config = pipeline_config  # Store pipeline config for context hierarchy
        self.scope_id = scope_id  # Store scope_id for cross-window update scoping

        # Live placeholder updates not yet ready - disable for now
        self._step_editor_coordinator = None
        # TODO: Re-enable when live updates feature is fully implemented
        # if hasattr(self.gui_config, 'enable_live_step_parameter_updates') and self.gui_config.enable_live_step_parameter_updates:
        #     from openhcs.config_framework.lazy_factory import ContextEventCoordinator
        #     self._step_editor_coordinator = ContextEventCoordinator()
        #     logger.debug("🔍 STEP EDITOR: Created step-editor-specific coordinator for live step parameter updates")
        
        # Analyze AbstractStep signature to get all inherited parameters (mirrors Textual TUI)
        from openhcs.core.steps.abstract import AbstractStep
        # Auto-detection correctly identifies constructors and includes all parameters
        param_info = SignatureAnalyzer.analyze(AbstractStep.__init__)
        
        # Get current parameter values from step instance
        parameters = {}
        parameter_types = {}
        param_defaults = {}

        for name, info in param_info.items():
            # All AbstractStep parameters are relevant for editing
            # ParameterFormManager will automatically route lazy dataclass parameters to LazyDataclassEditor
            current_value = getattr(self.step, name, info.default_value)

            # CRITICAL FIX: For lazy dataclass parameters, leave current_value as None
            # This allows the UI to show placeholders and use lazy resolution properly
            if current_value is None and self._is_optional_lazy_dataclass_in_pipeline(info.param_type, name):
                # Don't create concrete instances - leave as None for placeholder resolution
                # The UI will handle lazy resolution and show appropriate placeholders
                param_defaults[name] = None
                # Mark this as a step-level config for special handling
                if not hasattr(self, '_step_level_configs'):
                    self._step_level_configs = {}
                self._step_level_configs[name] = True
            else:
                param_defaults[name] = info.default_value

            parameters[name] = current_value
            parameter_types[name] = info.param_type

        # Track dataclass-backed parameters for the hierarchy tree
        self._tree_dataclass_params = self._collect_dataclass_parameters(parameter_types)
        self.tree_helper = ConfigHierarchyTreeHelper()
        
        # SIMPLIFIED: Create parameter form manager using dual-axis resolution

        # CRITICAL FIX: Use pipeline_config as context_obj (parent for inheritance)
        # The step is the overlay (what's being edited), not the parent context
        # Context hierarchy: GlobalPipelineConfig (thread-local) -> PipelineConfig (context_obj) -> Step (overlay)
        # CRITICAL FIX: Exclude 'func' parameter - it's handled by the Function Pattern tab
        self.form_manager = ParameterFormManager(
            object_instance=self.step,           # Step instance being edited (overlay)
            field_id="step",                     # Use "step" as field identifier
            parent=self,                         # Pass self as parent widget
            context_obj=self.pipeline_config,    # Pipeline config as parent context for inheritance
            exclude_params=['func'],             # Exclude func - it has its own dedicated tab
            scope_id=self.scope_id               # Pass scope_id to limit cross-window updates to same orchestrator
        )
        self.hierarchy_tree = None
        self.content_splitter = None

        self.setup_ui()
        self.setup_connections()

        logger.debug(f"Step parameter editor initialized for step: {getattr(step, 'name', 'Unknown')}")

    def _is_optional_lazy_dataclass_in_pipeline(self, param_type, param_name):
        """
        Check if parameter is an optional lazy dataclass that exists in PipelineConfig.

        This enables automatic step-level config creation for any parameter that:
        1. Is Optional[SomeDataclass]
        2. SomeDataclass exists as a field type in PipelineConfig (type-based matching)
        3. The dataclass has lazy resolution capabilities

        No manual mappings needed - uses type-based discovery.
        """

        # Check if parameter is Optional[dataclass]
        if not ParameterTypeUtils.is_optional_dataclass(param_type):
            return False

        # Get the inner dataclass type
        inner_type = ParameterTypeUtils.get_optional_inner_type(param_type)

        # Find if this type exists as a field in PipelineConfig (type-based matching)
        pipeline_field_name = self._find_pipeline_field_by_type(inner_type)
        if not pipeline_field_name:
            return False

        # Check if the dataclass has lazy resolution capabilities
        try:
            # Try to create an instance to see if it's a lazy dataclass
            test_instance = inner_type()
            # Check for lazy dataclass methods
            return hasattr(test_instance, '_resolve_field_value') or hasattr(test_instance, '_lazy_resolution_config')
        except:
            return False

    def _find_pipeline_field_by_type(self, target_type):
        """
        Find the field in PipelineConfig that matches the target type.

        This is type-based discovery - no manual mappings needed.
        """
        from openhcs.core.config import PipelineConfig
        import dataclasses

        for field in dataclasses.fields(PipelineConfig):
            # Use string comparison to handle type identity issues
            if str(field.type) == str(target_type):
                return field.name
        return None

    # REMOVED: _create_step_level_config method - dead code
    # The step editor should use the existing lazy dataclass instances from the step,
    # not create new "StepLevel" versions. The AbstractStep already has the correct
    # lazy dataclass types (LazyNapariStreamingConfig, LazyStepMaterializationConfig, etc.)

    def _collect_dataclass_parameters(self, parameter_types):
        """Return dataclass-based parameters for building the hierarchy tree."""
        dataclass_params = {}
        for field_name, param_type in parameter_types.items():
            if field_name == 'func':
                continue

            dataclass_type = self._extract_dataclass_from_param_type(param_type)
            if dataclass_type is not None:
                dataclass_params[field_name] = dataclass_type

        return dataclass_params

    def _extract_dataclass_from_param_type(self, param_type):
        """Resolve the concrete dataclass type from the annotated parameter."""
        import dataclasses
        from typing import Union, get_args, get_origin

        resolved_type = param_type

        try:
            origin = get_origin(param_type)
        except Exception:
            origin = None

        if origin is Union:
            args = [arg for arg in get_args(param_type) if arg is not type(None)]
            if len(args) == 1:
                resolved_type = args[0]

        if resolved_type is None or isinstance(resolved_type, str):
            return None

        if dataclasses.is_dataclass(resolved_type):
            return resolved_type

        return None

    def _create_configuration_tree(self) -> Optional[QTreeWidget]:
        """Create and populate the configuration hierarchy tree."""
        if not getattr(self, '_tree_dataclass_params', None):
            return None

        # Use default minimum_width=0 from shared helper (allows collapsing)
        tree = self.tree_helper.create_tree_widget()
        self.tree_helper.populate_from_mapping(tree, self._tree_dataclass_params)

        tree.itemDoubleClicked.connect(self._on_tree_item_double_clicked)
        return tree

    def _on_tree_item_double_clicked(self, item: QTreeWidgetItem, column: int):
        """Scroll to the associated form section when a tree item is activated."""
        data = item.data(0, Qt.ItemDataRole.UserRole)
        if not data or data.get('ui_hidden'):
            return

        item_type = data.get('type')
        if item_type == 'dataclass':
            field_name = data.get('field_name')
            if field_name:
                self._scroll_to_section(field_name)
        elif item_type == 'inheritance_link':
            target_class = data.get('target_class')
            if target_class:
                field_name = self._find_field_for_class(target_class)
                if field_name:
                    self._scroll_to_section(field_name)

    def _find_field_for_class(self, target_class) -> Optional[str]:
        """Locate the parameter field that edits the given dataclass."""
        for field_name, dataclass_type in self._tree_dataclass_params.items():
            base_type = self.tree_helper.get_base_type(dataclass_type)
            if target_class in (dataclass_type, base_type):
                return field_name
        return None

    def _scroll_to_section(self, field_name: str):
        """Ensure the requested parameter section is visible."""
        if not hasattr(self, 'scroll_area') or self.scroll_area is None:
            logger.warning("Scroll area not initialized; cannot navigate to section")
            return

        nested_managers = getattr(self.form_manager, 'nested_managers', {})
        nested_manager = nested_managers.get(field_name)
        if not nested_manager:
            logger.warning(f"Field '{field_name}' not found in nested managers")
            return

        first_widget = None
        if hasattr(nested_manager, 'widgets') and nested_manager.widgets:
            first_param_name = next(iter(nested_manager.widgets.keys()))
            first_widget = nested_manager.widgets[first_param_name]

        if first_widget:
            self.scroll_area.ensureWidgetVisible(first_widget, 100, 100)
            return

        from PyQt6.QtWidgets import QGroupBox
        current = nested_manager.parentWidget()
        while current:
            if isinstance(current, QGroupBox):
                self.scroll_area.ensureWidgetVisible(current, 50, 50)
                return
            current = current.parentWidget()

        logger.warning(f"Could not locate widget for '{field_name}' to scroll into view")





    def setup_ui(self):
        """Setup the user interface (matches FunctionListEditorWidget structure)."""
        # Main layout directly on self (like FunctionListEditorWidget)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(8)

        # Header with controls (like FunctionListEditorWidget)
        header_layout = QHBoxLayout()

        # Header label
        header_label = QLabel("Step Parameters")
        header_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)}; font-weight: bold; font-size: 14px;")
        header_layout.addWidget(header_label)

        header_layout.addStretch()

        # Action buttons in header (preserving functionality)
        code_btn = QPushButton("Code")
        code_btn.setMaximumWidth(60)
        code_btn.setStyleSheet(self._get_button_style())
        code_btn.clicked.connect(self.view_step_code)
        header_layout.addWidget(code_btn)

        load_btn = QPushButton("Load .step")
        load_btn.setMaximumWidth(100)
        load_btn.setStyleSheet(self._get_button_style())
        load_btn.clicked.connect(self.load_step_settings)
        header_layout.addWidget(load_btn)

        save_btn = QPushButton("Save .step As")
        save_btn.setMaximumWidth(120)
        save_btn.setStyleSheet(self._get_button_style())
        save_btn.clicked.connect(self.save_step_settings)
        header_layout.addWidget(save_btn)

        layout.addLayout(header_layout)

        # Scrollable parameter form (matches config window pattern)
        self.scroll_area = QScrollArea()
        self.scroll_area.setWidgetResizable(True)
        self.scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        # No explicit styling - let it inherit from parent

        # Add form manager directly to scroll area (like config window)
        self.scroll_area.setWidget(self.form_manager)
        hierarchy_tree = self._create_configuration_tree()
        if hierarchy_tree:
            splitter = QSplitter(Qt.Orientation.Horizontal)
            splitter.setChildrenCollapsible(True)  # CRITICAL: Allow tree to collapse
            splitter.setHandleWidth(5)  # Make handle more visible
            splitter.addWidget(hierarchy_tree)
            splitter.addWidget(self.scroll_area)
            splitter.setSizes([280, 720])
            layout.addWidget(splitter, 1)
            self.hierarchy_tree = hierarchy_tree
            self.content_splitter = splitter

            # Install collapsible splitter helper for double-click toggle
            self.splitter_helper = CollapsibleSplitterHelper(splitter, left_panel_index=0)
            self.splitter_helper.set_initial_size(280)
        else:
            layout.addWidget(self.scroll_area)
            self.hierarchy_tree = None
            self.content_splitter = None

        # Apply tree widget styling (matches config window)
        self.setStyleSheet(self.style_generator.generate_tree_widget_style())
    
    def _get_button_style(self) -> str:
        """Get consistent button styling."""
        return """
            QPushButton {
                background-color: {self.color_scheme.to_hex(self.color_scheme.input_bg)};
                color: white;
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_light)};
                border-radius: 3px;
                padding: 6px 12px;
                font-size: 11px;
            }
            QPushButton:hover {
                background-color: {self.color_scheme.to_hex(self.color_scheme.button_hover_bg)};
            }
            QPushButton:pressed {
                background-color: {self.color_scheme.to_hex(self.color_scheme.button_pressed_bg)};
            }
        """
    
    def setup_connections(self):
        """Setup signal/slot connections."""
        # Connect form manager parameter changes
        self.form_manager.parameter_changed.connect(self._handle_parameter_change)
    
    def _handle_parameter_change(self, param_name: str, value: Any):
        """Handle parameter change from form manager (mirrors Textual TUI)."""
        try:
            # Get the properly converted value from the form manager
            # The form manager handles all type conversions including List[Enum]
            final_value = self.form_manager.get_current_values().get(param_name, value)

            # Debug: Check what we're actually saving
            if param_name == 'materialization_config':
                print(f"DEBUG: Saving materialization_config, type: {type(final_value)}")
                print(f"DEBUG: Raw value from form manager: {value}")
                print(f"DEBUG: Final value from get_current_values(): {final_value}")
                if hasattr(final_value, '__dataclass_fields__'):
                    from dataclasses import fields
                    for field_obj in fields(final_value):
                        raw_value = object.__getattribute__(final_value, field_obj.name)
                        print(f"DEBUG: Field {field_obj.name} = {raw_value}")

            # CRITICAL FIX: For function parameters, use fresh imports to avoid unpicklable registry wrappers
            if param_name == 'func' and callable(final_value) and hasattr(final_value, '__module__'):
                try:
                    import importlib
                    module = importlib.import_module(final_value.__module__)
                    final_value = getattr(module, final_value.__name__)
                except Exception:
                    pass  # Use original if refresh fails

            # Update step attribute
            setattr(self.step, param_name, final_value)
            logger.debug(f"Updated step parameter {param_name}={final_value}")
            self.step_parameter_changed.emit()

        except Exception as e:
            logger.error(f"Error updating step parameter {param_name}: {e}")

    def load_step_settings(self):
        """Load step settings from .step file (mirrors Textual TUI)."""
        if not self.service_adapter:
            logger.warning("No service adapter available for file dialog")
            return
        
        from openhcs.core.path_cache import PathCacheKey
        
        file_path = self.service_adapter.show_cached_file_dialog(
            cache_key=PathCacheKey.STEP_SETTINGS,
            title="Load Step Settings (.step)",
            file_filter="Step Files (*.step);;All Files (*)",
            mode="open"
        )
        
        if file_path:
            self._load_step_settings_from_file(file_path)
    
    def save_step_settings(self):
        """Save step settings to .step file (mirrors Textual TUI)."""
        if not self.service_adapter:
            logger.warning("No service adapter available for file dialog")
            return
        
        from openhcs.core.path_cache import PathCacheKey
        
        file_path = self.service_adapter.show_cached_file_dialog(
            cache_key=PathCacheKey.STEP_SETTINGS,
            title="Save Step Settings (.step)",
            file_filter="Step Files (*.step);;All Files (*)",
            mode="save"
        )
        
        if file_path:
            self._save_step_settings_to_file(file_path)
    
    def _load_step_settings_from_file(self, file_path: Path):
        """Load step settings from file."""
        try:
            import dill as pickle
            with open(file_path, 'rb') as f:
                step_data = pickle.load(f)

            # Update form manager with loaded values
            for param_name, value in step_data.items():
                if hasattr(self.form_manager, 'update_parameter'):
                    self.form_manager.update_parameter(param_name, value)
                    # Also update the step object
                    if hasattr(self.step, param_name):
                        setattr(self.step, param_name, value)

            # Refresh the form to show loaded values
            self.form_manager._refresh_all_placeholders()
            logger.debug(f"Loaded {len(step_data)} parameters from {file_path.name}")

        except Exception as e:
            logger.error(f"Failed to load step settings from {file_path}: {e}")
            if self.service_adapter:
                self.service_adapter.show_error_dialog(f"Failed to load step settings: {e}")

    def _save_step_settings_to_file(self, file_path: Path):
        """Save step settings to file."""
        try:
            import dill as pickle
            # Get current values from form manager
            step_data = self.form_manager.get_current_values()
            with open(file_path, 'wb') as f:
                pickle.dump(step_data, f)
            logger.debug(f"Saved {len(step_data)} parameters to {file_path.name}")

        except Exception as e:
            logger.error(f"Failed to save step settings to {file_path}: {e}")
            if self.service_adapter:
                self.service_adapter.show_error_dialog(f"Failed to save step settings: {e}")

    
    def get_current_step(self) -> FunctionStep:
        """Get the current step with all parameter values."""
        return self.step
    
    def update_step(self, step: FunctionStep):
        """Update the step and refresh the form."""
        self.step = step
        
        # Update form manager with new values
        for param_name in self.form_manager.parameters.keys():
            current_value = getattr(self.step, param_name, None)
            self.form_manager.update_parameter(param_name, current_value)

        logger.debug(f"Updated step parameter editor for step: {getattr(step, 'name', 'Unknown')}")

    def view_step_code(self):
        """View the complete FunctionStep as Python code."""
        try:
            from openhcs.pyqt_gui.services.simple_code_editor import SimpleCodeEditorService
            from openhcs.debug.pickle_to_python import generate_step_code
            import os

            # CRITICAL: Refresh with live context BEFORE getting current values
            self.form_manager._refresh_with_live_context()

            # Get current step from form (includes live context values)
            current_values = self.form_manager.get_current_values()

            # CRITICAL: Get func from parent dual editor's function list editor if available
            # The func is managed by the Function Pattern tab in the dual editor
            func = self.step.func  # Default to step's current func

            # Check if we're inside a dual editor window with a function list editor
            parent_window = self.window()
            if hasattr(parent_window, 'func_editor') and parent_window.func_editor:
                # Get live func pattern from function list editor
                func = parent_window.func_editor.current_pattern
                logger.debug(f"Using live func from function list editor: {func}")
            else:
                logger.debug(f"Using func from step instance: {func}")

            current_values['func'] = func

            from openhcs.core.steps.function_step import FunctionStep
            current_step = FunctionStep(**current_values)

            # Generate code using existing pattern
            python_code = generate_step_code(current_step, clean_mode=False)

            # Launch editor
            editor_service = SimpleCodeEditorService(self)
            use_external = os.environ.get('OPENHCS_USE_EXTERNAL_EDITOR', '').lower() in ('1', 'true', 'yes')

            editor_service.edit_code(
                initial_content=python_code,
                title=f"Edit Step: {current_step.name}",
                callback=self._handle_edited_step_code,
                use_external=use_external,
                code_type='step'
            )

        except Exception as e:
            logger.error(f"Failed to open step code editor: {e}")
            if self.service_adapter:
                self.service_adapter.show_error_dialog(f"Failed to open code editor: {str(e)}")

    def _handle_edited_step_code(self, edited_code: str) -> None:
        """Handle the edited step code from code editor."""
        try:
            # SIMPLIFIED: Just exec with patched constructors
            # The patched constructors preserve None vs concrete distinction in raw field values
            # No need to parse code - just inspect raw values after exec
            namespace = {}
            with CodeEditorFormUpdater.patch_lazy_constructors():
                exec(edited_code, namespace)

            new_step = namespace.get('step')
            if not new_step:
                raise ValueError("No 'step' variable found in edited code")

            # Update step object
            self.step = new_step

            # OPTIMIZATION: Block cross-window updates during bulk update
            self.form_manager._block_cross_window_updates = True
            try:
                CodeEditorFormUpdater.update_form_from_instance(
                    self.form_manager,
                    new_step,
                    broadcast_callback=None
                )
            finally:
                self.form_manager._block_cross_window_updates = False

            # CRITICAL: Update function list editor if we're inside a dual editor window
            parent_window = self.window()
            if hasattr(parent_window, 'func_editor') and parent_window.func_editor:
                func_editor = parent_window.func_editor
                func_editor._initialize_pattern_data(new_step.func)
                func_editor._populate_function_list()
                logger.debug(f"Updated function list editor with new func: {new_step.func}")

            # CodeEditorFormUpdater already refreshes placeholders and emits context events

            # Emit step parameter changed signal for parent window
            self.step_parameter_changed.emit()

            logger.info(f"Updated step from code editor: {new_step.name}")

        except Exception as e:
            logger.error(f"Failed to apply edited step code: {e}")
            raise
