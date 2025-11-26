"""
Pipeline Editor Widget for PyQt6

Pipeline step management with full feature parity to Textual TUI version.
Uses hybrid approach: extracted business logic + clean PyQt6 UI.
"""

import logging
import inspect
import copy
from typing import List, Dict, Optional, Callable, Tuple, Any, Iterable, Set
from dataclasses import is_dataclass
import dataclasses
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
from openhcs.pyqt_gui.widgets.mixins import (
    preserve_selection_during_update,
    handle_selection_change_with_prevention,
    CrossWindowPreviewMixin,
)
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.config import PyQtGUIConfig, get_default_pyqt_gui_config
from openhcs.config_framework import LiveContextResolver

# Import shared list widget components (single source of truth)
from openhcs.pyqt_gui.widgets.shared.reorderable_list_widget import ReorderableListWidget
from openhcs.pyqt_gui.widgets.shared.list_item_delegate import MultilinePreviewItemDelegate
from openhcs.pyqt_gui.widgets.config_preview_formatters import CONFIG_INDICATORS
from openhcs.core.config import ProcessingConfig

from openhcs.utils.performance_monitor import timer

logger = logging.getLogger(__name__)


class PipelineEditorWidget(QWidget, CrossWindowPreviewMixin):
    """
    PyQt6 Pipeline Editor Widget.

    Manages pipeline steps with add, edit, delete, load, save functionality.
    Preserves all business logic from Textual version with clean PyQt6 UI.
    """

    # Config attribute name to display abbreviation mapping
    # Maps step config attribute names to their preview text indicators
    # MOVED TO: openhcs/pyqt_gui/widgets/config_preview_formatters.py (single source of truth)
    # Imported at runtime to avoid class-level import issues
    STEP_CONFIG_INDICATORS = None  # Populated in __init__ from CONFIG_INDICATORS

    STEP_SCOPE_ATTR = "_pipeline_scope_token"
    # Signals
    pipeline_changed = pyqtSignal(list)  # List[FunctionStep]
    step_selected = pyqtSignal(object)  # FunctionStep
    status_message = pyqtSignal(str)  # status message
    
    def __init__(self, file_manager: FileManager, service_adapter,
                 color_scheme: Optional[PyQt6ColorScheme] = None, gui_config: Optional[PyQtGUIConfig] = None, parent=None):
        """
        Initialize the pipeline editor widget.

        Args:
            file_manager: FileManager instance for file operations
            service_adapter: PyQt service adapter for dialogs and operations
            color_scheme: Color scheme for styling (optional, uses service adapter if None)
            gui_config: GUI configuration (optional, uses default if None)
            parent: Parent widget
        """
        super().__init__(parent)

        # Core dependencies
        self.file_manager = file_manager
        self.service_adapter = service_adapter
        self.global_config = service_adapter.get_global_config()
        self.gui_config = gui_config or get_default_pyqt_gui_config()

        # Initialize color scheme and style generator
        self.color_scheme = color_scheme or service_adapter.get_current_color_scheme()
        self.style_generator = StyleSheetGenerator(self.color_scheme)

        # Get event bus for cross-window communication
        self.event_bus = service_adapter.get_event_bus() if service_adapter else None
        
        # Business logic state (extracted from Textual version)
        self.pipeline_steps: List[FunctionStep] = []
        self.current_plate: str = ""
        self.selected_step: str = ""
        self.plate_pipelines: Dict[str, List[FunctionStep]] = {}  # Per-plate pipeline storage
        
        # UI components
        self.step_list: Optional[QListWidget] = None
        self.buttons: Dict[str, QPushButton] = {}
        self.status_label: Optional[QLabel] = None
        
        # Reference to plate manager (set externally)
        self.plate_manager = None

        # Live context resolver for config attribute resolution
        self._live_context_resolver = LiveContextResolver()
        self._preview_step_cache: Dict[int, FunctionStep] = {}
        self._preview_step_cache_token: Optional[int] = None
        self._next_scope_token = 0
        # Cache for attribute resolutions per token to avoid repeat resolver calls within a refresh
        self._attr_resolution_cache: Dict[Tuple[Optional[int], int, str], Any] = {}
        self._attr_resolution_cache_token: Optional[int] = None

        self._init_cross_window_preview_mixin()
        self._register_preview_scopes()
        self._configure_step_preview_fields()

        # Import centralized config indicators (single source of truth)
        from openhcs.pyqt_gui.widgets.config_preview_formatters import CONFIG_INDICATORS
        self.STEP_CONFIG_INDICATORS = CONFIG_INDICATORS

        # Setup UI
        self.setup_ui()
        self.setup_connections()
        self.update_button_states()



    # ========== UI Setup ==========

    def setup_ui(self):
        """Setup the user interface."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(2, 2, 2, 2)
        layout.setSpacing(2)

        # Header with title and status
        header_widget = QWidget()
        header_layout = QHBoxLayout(header_widget)
        header_layout.setContentsMargins(5, 5, 5, 5)

        title_label = QLabel("Pipeline Editor")
        title_label.setFont(QFont("Arial", 12, QFont.Weight.Bold))
        title_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};")
        header_layout.addWidget(title_label)

        header_layout.addStretch()

        # Status label in header
        self.status_label = QLabel("Ready")
        self.status_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.status_success)}; font-weight: bold;")
        header_layout.addWidget(self.status_label)

        layout.addWidget(header_widget)
        
        # Main content splitter
        splitter = QSplitter(Qt.Orientation.Vertical)
        layout.addWidget(splitter)
        
        # Pipeline steps list
        self.step_list = ReorderableListWidget()
        self.step_list.setSelectionMode(QListWidget.SelectionMode.ExtendedSelection)
        self.step_list.setStyleSheet(f"""
            QListWidget {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.panel_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
                border: none;
                padding: 5px;
            }}
            QListWidget::item {{
                padding: 8px;
                border: none;
                border-radius: 3px;
                margin: 2px;
                background: transparent;  /* Let delegate draw background */
            }}
            QListWidget::item:selected {{
                /* Don't override background - let scope colors show through */
                /* Just add a subtle border to indicate selection */
                background: transparent;  /* Critical: don't override delegate background */
                border-left: 3px solid {self.color_scheme.to_hex(self.color_scheme.selection_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
            }}
            QListWidget::item:hover {{
                /* Subtle hover effect that doesn't completely override background */
                background: transparent;  /* Critical: don't override delegate background */
            }}
        """)
        # Set custom delegate to render white name and grey preview (shared with PlateManager)
        try:
            name_color = QColor(self.color_scheme.to_hex(self.color_scheme.text_primary))
            preview_color = QColor(self.color_scheme.to_hex(self.color_scheme.text_disabled))
            selected_text_color = QColor("#FFFFFF")  # White text when selected
            self.step_list.setItemDelegate(MultilinePreviewItemDelegate(name_color, preview_color, selected_text_color, self.step_list))
        except Exception:
            # Fallback silently if color scheme isn't ready
            pass
        splitter.addWidget(self.step_list)
        
        # Button panel
        button_panel = self.create_button_panel()
        splitter.addWidget(button_panel)

        # Set splitter proportions
        splitter.setSizes([400, 120])
    
    def create_button_panel(self) -> QWidget:
        """
        Create the button panel with all pipeline actions.
        
        Returns:
            Widget containing action buttons
        """
        panel = QWidget()
        panel.setStyleSheet(f"""
            QWidget {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.window_bg)};
                border: none;
                padding: 0px;
            }}
        """)

        layout = QVBoxLayout(panel)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Button configurations (extracted from Textual version)
        button_configs = [
            ("Add", "add_step", "Add new pipeline step"),
            ("Del", "del_step", "Delete selected steps"),
            ("Edit", "edit_step", "Edit selected step"),
            ("Auto", "auto_load_pipeline", "Load basic_pipeline.py"),
            ("Code", "code_pipeline", "Edit pipeline as Python code"),
        ]

        # Create buttons in a single row
        row_layout = QHBoxLayout()
        row_layout.setContentsMargins(2, 2, 2, 2)
        row_layout.setSpacing(2)

        for name, action, tooltip in button_configs:
            button = QPushButton(name)
            button.setToolTip(tooltip)
            button.setMinimumHeight(30)
            button.setStyleSheet(self.style_generator.generate_button_style())

            # Connect button to action
            button.clicked.connect(lambda checked, a=action: self.handle_button_action(a))

            self.buttons[action] = button
            row_layout.addWidget(button)

        layout.addLayout(row_layout)

        # Set maximum height to constrain the button panel
        panel.setMaximumHeight(40)

        return panel
    

    
    def setup_connections(self):
        """Setup signal/slot connections."""
        # Step list selection
        self.step_list.itemSelectionChanged.connect(self.on_selection_changed)
        self.step_list.itemDoubleClicked.connect(self.on_item_double_clicked)

        # Step list reordering
        self.step_list.items_reordered.connect(self.on_steps_reordered)

        # Internal signals
        self.status_message.connect(self.update_status)
        self.pipeline_changed.connect(self.on_pipeline_changed)

        # Note: ParameterFormManager registration is handled by CrossWindowPreviewMixin._init_cross_window_preview_mixin()

    def _register_preview_scopes(self) -> None:
        """Configure scope resolvers for cross-window preview updates."""
        from openhcs.core.steps.function_step import FunctionStep
        from openhcs.core.config import PipelineConfig, GlobalPipelineConfig

        def step_scope_resolver(step, ctx):
            scope_id = self._build_step_scope_id(step)
            return scope_id or self.ALL_ITEMS_SCOPE

        self.register_preview_scope(
            root_name='step',
            editing_types=(FunctionStep,),
            scope_resolver=step_scope_resolver,
            aliases=('FunctionStep', 'step'),
        )

        self.register_preview_scope(
            root_name='pipeline_config',
            editing_types=(PipelineConfig,),
            scope_resolver=lambda obj, ctx: self.ALL_ITEMS_SCOPE,
            aliases=('PipelineConfig',),
            process_all_fields=True,
        )

        self.register_preview_scope(
            root_name='global_config',
            editing_types=(GlobalPipelineConfig,),
            scope_resolver=lambda obj, ctx: self.ALL_ITEMS_SCOPE,
            aliases=('GlobalPipelineConfig',),
            process_all_fields=True,
        )

    def _configure_step_preview_fields(self) -> None:
        """Register step preview fields using reusable mixin helper."""
        base_fields = ['func']
        nested_configs = [('processing_config', ProcessingConfig)]
        config_attrs = set(CONFIG_INDICATORS.keys()) | {'step_well_filter_config'}

        self.enable_preview_fields_from_introspection(
            base_fields=base_fields,
            nested_configs=nested_configs,
            config_attrs=config_attrs,
            sample_object_factory=self._get_preview_sample_step,
            scope_root='step',
        )

    _preview_sample_step = None

    @classmethod
    def _get_preview_sample_step(cls):
        """Create a lightweight FunctionStep instance for introspection (cached)."""
        if cls._preview_sample_step is None:
            from openhcs.core.steps.function_step import FunctionStep
            cls._preview_sample_step = FunctionStep(func=lambda *args, **kwargs: None)
        return cls._preview_sample_step
    
    def handle_button_action(self, action: str):
        """
        Handle button actions (extracted from Textual version).
        
        Args:
            action: Action identifier
        """
        # Action mapping (preserved from Textual version)
        action_map = {
            "add_step": self.action_add_step,
            "del_step": self.action_delete_step,
            "edit_step": self.action_edit_step,
            "auto_load_pipeline": self.action_auto_load_pipeline,
            "code_pipeline": self.action_code_pipeline,
        }
        
        if action in action_map:
            action_func = action_map[action]
            
            # Handle async actions
            if inspect.iscoroutinefunction(action_func):
                # Run async action in thread
                self.run_async_action(action_func)
            else:
                action_func()
    
    def run_async_action(self, async_func: Callable):
        """
        Run async action using service adapter.

        Args:
            async_func: Async function to execute
        """
        self.service_adapter.execute_async_operation(async_func)
    
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
        display_text = self._format_resolved_step_for_display(step_for_display, step, live_context_snapshot)
        step_name = getattr(step_for_display, 'name', 'Unknown Step')
        return display_text, step_name

    def _format_resolved_step_for_display(
        self,
        step_for_display: FunctionStep,
        original_step: FunctionStep,
        live_context_snapshot=None,
        saved_context_snapshot=None
    ) -> str:
        """
        Format ALREADY RESOLVED step for display.

        This is the extracted logic that uses an already-resolved step preview instance.

        Args:
            step_for_display: Already resolved step preview instance
            original_step: Original step (with saved values, not merged with live)
            live_context_snapshot: Live context snapshot (for config resolution)
            saved_context_snapshot: Optional pre-collected saved context snapshot (for batch processing)

        Returns:
            Display text string
        """
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

        # Optional configurations preview - use lazy resolution system for enabled fields
        # CRITICAL: Must resolve through context hierarchy (Global -> Pipeline -> Step)
        # to match the same resolution that step editor placeholders use
        from openhcs.pyqt_gui.widgets.config_preview_formatters import format_config_indicator

        # Token-scoped resolution cache (per debounce cycle)
        current_token = getattr(live_context_snapshot, 'token', None) if live_context_snapshot else None
        if self._attr_resolution_cache_token != current_token:
            self._attr_resolution_cache.clear()
            self._attr_resolution_cache_token = current_token

        def _cached_resolve(step_obj: FunctionStep, config_obj, attr_name: str, context):
            cache_key = (getattr(context, 'token', None), id(config_obj), attr_name)
            if cache_key in self._attr_resolution_cache:
                return self._attr_resolution_cache[cache_key]
            result = self._resolve_config_attr(step_obj, config_obj, attr_name, context)
            self._attr_resolution_cache[cache_key] = result
            return result

        config_indicators = []
        for config_attr in self.STEP_CONFIG_INDICATORS.keys():
            config = getattr(step_for_display, config_attr, None)
            if config is None:
                continue

            # Create resolver function that uses live context with caching
            def resolve_attr(parent_obj, config_obj, attr_name, context):
                return _cached_resolve(step_for_display, config_obj, attr_name, live_context_snapshot)

            # Use centralized formatter with unsaved change detection
            indicator_text = format_config_indicator(
                config_attr,
                config,
                resolve_attr,
                parent_obj=step_for_display,  # Pass step for context
                live_context_snapshot=live_context_snapshot  # Pass snapshot for unsaved change detection
            )

            if indicator_text:
                config_indicators.append(indicator_text)

        if config_indicators:
            preview_parts.append(f"configs=[{','.join(config_indicators)}]")

        # Check if step has any unsaved changes
        # CRITICAL: We need TWO step instances:
        # 1. PREVIEW instance (with live values merged) for LIVE comparison
        # 2. ORIGINAL instance (saved values) for SAVED comparison
        from openhcs.pyqt_gui.widgets.config_preview_formatters import check_step_has_unsaved_changes
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

        # step_for_display is already the preview instance with live values merged
        step_preview = step_for_display

        def resolve_attr(parent_obj, config_obj, attr_name, context):
            # If context token matches live token, use preview instance
            # If context token is different (saved snapshot), use original instance
            is_live_context = (context.token == current_token)
            step_to_use = step_preview if is_live_context else original_step
            return _cached_resolve(step_to_use, config_obj, attr_name, context)

        logger.info(f"🔍 _format_resolved_step_for_display: About to call check_step_has_unsaved_changes for step {getattr(original_step, 'name', 'unknown')}")
        has_unsaved = check_step_has_unsaved_changes(
            original_step,  # Use ORIGINAL step as parent_obj (for field extraction)
            self.STEP_CONFIG_INDICATORS,
            resolve_attr,
            live_context_snapshot,
            scope_filter=self.current_plate,  # CRITICAL: Pass scope filter
            saved_context_snapshot=saved_context_snapshot  # PERFORMANCE: Reuse saved snapshot
        )
        logger.info(f"🔍 _format_resolved_step_for_display: check_step_has_unsaved_changes returned {has_unsaved} for step {getattr(original_step, 'name', 'unknown')}")

        logger.info(f"🔍 _format_resolved_step_for_display: step_name={step_name}, has_unsaved={has_unsaved}")

        # Add unsaved changes marker to step name if needed
        display_step_name = f"{step_name}†" if has_unsaved else step_name

        # Build display text
        if preview_parts:
            preview = " | ".join(preview_parts)
            display_text = f"▶ {display_step_name}  ({preview})"
        else:
            display_text = f"▶ {display_step_name}"

        return display_text

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

        for config_attr in self.STEP_CONFIG_INDICATORS.keys():
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

            self.update_step_list()
            self.pipeline_changed.emit(self.pipeline_steps)

        # Create and show editor dialog within the correct config context
        orchestrator = self._get_current_orchestrator()

        # SIMPLIFIED: Orchestrator context is automatically available through type-based registry
        # No need for explicit context management - dual-axis resolver handles it automatically
        if not orchestrator:
            pass  # No orchestrator available

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

        editor.show()
        editor.raise_()
        editor.activateWindow()
    
    def action_delete_step(self):
        """Handle Delete Step button (extracted from Textual version)."""
        # Get selected item indices instead of step objects to handle duplicate names
        selected_indices = []
        for item in self.step_list.selectedItems():
            step_index = item.data(Qt.ItemDataRole.UserRole)
            if step_index is not None:
                selected_indices.append(step_index)

        if not selected_indices:
            self.service_adapter.show_error_dialog("No steps selected to delete.")
            return

        # Remove selected steps by index (not by name to handle duplicates)
        indices_to_remove = set(selected_indices)
        new_steps = [step for i, step in enumerate(self.pipeline_steps) if i not in indices_to_remove]

        self.pipeline_steps = new_steps
        self._normalize_step_scope_tokens()
        self.update_step_list()
        self.pipeline_changed.emit(self.pipeline_steps)

        deleted_count = len(selected_indices)
        self.status_message.emit(f"Deleted {deleted_count} steps")
    
    def action_edit_step(self):
        """Handle Edit Step button (adapted from Textual version)."""
        selected_items = self.get_selected_steps()
        if not selected_items:
            self.service_adapter.show_error_dialog("No step selected to edit.")
            return

        step_to_edit = selected_items[0]

        # Open step editor dialog
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
            self.update_step_list()
            self.pipeline_changed.emit(self.pipeline_steps)
            self.status_message.emit(f"Updated step: {edited_step.name}")

        # SIMPLIFIED: Orchestrator context is automatically available through type-based registry
        # No need for explicit context management - dual-axis resolver handles it automatically
        orchestrator = self._get_current_orchestrator()

        # Find step position for scope-based styling
        try:
            step_position = self.pipeline_steps.index(step_to_edit)
        except ValueError:
            step_position = None

        # FOCUS-INSTEAD-OF-DUPLICATE: Build scope_id and check for existing window
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        scope_id = self._build_step_scope_id(step_to_edit, position=None)  # No position for window lookup
        if ParameterFormManager.focus_existing_window(scope_id):
            return  # Existing window was focused, don't create new one

        editor = DualEditorWindow(
            step_data=step_to_edit,
            is_new=False,
            on_save_callback=handle_save,
            orchestrator=orchestrator,
            gui_config=self.gui_config,
            parent=self,
            step_position=step_position
        )
        # Set original step for change detection
        editor.set_original_step_for_change_detection()

        # Register window for focus-instead-of-duplicate behavior
        ParameterFormManager.register_window_for_scope(scope_id, editor)

        # Connect orchestrator config changes to step editor for live placeholder updates
        # This ensures the step editor's placeholders update when pipeline config is saved
        if self.plate_manager and hasattr(self.plate_manager, 'orchestrator_config_changed'):
            self.plate_manager.orchestrator_config_changed.connect(editor.on_orchestrator_config_changed)

        editor.show()
        editor.raise_()
        editor.activateWindow()

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

            # DEBUG: Check what VariableComponents values are in namespace
            if 'VariableComponents' in namespace:
                vc = namespace['VariableComponents']
                logger.info(f"🔍 AUTO: VariableComponents.CHANNEL = {vc.CHANNEL}")
                logger.info(f"🔍 AUTO: VariableComponents.Z_INDEX = {vc.Z_INDEX}")
                logger.info(f"🔍 AUTO: VariableComponents.SITE = {vc.SITE}")

            # DEBUG: Check LazyProcessingConfig class ID
            if 'LazyProcessingConfig' in namespace:
                lpc = namespace['LazyProcessingConfig']
                logger.info(f"🔍 AUTO: LazyProcessingConfig class id={id(lpc)}")
                logger.info(f"🔍 AUTO: LazyProcessingConfig.__init__ = {lpc.__init__}")
                logger.info(f"🔍 AUTO: LazyProcessingConfig has __deepcopy__? {hasattr(lpc, '__deepcopy__')}")
                if hasattr(lpc, '__deepcopy__'):
                    logger.info(f"🔍 AUTO: LazyProcessingConfig.__deepcopy__ = {lpc.__deepcopy__}")

            # Get the pipeline_steps from the namespace
            if 'pipeline_steps' in namespace:
                new_pipeline_steps = namespace['pipeline_steps']

                # DEBUG: Check what values the steps have right after exec
                for i, step in enumerate(new_pipeline_steps):
                    if hasattr(step, 'processing_config') and step.processing_config:
                        pc = step.processing_config
                        # Use object.__getattribute__ to get RAW value
                        raw_vc = object.__getattribute__(pc, 'variable_components')
                        logger.info(f"🔍 AUTO: Step {i} RAW variable_components = {raw_vc}")

                        # Test if deepcopy calls __deepcopy__
                        if i == 1:  # Test on step 1 which has CHANNEL
                            import copy
                            logger.info(f"🔍 AUTO: Testing deepcopy on step {i} processing_config")
                            logger.info(f"🔍 AUTO: pc has __deepcopy__? {hasattr(pc, '__deepcopy__')}")
                            copied_pc = copy.deepcopy(pc)
                            copied_raw_vc = object.__getattribute__(copied_pc, 'variable_components')
                            logger.info(f"🔍 AUTO: After deepcopy processing_config, RAW variable_components = {copied_raw_vc}")

                            # Now test deepcopy on the entire step
                            logger.info(f"🔍 AUTO: Testing deepcopy on entire step {i}")
                            copied_step = copy.deepcopy(step)
                            copied_step_pc = copied_step.processing_config
                            if copied_step_pc:
                                copied_step_raw_vc = object.__getattribute__(copied_step_pc, 'variable_components')
                                logger.info(f"🔍 AUTO: After deepcopy step, RAW variable_components = {copied_step_raw_vc}")
                                # Check tracking attributes
                                try:
                                    tracking = object.__getattribute__(copied_step_pc, '_explicitly_set_fields')
                                    logger.info(f"🔍 AUTO: After deepcopy step, _explicitly_set_fields = {tracking}")
                                except AttributeError:
                                    logger.info(f"🔍 AUTO: After deepcopy step, _explicitly_set_fields MISSING!")

                                # Now test RESOLVED value (using normal getattr, which triggers lazy resolution)
                                resolved_vc = copied_step_pc.variable_components
                                logger.info(f"🔍 AUTO: After deepcopy step, RESOLVED variable_components = {resolved_vc}")

                # Update the pipeline with new steps
                self.pipeline_steps = new_pipeline_steps

                # DEBUG: Check RAW values BEFORE normalize
                for i, step in enumerate(self.pipeline_steps):
                    if hasattr(step, 'processing_config') and step.processing_config:
                        pc = step.processing_config
                        raw_vc = object.__getattribute__(pc, 'variable_components')
                        logger.info(f"🔍 AUTO: BEFORE normalize - Step {i} RAW variable_components = {raw_vc}")

                self._normalize_step_scope_tokens()

                # DEBUG: Check RAW values AFTER normalize
                for i, step in enumerate(self.pipeline_steps):
                    if hasattr(step, 'processing_config') and step.processing_config:
                        pc = step.processing_config
                        raw_vc = object.__getattribute__(pc, 'variable_components')
                        logger.info(f"🔍 AUTO: AFTER normalize - Step {i} RAW variable_components = {raw_vc}")

                # CRITICAL: Increment token to invalidate cache after loading new pipeline
                # Auto-loading creates new step instances with different config values,
                # but doesn't open any parameter forms, so the token doesn't get incremented automatically.
                # Without this, the cache returns stale values from the previous pipeline.
                from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
                ParameterFormManager._live_context_token_counter += 1
                logger.info(f"🔍 AUTO: Incremented token to {ParameterFormManager._live_context_token_counter} after loading pipeline")

                self.update_step_list()
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

            # Launch editor with callback and code_type for clean mode toggle
            editor_service.edit_code(
                initial_content=python_code,
                title="Edit Pipeline Steps",
                callback=self._handle_edited_pipeline_code,
                use_external=use_external,
                code_type='pipeline',
                code_data={'clean_mode': True}
            )

        except Exception as e:
            logger.error(f"Failed to open pipeline code editor: {e}")
            self.service_adapter.show_error_dialog(f"Failed to open code editor: {str(e)}")

    def _handle_edited_pipeline_code(self, edited_code: str) -> None:
        """Handle the edited pipeline code from code editor."""
        try:
            # Ensure we have a string
            if not isinstance(edited_code, str):
                logger.error(f"Expected string, got {type(edited_code)}: {edited_code}")
                raise ValueError("Invalid code format received from editor")

            # CRITICAL FIX: Execute code with lazy dataclass constructor patching to preserve None vs concrete distinction
            namespace = {}
            try:
                # Try normal execution first
                with self._patch_lazy_constructors():
                    exec(edited_code, namespace)
            except TypeError as e:
                # If TypeError about unexpected keyword arguments (old-format constructors), retry with migration
                error_msg = str(e)
                if "unexpected keyword argument" in error_msg and ("group_by" in error_msg or "variable_components" in error_msg):
                    namespace = {}
                    from openhcs.io.pipeline_migration import patch_step_constructors_for_migration
                    with self._patch_lazy_constructors(), patch_step_constructors_for_migration():
                        exec(edited_code, namespace)
                else:
                    # Not a migration issue, re-raise
                    raise

            # Get the pipeline_steps from the namespace
            if 'pipeline_steps' in namespace:
                new_pipeline_steps = namespace['pipeline_steps']
                # Update the pipeline with new steps
                self.pipeline_steps = new_pipeline_steps
                self._normalize_step_scope_tokens()
                self.update_step_list()
                self.pipeline_changed.emit(self.pipeline_steps)
                self.status_message.emit(f"Pipeline updated with {len(new_pipeline_steps)} steps")

                # CRITICAL: Broadcast to global event bus for ALL windows to receive
                # This is the OpenHCS "set and forget" pattern - one broadcast reaches everyone
                self._broadcast_to_event_bus(new_pipeline_steps)

                # CRITICAL: Trigger global cross-window refresh for ALL open windows
                # This ensures any window with placeholders (configs, steps, etc.) refreshes
                from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
                ParameterFormManager.trigger_global_cross_window_refresh()
            else:
                raise ValueError("No 'pipeline_steps = [...]' assignment found in edited code")

        except (SyntaxError, Exception) as e:
            logger.error(f"Failed to parse edited pipeline code: {e}")
            # Re-raise so the code editor can handle it (keep dialog open, move cursor to error line)
            raise

    def _patch_lazy_constructors(self):
        """Context manager that patches lazy dataclass constructors to preserve None vs concrete distinction."""
        from openhcs.introspection import patch_lazy_constructors
        return patch_lazy_constructors()

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
                self.update_step_list()
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
    
    def set_current_plate(self, plate_path: str):
        """
        Set current plate and load its pipeline (extracted from Textual version).

        Args:
            plate_path: Path of the current plate
        """
        self.current_plate = plate_path

        # Load pipeline for the new plate
        if plate_path:
            plate_pipeline = self.plate_pipelines.get(plate_path, [])
            self.pipeline_steps = plate_pipeline
        else:
            self.pipeline_steps = []

        self._normalize_step_scope_tokens()

        self.update_step_list()
        self.update_button_states()

    def _broadcast_to_event_bus(self, pipeline_steps: list):
        """Broadcast pipeline changed event to global event bus.

        Args:
            pipeline_steps: Updated list of FunctionStep objects
        """
        if self.event_bus:
            self.event_bus.emit_pipeline_changed(pipeline_steps)

    def on_orchestrator_config_changed(self, plate_path: str, effective_config):
        """
        Handle orchestrator configuration changes for placeholder refresh.

        Args:
            plate_path: Path of the plate whose orchestrator config changed
            effective_config: The orchestrator's new effective configuration
        """
        # Only refresh if this is for the current plate
        if plate_path == self.current_plate:
            pass  # Orchestrator config changed for current plate

    def _build_context_stack_with_live_values(
        self,
        step: FunctionStep,
        live_context_snapshot: Optional['LiveContextSnapshot'],
        step_is_preview: bool = False
    ) -> Optional[list]:
        """
        Build context stack for resolution with live values merged.

        CRITICAL: This MUST use preview instances (with scoped live values merged)
        for all objects in the context stack. Using original objects will cause
        step editor changes to be invisible during resolution.

        Pattern:
        1. Get preview instance for each object (merges scoped live values)
        2. Build context stack: GlobalPipelineConfig → PipelineConfig → Step
        3. Pass to LiveContextResolver

        This is the SINGLE SOURCE OF TRUTH for building context stacks.
        All resolution code (flash detection, unsaved changes, label updates)
        MUST use this method.

        See: docs/source/development/scope_hierarchy_live_context.rst

        Args:
            step: Step object (original from pipeline_steps OR preview instance)
            live_context_snapshot: Live context snapshot with scoped values
            step_is_preview: If True, step is already a preview instance (don't merge again)
                            If False, step is original (merge scoped live values)

        Returns:
            Context stack [GlobalPipelineConfig, PipelineConfig, Step] with live values,
            or None if orchestrator not available
        """
        from openhcs.core.config import GlobalPipelineConfig
        from openhcs.config_framework.global_config import get_current_global_config

        orchestrator = self._get_current_orchestrator()
        if not orchestrator:
            return None

        try:
            logger.info(f"🔍 _build_context_stack_with_live_values: Building context stack for step {getattr(step, 'name', 'unknown')}")
            logger.info(f"🔍 _build_context_stack_with_live_values: live_context_snapshot.token={live_context_snapshot.token if live_context_snapshot else None}")

            # Get preview instances with scoped live values merged
            pipeline_config = self._get_pipeline_config_preview_instance(live_context_snapshot) or orchestrator.pipeline_config
            logger.info(f"🔍 _build_context_stack_with_live_values: pipeline_config type={type(pipeline_config).__name__}, id={id(pipeline_config)}")

            # Check if pipeline_config has well_filter_config
            if hasattr(pipeline_config, 'well_filter_config'):
                wfc = pipeline_config.well_filter_config
                logger.info(f"🔍 _build_context_stack_with_live_values: pipeline_config.well_filter_config type={type(wfc).__name__}")
                # Get RAW value without triggering lazy resolution
                try:
                    raw_well_filter = object.__getattribute__(wfc, 'well_filter')
                    logger.info(f"🔍 _build_context_stack_with_live_values: pipeline_config.well_filter_config.well_filter (RAW) = {raw_well_filter}")
                except AttributeError:
                    logger.info(f"🔍 _build_context_stack_with_live_values: pipeline_config.well_filter_config.well_filter (RAW) = N/A")

            global_config = self._get_global_config_preview_instance(live_context_snapshot)
            if global_config is None:
                global_config = get_current_global_config(GlobalPipelineConfig)

            # Get step preview instance (or use as-is if already a preview)
            if step_is_preview:
                # Step is already a preview instance (from flash detection caller)
                step_preview = step
            else:
                # Step is original - merge scoped live values
                step_preview = self._get_step_preview_instance(step, live_context_snapshot)

            # Build context stack: GlobalPipelineConfig → PipelineConfig → Step (with live values)
            logger.info(f"🔍 _build_context_stack_with_live_values: Context stack built: [GlobalPipelineConfig, PipelineConfig(id={id(pipeline_config)}), Step]")
            return [global_config, pipeline_config, step_preview]

        except Exception:
            return None

    def _build_flash_context_stack(self, obj: Any, live_context_snapshot) -> Optional[list]:
        """Build context stack for flash resolution.

        Builds: GlobalPipelineConfig → PipelineConfig → Step

        Args:
            obj: Step object (PREVIEW INSTANCE with live values already merged)
            live_context_snapshot: Live context snapshot

        Returns:
            Context stack for resolution, or None if orchestrator not available
        """
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

        # Collect live context if not provided
        if live_context_snapshot is None:
            live_context_snapshot = ParameterFormManager.collect_live_context(scope_filter=self.current_plate)

        # Use centralized context stack builder
        # obj is ALREADY a preview instance (caller created it), so set step_is_preview=True
        return self._build_context_stack_with_live_values(
            step=obj,
            live_context_snapshot=live_context_snapshot,
            step_is_preview=True  # Don't merge again - already a preview instance
        )

    def _resolve_config_attr(self, step: FunctionStep, config: object, attr_name: str,
                             live_context_snapshot=None) -> object:
        """
        Resolve any config attribute through lazy resolution system using LIVE context.

        Uses LiveContextResolver service from configuration framework for cached resolution.

        IMPORTANT: The 'step' parameter is the ORIGINAL step from pipeline_steps.
        This method internally converts it to a preview instance with live values.
        Do NOT pass a preview instance as the 'step' parameter.

        Args:
            step: FunctionStep containing the config (original, not preview instance)
            config: Config dataclass instance (e.g., LazyNapariStreamingConfig)
            attr_name: Name of the attribute to resolve (e.g., 'enabled', 'well_filter')
            live_context_snapshot: Optional pre-collected LiveContextSnapshot (for performance)

        Returns:
            Resolved attribute value (type depends on attribute)
        """
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

        try:
            # Collect live context if not provided (for backwards compatibility)
            if live_context_snapshot is None:
                live_context_snapshot = ParameterFormManager.collect_live_context(scope_filter=self.current_plate)

            # Use centralized context stack builder (ensures preview instances are used)
            context_stack = self._build_context_stack_with_live_values(step, live_context_snapshot)
            if context_stack is None:
                return None

            # Resolve using service
            resolved_value = self._live_context_resolver.resolve_config_attr(
                config_obj=config,
                attr_name=attr_name,
                context_stack=context_stack,
                live_context=live_context_snapshot.values,
                cache_token=live_context_snapshot.token
            )

            return resolved_value

        except Exception as e:
            import traceback
            logger.warning(f"Failed to resolve config.{attr_name} for {type(config).__name__}: {e}")
            logger.warning(f"Traceback: {traceback.format_exc()}")
            # Fallback to raw value
            raw_value = object.__getattribute__(config, attr_name)
            return raw_value

    def _build_step_scope_id(self, step: FunctionStep, position: Optional[int] = None) -> Optional[str]:
        """Return the hierarchical scope id for a step editor instance.

        Args:
            step: The step to build scope_id for
            position: Optional position of step in pipeline (for per-orchestrator visual styling)
                     If None, scope_id will NOT include @position suffix

        Returns:
            Scope ID in format "plate_path::step_token@position" (if position provided)
            or "plate_path::step_token" (if position is None)

        Note:
            - For cross-window updates: use position=None to match DualEditorWindow scope_id
            - For visual styling: use position=idx to get per-orchestrator colors
        """
        token = self._ensure_step_scope_token(step)
        plate_scope = self.current_plate or "no_plate"

        # Include position for per-orchestrator visual styling ONLY if explicitly provided
        if position is not None:
            return f"{plate_scope}::{token}@{position}"
        else:
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

    def _merge_with_live_values(self, obj: Any, live_values: Dict[str, Any]) -> Any:
        """Merge object with live values from ParameterFormManager.

        Implementation of CrossWindowPreviewMixin hook for PipelineEditor.
        Handles both dataclass objects (PipelineConfig, GlobalPipelineConfig) and
        non-dataclass objects (FunctionStep).

        Args:
            obj: Object to merge (FunctionStep, PipelineConfig, or GlobalPipelineConfig)
            live_values: Dict of field_name -> value from ParameterFormManager

        Returns:
            New object with live values merged
        """
        if not live_values:
            return obj

        # Reconstruct live values (handles nested dataclasses)
        reconstructed_values = self._live_context_resolver.reconstruct_live_values(live_values)
        if not reconstructed_values:
            return obj

        # Try dataclasses.replace for dataclasses
        if dataclasses.is_dataclass(obj):
            try:
                return dataclasses.replace(obj, **reconstructed_values)
            except Exception:
                return obj

        # For non-dataclass objects (like FunctionStep), use manual merge
        try:
            obj_clone = copy.deepcopy(obj)
        except Exception:
            obj_clone = copy.copy(obj)

        for field_name, value in reconstructed_values.items():
            setattr(obj_clone, field_name, value)

        return obj_clone

    def _get_step_preview_instance(self, step: FunctionStep, live_context_snapshot) -> FunctionStep:
        """Return a step instance that includes any live overrides for previews."""
        logger.info(f"🔍 PREVIEW: _get_step_preview_instance called for step {step.name}")
        logger.info(f"🔍 PREVIEW: live_context_snapshot = {live_context_snapshot}")

        if live_context_snapshot is None:
            logger.info(f"🔍 PREVIEW: Returning step early - no live context snapshot")
            return step

        token = getattr(live_context_snapshot, 'token', None)
        logger.info(f"🔍 PREVIEW: token = {token}")
        if token is None:
            logger.info(f"🔍 PREVIEW: Returning step early - no token")
            return step

        # Token-based caching to avoid redundant merges
        if self._preview_step_cache_token != token:
            self._preview_step_cache.clear()
            self._preview_step_cache_token = token

        cache_key = id(step)
        cached_step = self._preview_step_cache.get(cache_key)
        if cached_step is not None:
            return cached_step

        # DEBUG: Check RAW value BEFORE merge
        if hasattr(step, 'processing_config') and step.processing_config:
            pc = step.processing_config
            raw_vc = object.__getattribute__(pc, 'variable_components')
            logger.info(f"🔍 PREVIEW: BEFORE merge - step {step.name} RAW variable_components = {raw_vc}")

        # Use generic helper to merge scoped live values
        scope_id = self._build_step_scope_id(step)
        merged_step = self._get_preview_instance_generic(
            obj=step,
            obj_type=type(step),
            scope_id=scope_id,
            live_context_snapshot=live_context_snapshot,
            use_global_values=False
        )

        # DEBUG: Check RAW value AFTER merge
        if hasattr(merged_step, 'processing_config') and merged_step.processing_config:
            pc = merged_step.processing_config
            raw_vc = object.__getattribute__(pc, 'variable_components')
            logger.info(f"🔍 PREVIEW: AFTER merge - step {merged_step.name} RAW variable_components = {raw_vc}")

        self._preview_step_cache[cache_key] = merged_step
        return merged_step

    def _get_step_preview_instance_excluding_self(self, step: FunctionStep, live_context_snapshot) -> FunctionStep:
        """Return step instance WITHOUT its own editor values (for flash detection).

        This allows flash detection to see inheritance changes even when step editor is open.
        E.g., if pipeline_config.well_filter changes and step inherits it, the step should flash
        even if the step editor is currently open with a concrete value.
        """
        if live_context_snapshot is None:
            return step

        # Get the step's scope ID
        scope_id = self._build_step_scope_id(step)
        if not scope_id:
            return step

        # Clone the live context snapshot but exclude this step's values
        scoped_values = getattr(live_context_snapshot, 'scoped_values', {}) or {}
        scope_entries = scoped_values.get(scope_id)
        if not scope_entries:
            return step

        # Check if this step has live values
        if type(step) not in scope_entries:
            return step

        # Create a modified snapshot without this step's values
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import LiveContextSnapshot
        modified_scoped_values = {
            scope: {
                config_type: values
                for config_type, values in entries.items()
                if config_type != type(step)  # Exclude step's own type
            }
            for scope, entries in scoped_values.items()
        }

        modified_snapshot = LiveContextSnapshot(
            token=live_context_snapshot.token,
            values=getattr(live_context_snapshot, 'values', {}),
            scoped_values=modified_scoped_values
        )

        # Now get preview instance with modified snapshot (no step values)
        return self._get_step_preview_instance(step, modified_snapshot)

    def _get_pipeline_config_preview_instance(self, live_context_snapshot):
        """Return pipeline config merged with live overrides for current plate.

        Uses CrossWindowPreviewMixin._get_preview_instance_generic for scoped values.

        CRITICAL: This method must merge BOTH:
        1. Scoped PipelineConfig values (from PipelineConfig editor)
        2. Global GlobalPipelineConfig values (from GlobalPipelineConfig editor)

        The global values should be applied FIRST, then scoped values override them.
        """
        from openhcs.core.config import GlobalPipelineConfig

        orchestrator = self._get_current_orchestrator()
        if not orchestrator:
            return None

        pipeline_config = orchestrator.pipeline_config
        logger.info(f"🔍 _get_pipeline_config_preview_instance: Original pipeline_config id={id(pipeline_config)}")

        if not self.current_plate:
            logger.info(f"🔍 _get_pipeline_config_preview_instance: No current_plate, returning original")
            return pipeline_config

        if live_context_snapshot is None:
            logger.info(f"🔍 _get_pipeline_config_preview_instance: No live_context_snapshot, returning original")
            return pipeline_config

        logger.info(f"🔍 _get_pipeline_config_preview_instance: live_context_snapshot.token={live_context_snapshot.token}")

        # Step 1: Get scoped PipelineConfig values (from PipelineConfig editor)
        scope_id = self.current_plate
        scoped_values = getattr(live_context_snapshot, 'scoped_values', {}) or {}
        scope_entries = scoped_values.get(scope_id, {})
        pipeline_config_live_values = scope_entries.get(type(pipeline_config), {})
        logger.info(f"🔍 _get_pipeline_config_preview_instance: Scoped PipelineConfig live values: {list(pipeline_config_live_values.keys()) if pipeline_config_live_values else 'EMPTY'}")

        # Step 2: Get global GlobalPipelineConfig values (from GlobalPipelineConfig editor)
        global_values = getattr(live_context_snapshot, 'values', {}) or {}
        global_config_live_values = global_values.get(GlobalPipelineConfig, {})
        logger.info(f"🔍 _get_pipeline_config_preview_instance: Global GlobalPipelineConfig live values: {list(global_config_live_values.keys()) if global_config_live_values else 'EMPTY'}")

        # Step 3: Merge global values first, then scoped values (scoped overrides global)
        merged_live_values = {}
        merged_live_values.update(global_config_live_values)  # Global values first
        merged_live_values.update(pipeline_config_live_values)  # Scoped values override
        logger.info(f"🔍 _get_pipeline_config_preview_instance: Merged live values: {list(merged_live_values.keys()) if merged_live_values else 'EMPTY'}")

        if not merged_live_values:
            logger.info(f"🔍 _get_pipeline_config_preview_instance: No merged values, returning original pipeline_config")
            return pipeline_config

        # Step 4: Merge into PipelineConfig instance
        logger.info(f"🔍 _get_pipeline_config_preview_instance: Merging live values into pipeline_config")
        merged_config = self._merge_with_live_values(pipeline_config, merged_live_values)
        logger.info(f"🔍 _get_pipeline_config_preview_instance: Merged config id={id(merged_config)}")

        # Check merged config's well_filter_config
        if hasattr(merged_config, 'well_filter_config'):
            wfc = merged_config.well_filter_config
            logger.info(f"🔍 _get_pipeline_config_preview_instance: merged_config.well_filter_config type={type(wfc).__name__}")
            try:
                raw_well_filter = object.__getattribute__(wfc, 'well_filter')
                logger.info(f"🔍 _get_pipeline_config_preview_instance: merged_config.well_filter_config.well_filter (RAW) = {raw_well_filter}")
            except AttributeError:
                logger.info(f"🔍 _get_pipeline_config_preview_instance: merged_config.well_filter_config.well_filter (RAW) = N/A")

        return merged_config

    def _get_global_config_preview_instance(self, live_context_snapshot):
        """Return global config merged with live overrides.

        Uses CrossWindowPreviewMixin._get_preview_instance_generic for global values.
        """
        from openhcs.core.config import GlobalPipelineConfig

        # Use mixin's generic helper (global values)
        return self._get_preview_instance_generic(
            obj=self.global_config,
            obj_type=GlobalPipelineConfig,
            scope_id=None,
            live_context_snapshot=live_context_snapshot,
            use_global_values=True
        )






    def _build_scope_index_map(self) -> Dict[str, int]:
        scope_map: Dict[str, int] = {}
        for idx, step in enumerate(self.pipeline_steps):
            # Build scope_id WITHOUT @position for cross-window updates
            # The @position suffix is only for visual styling, not for scope matching
            scope_id = self._build_step_scope_id(step, position=None)
            if scope_id:
                scope_map[scope_id] = idx
        return scope_map

    def _resolve_scope_targets(self, scope_id: Optional[str]):
        """Override to handle PipelineConfig and GlobalPipelineConfig changes affecting all steps.

        When PipelineConfig or GlobalPipelineConfig changes, all steps need to be updated because they
        inherit from these configs. Return all step indices for incremental update.

        Returns:
            (target_keys, requires_full_refresh)
        """
        from openhcs.core.config import PipelineConfig

        # If scope_id is ALL_ITEMS_SCOPE (GlobalPipelineConfig or PipelineConfig), return all step indices
        if scope_id == self.ALL_ITEMS_SCOPE:
            all_step_indices = set(range(len(self.pipeline_steps)))
            logger.info(f"🔍 PipelineEditor._resolve_scope_targets: scope_id=ALL_ITEMS_SCOPE, returning all_step_indices={all_step_indices}")
            return all_step_indices, False

        # If scope_id is None, check if this is a PipelineConfig change
        # by checking if the current plate is set (PipelineConfig is plate-scoped)
        if scope_id is None and self.current_plate:
            # This is likely a PipelineConfig change - update all steps incrementally
            # Return all step indices as target keys
            all_step_indices = set(range(len(self.pipeline_steps)))
            logger.info(f"🔍 PipelineEditor._resolve_scope_targets: scope_id=None, returning all_step_indices={all_step_indices}")
            return all_step_indices, False

        # Otherwise use parent implementation
        result = super()._resolve_scope_targets(scope_id)
        logger.info(f"🔍 PipelineEditor._resolve_scope_targets: scope_id={scope_id}, result={result}, _preview_scope_map size={len(self._preview_scope_map)}")
        return result

    def _process_pending_preview_updates(self) -> None:
        logger.info(f"🔥 PipelineEditor._process_pending_preview_updates called: _pending_preview_keys={self._pending_preview_keys}")

        if not self._pending_preview_keys:
            logger.info(f"🔥 PipelineEditor: No pending preview keys - returning early")
            return

        if not self.current_plate:
            self._pending_preview_keys.clear()
            self._pending_label_keys.clear()
            self._pending_changed_fields.clear()
            return

        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

        # Get current live context snapshot WITH scope filter (critical for resolution)
        if not self.current_plate:
            return

        # PERFORMANCE: Use pre-computed batch snapshots if available (coordinator path)
        batch_live, _ = ParameterFormManager.get_batch_snapshots()
        if batch_live is not None:
            live_context_snapshot = batch_live
            logger.info(f"📸 Using batch live_context_snapshot (token={live_context_snapshot.token})")
        else:
            live_context_snapshot = ParameterFormManager.collect_live_context(scope_filter=self.current_plate)

        indices = sorted(
            idx for idx in self._pending_preview_keys if isinstance(idx, int)
        )
        label_indices = {idx for idx in self._pending_label_keys if isinstance(idx, int)}

        # Copy changed fields before clearing
        changed_fields = set(self._pending_changed_fields) if self._pending_changed_fields else None

        # Use last snapshot as "before" for comparison
        live_context_before = self._last_live_context_snapshot

        logger.info(f"🔍 PipelineEditor._process_pending_preview_updates START:")
        logger.info(f"  - _last_live_context_snapshot is None: {live_context_before is None}")
        logger.info(f"  - _last_live_context_snapshot token: {getattr(live_context_before, 'token', None)}")
        logger.info(f"  - live_context_snapshot token: {getattr(live_context_snapshot, 'token', None)}")
        logger.info(f"  - Pending indices: {len(indices)}")
        logger.info(f"  - Changed fields: {changed_fields}")

        # CRITICAL: DON'T update _last_live_context_snapshot here!
        # We want to keep the original "before" state across multiple edits in the same editing session.
        # Only update it when the editing session ends (window close, focus change, etc.)
        # This allows flash detection to work for ALL changes in a session, not just the first one.

        # Clear pending updates
        self._pending_preview_keys.clear()
        self._pending_label_keys.clear()
        self._pending_changed_fields.clear()

        logger.debug(f"🔥 Calling _refresh_step_items_by_index with {len(indices)} indices")

        # Refresh with changed fields for flash logic
        self._refresh_step_items_by_index(
            indices,
            live_context_snapshot,
            changed_fields,
            live_context_before,
            label_indices=label_indices,
        )

    def _handle_full_preview_refresh(self) -> None:
        """Handle full refresh WITH flash (used for window close/reset events).

        When a window closes with unsaved changes or reset is clicked, values revert
        to saved state and should flash to indicate the change.
        """
        if not self.current_plate:
            return

        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

        # CRITICAL: Use saved "after" snapshot if available (from window close)
        # This snapshot was collected AFTER the form manager was unregistered
        # If not available, collect a new snapshot (for reset events)
        live_context_after = getattr(self, '_pending_window_close_after_snapshot', None)
        if live_context_after is None:
            live_context_after = ParameterFormManager.collect_live_context(scope_filter=self.current_plate)

        # Use saved "before" snapshot if available (from window close), otherwise use last snapshot
        live_context_before = getattr(self, '_pending_window_close_before_snapshot', None) or self._last_live_context_snapshot
        logger.info(f"🔍 _handle_full_preview_refresh: live_context_before token={getattr(live_context_before, 'token', None) if live_context_before else None}")
        logger.info(f"🔍 _handle_full_preview_refresh: live_context_after token={getattr(live_context_after, 'token', None) if live_context_after else None}")

        # Get the user-modified fields from the closed window (if available)
        modified_fields = getattr(self, '_pending_window_close_changed_fields', None)
        logger.info(f"🔍 _handle_full_preview_refresh: modified_fields={modified_fields}")

        # Update last snapshot for next comparison
        self._last_live_context_snapshot = live_context_after

        # CRITICAL: Determine which steps to refresh based on what was closed
        # - If GlobalPipelineConfig or PipelineConfig closed: refresh ALL steps (they inherit from these)
        # - If step editor closed: refresh only that specific step
        #
        # We can't rely on '::' to distinguish step vs plate scope because plate paths can contain '::'
        # Instead, check if _pending_preview_keys contains all steps (set by _resolve_scope_targets)
        indices_to_check = list(range(len(self.pipeline_steps)))
        logger.info(f"🔍 _handle_full_preview_refresh: Initial indices_to_check (ALL steps): {indices_to_check}")
        logger.info(f"🔍 _handle_full_preview_refresh: _pending_preview_keys={self._pending_preview_keys}")

        # If _pending_preview_keys contains all step indices, this is a global/plate-level change
        # (GlobalPipelineConfig or PipelineConfig closed) - refresh all steps
        all_step_indices = set(range(len(self.pipeline_steps)))
        if self._pending_preview_keys == all_step_indices:
            logger.info(f"🔍 _handle_full_preview_refresh: _pending_preview_keys matches all steps - global/plate-level change, checking ALL steps")
        elif live_context_before:
            # Otherwise, check if this is a step-specific change by looking at scoped_values
            scoped_values_before = getattr(live_context_before, 'scoped_values', {})
            logger.info(f"🔍 _handle_full_preview_refresh: scoped_values_before keys: {list(scoped_values_before.keys()) if scoped_values_before else 'None'}")
            if scoped_values_before:
                # The before snapshot should have exactly one scope_id (the step being edited)
                # Find which step index matches that scope_id
                scope_ids = list(scoped_values_before.keys())
                if len(scope_ids) == 1:
                    window_close_scope_id = scope_ids[0]
                    logger.info(f"🔍 _handle_full_preview_refresh: window_close_scope_id={window_close_scope_id}")

                    # Find the step that matches this scope_id
                    for idx, step in enumerate(self.pipeline_steps):
                        step_scope_id = self._build_step_scope_id(step)
                        if step_scope_id == window_close_scope_id:
                            indices_to_check = [idx]
                            logger.info(f"🔍 _handle_full_preview_refresh: Found matching step at index {idx}, only checking that step")
                            break
            else:
                logger.info(f"🔍 _handle_full_preview_refresh: No scoped_values_before, checking ALL steps")

        logger.info(f"🔍 _handle_full_preview_refresh: Final indices_to_check: {indices_to_check}")
        self._refresh_step_items_by_index(
            indices_to_check,
            live_context_after,
            changed_fields=modified_fields,  # Only check modified fields from closed window
            live_context_before=live_context_before,
            label_indices=set(indices_to_check),  # Update labels for checked steps
        )

        # Clear the saved snapshots and modified fields after ALL refresh logic is complete
        # CRITICAL: Must be done AFTER _refresh_step_items_by_index because that calls
        # _check_resolved_values_changed_batch which needs these attributes
        if hasattr(self, '_pending_window_close_before_snapshot'):
            delattr(self, '_pending_window_close_before_snapshot')
        if hasattr(self, '_pending_window_close_after_snapshot'):
            delattr(self, '_pending_window_close_after_snapshot')
        if hasattr(self, '_pending_window_close_changed_fields'):
            delattr(self, '_pending_window_close_changed_fields')



    def _refresh_step_items_by_index(
        self,
        indices: Iterable[int],
        live_context_snapshot=None,
        changed_fields=None,
        live_context_before=None,
        *,
        label_indices: Optional[Set[int]] = None,
    ) -> None:
        """Refresh step items incrementally.

        Args:
            indices: Step indices to refresh
            live_context_snapshot: Pre-collected live context (optional)
            changed_fields: Set of field names that changed (for flash logic)
            live_context_before: Live context snapshot before changes (for flash logic)
            label_indices: Optional subset of indices that require label updates
        """
        logger.info(f"🔥 _refresh_step_items_by_index called: indices={indices}, label_indices={label_indices}")

        if not indices:
            return

        if live_context_snapshot is None:
            from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

            if not self.current_plate:
                return
            live_context_snapshot = ParameterFormManager.collect_live_context(scope_filter=self.current_plate)

        label_subset = set(label_indices) if label_indices is not None else None

        # BATCH UPDATE: Collect all steps to update
        step_items = []
        for step_index in sorted(set(indices)):
            if step_index < 0 or step_index >= len(self.pipeline_steps):
                continue
            item = self.step_list.item(step_index)
            if item is None:
                continue
            step = self.pipeline_steps[step_index]
            should_update_labels = (
                label_subset is None or step_index in label_subset
            )
            step_items.append((step_index, item, step, should_update_labels))

        if not step_items:
            return

        # Build before/after step pairs for batch flash detection
        # ALSO store step_after instances to reuse for display formatting
        step_pairs = []
        step_after_instances = []
        for step_index, item, step, should_update_labels in step_items:
            # Get preview instances (before and after)
            # For LABELS: use full live context (includes step editor values)
            step_after = self._get_step_preview_instance(step, live_context_snapshot)

            # For FLASH DETECTION: use FULL context (including step's own editor values)
            step_before_for_flash = self._get_step_preview_instance(step, live_context_before) if live_context_before else None
            step_after_for_flash = step_after  # Reuse the already-computed instance

            step_pairs.append((step_before_for_flash, step_after_for_flash))
            step_after_instances.append(step_after)

        # Batch check which steps should flash
        should_flash_list = self._check_resolved_values_changed_batch(
            step_pairs,
            changed_fields,
            live_context_before=live_context_before,
            live_context_after=live_context_snapshot
        )

        # PHASE 1: Update all labels and styling (this is the slow part - formatting)
        # Do this BEFORE triggering flashes so all flashes start simultaneously
        steps_to_flash = []

        # PERFORMANCE: Use pre-computed batch snapshots if available (coordinator path)
        # This avoids collecting saved context separately for each listener
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

        batch_live, batch_saved = ParameterFormManager.get_batch_snapshots()
        if batch_saved is not None:
            # Fast path: use coordinator's pre-computed saved context
            saved_context_snapshot = batch_saved
            logger.info(f"📸 Using batch saved_context_snapshot (token={saved_context_snapshot.token})")
        else:
            # Fallback: compute saved context ourselves (non-coordinator path)
            saved_managers = ParameterFormManager._active_form_managers.copy()
            saved_token = ParameterFormManager._live_context_token_counter

            try:
                ParameterFormManager._active_form_managers.clear()
                ParameterFormManager._live_context_token_counter += 1
                saved_context_snapshot = ParameterFormManager.collect_live_context(scope_filter=self.current_plate)
            finally:
                ParameterFormManager._active_form_managers[:] = saved_managers
                ParameterFormManager._live_context_token_counter = saved_token

        for idx, (step_index, item, step, should_update_labels) in enumerate(step_items):
            # Reuse the step_after instance we already created
            step_after = step_after_instances[idx]

            # Format display text (this is what actually resolves through hierarchy)
            # Pass saved_context_snapshot to avoid re-collecting it for each step
            display_text = self._format_resolved_step_for_display(
                step_after,
                step,
                live_context_snapshot,
                saved_context_snapshot=saved_context_snapshot
            )

            # Reapply scope-based styling BEFORE flash (so flash color isn't overwritten)
            if should_update_labels:
                self._apply_step_item_styling(item)

            # Label update
            if should_update_labels:
                item.setText(display_text)
                item.setData(Qt.ItemDataRole.UserRole, step_index)
                item.setData(Qt.ItemDataRole.UserRole + 1, not step.enabled)
                item.setToolTip(self._create_step_tooltip(step))

                # CRITICAL: Reapply flash color if item is currently flashing
                # This prevents styling updates from killing an active flash animation
                from openhcs.pyqt_gui.widgets.shared.list_item_flash_animation import reapply_flash_if_active
                reapply_flash_if_active(self.step_list, step_index)

            # Collect steps that need to flash (but don't flash yet!)
            should_flash = should_flash_list[idx]
            if should_flash:
                steps_to_flash.append(step_index)

        # PHASE 2: Trigger ALL flashes at once (simultaneously, not sequentially)
        # This happens AFTER all formatting is done, so all flashes start at the same time
        if steps_to_flash:
            logger.info(f"✨ FLASHING {len(steps_to_flash)} steps simultaneously: {steps_to_flash}")
            for step_index in steps_to_flash:
                self._flash_step_item(step_index)

            # CRITICAL: Process events immediately to ensure flash is visible
            # This prevents the flash from being blocked by subsequent heavy work
            from PyQt6.QtWidgets import QApplication
            QApplication.processEvents()

        # CRITICAL: Update snapshot AFTER all flashes are shown
        # This ensures subsequent edits trigger flashes correctly
        # Only update if we have a new snapshot (not None)
        if live_context_snapshot is not None:
            self._last_live_context_snapshot = live_context_snapshot

    def _apply_step_item_styling(self, item: QListWidgetItem) -> None:
        """Apply scope-based background color and layered borders to step list item.

        Args:
            item: List item to style
        """
        from openhcs.pyqt_gui.widgets.shared.scope_color_utils import get_scope_color_scheme

        # Get step index from item data
        step_index = item.data(Qt.ItemDataRole.UserRole)
        if step_index is None or step_index < 0 or step_index >= len(self.pipeline_steps):
            return

        # Build scope_id for this step INCLUDING position for per-orchestrator indexing
        step = self.pipeline_steps[step_index]
        step_token = getattr(step, '_pipeline_scope_token', f'step_{step_index}')
        # Format: "plate_path::step_token@position" where position is the step's index in THIS pipeline
        scope_id = f"{self.current_plate}::{step_token}@{step_index}"

        # Get color scheme for this scope
        color_scheme = get_scope_color_scheme(scope_id)

        # Apply background color (None = transparent)
        bg_color = color_scheme.to_qcolor_step_item_bg()
        if bg_color is not None:
            item.setBackground(bg_color)
        else:
            # Clear background to make it transparent
            from PyQt6.QtGui import QBrush
            item.setBackground(QBrush())

        # Store border layers and base color in item data for delegate to use
        item.setData(Qt.ItemDataRole.UserRole + 3, color_scheme.step_border_layers)
        item.setData(Qt.ItemDataRole.UserRole + 4, color_scheme.base_color_rgb)

    def _flash_step_item(self, step_index: int) -> None:
        """Flash step list item to indicate update.

        Args:
            step_index: Index of step whose item should flash
        """
        from openhcs.pyqt_gui.widgets.shared.list_item_flash_animation import flash_list_item
        from openhcs.pyqt_gui.widgets.shared.scope_visual_config import ListItemType

        logger.debug(f"🔥 _flash_step_item called for step {step_index}")

        if 0 <= step_index < self.step_list.count():
            # Build scope_id for this step INCLUDING position for per-orchestrator indexing
            step = self.pipeline_steps[step_index]
            step_token = getattr(step, '_pipeline_scope_token', f'step_{step_index}')
            # Format: "plate_path::step_token@position" where position is the step's index in THIS pipeline
            scope_id = f"{self.current_plate}::{step_token}@{step_index}"

            logger.debug(f"🔥 Calling flash_list_item with scope_id={scope_id}")

            flash_list_item(
                self.step_list,
                step_index,
                scope_id,
                ListItemType.STEP
            )
        else:
            logger.warning(f"🔥 Cannot flash step {step_index}: out of range (count={self.step_list.count()})")

    def handle_cross_window_preview_change(
        self,
        field_path: str,
        new_value: Any,
        editing_object: Any,
        context_object: Any,
    ) -> None:
        """Handle cross-window preview change.

        Flash happens in _refresh_step_items_by_index after debouncing,
        so we delegate all logic to parent implementation.

        Args:
            field_path: Field path that changed
            new_value: New value
            editing_object: Object being edited
            context_object: Context object
        """
        logger.info(f"🔔 PipelineEditor.handle_cross_window_preview_change: field_path={field_path}, editing_object={type(editing_object).__name__ if editing_object else None}")
        # Call parent implementation (adds to pending updates, schedules debounced refresh with flash)
        super().handle_cross_window_preview_change(field_path, new_value, editing_object, context_object)

    # ========== UI Helper Methods ==========

    def update_step_list(self):
        """Update the step list widget using selection preservation mixin."""
        with timer("Pipeline editor: update_step_list()", threshold_ms=1.0):
            # If no orchestrator, show placeholder
            orchestrator = self._get_current_orchestrator()
            if not orchestrator:
                self.step_list.clear()
                placeholder_item = QListWidgetItem("No plate selected - select a plate to view pipeline")
                placeholder_item.setData(Qt.ItemDataRole.UserRole, None)
                self.step_list.addItem(placeholder_item)
                self.set_preview_scope_mapping({})
                self.update_button_states()
                return

            self._normalize_step_scope_tokens()

            # OPTIMIZATION: Collect live context ONCE for all steps (instead of 20+ times)
            from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
            with timer("  collect_live_context", threshold_ms=1.0):
                live_context_snapshot = ParameterFormManager.collect_live_context(scope_filter=self.current_plate)

            # DEBUG: Check what's in the live context snapshot
            if live_context_snapshot:
                logger.info(f"🔍 UPDATE_STEP_LIST: Live context token = {getattr(live_context_snapshot, 'token', None)}")
                scoped_values = getattr(live_context_snapshot, 'scoped_values', {})
                logger.info(f"🔍 UPDATE_STEP_LIST: Scoped values keys = {list(scoped_values.keys())}")
                for scope_id, scope_entries in scoped_values.items():
                    logger.info(f"🔍 UPDATE_STEP_LIST: Scope {scope_id} has types: {list(scope_entries.keys())}")
            else:
                logger.info(f"🔍 UPDATE_STEP_LIST: No live context snapshot")

            self.set_preview_scope_mapping(self._build_scope_index_map())

        def update_func():
            """Update function that updates existing items or rebuilds if structure changed."""
            # OPTIMIZATION: If list structure hasn't changed, just update text in place
            # This avoids expensive widget destruction/creation
            current_count = self.step_list.count()
            expected_count = len(self.pipeline_steps)

            if current_count == expected_count and current_count > 0:
                # Structure unchanged - just update text on existing items
                for step_index, step in enumerate(self.pipeline_steps):
                    item = self.step_list.item(step_index)
                    if item is None:
                        continue
                    display_text, _ = self.format_item_for_display(step, live_context_snapshot)

                    if item.text() != display_text:
                        item.setText(display_text)

                    item.setData(Qt.ItemDataRole.UserRole, step_index)
                    item.setData(Qt.ItemDataRole.UserRole + 1, not step.enabled)
                    item.setToolTip(self._create_step_tooltip(step))

                    # Reapply scope-based styling (in case colors changed)
                    self._apply_step_item_styling(item)
            else:
                # Structure changed - rebuild entire list
                # Clear flash animators before clearing list
                from openhcs.pyqt_gui.widgets.shared.list_item_flash_animation import clear_all_animators
                clear_all_animators(self.step_list)

                self.step_list.clear()

                for step_index, step in enumerate(self.pipeline_steps):
                    display_text, _ = self.format_item_for_display(step, live_context_snapshot)
                    item = QListWidgetItem(display_text)
                    item.setData(Qt.ItemDataRole.UserRole, step_index)
                    item.setData(Qt.ItemDataRole.UserRole + 1, not step.enabled)
                    item.setToolTip(self._create_step_tooltip(step))

                    # Apply scope-based styling
                    self._apply_step_item_styling(item)

                    self.step_list.addItem(item)

        # Use utility to preserve selection during update
        preserve_selection_during_update(
            self.step_list,
            lambda item_data: getattr(item_data, 'name', str(item_data)),
            lambda: bool(self.pipeline_steps),
            update_func
        )
        self.update_button_states()
    
    def get_selected_steps(self) -> List[FunctionStep]:
        """
        Get currently selected steps.

        Returns:
            List of selected FunctionStep objects
        """
        selected_items = []
        for item in self.step_list.selectedItems():
            step_index = item.data(Qt.ItemDataRole.UserRole)
            if step_index is not None and 0 <= step_index < len(self.pipeline_steps):
                selected_items.append(self.pipeline_steps[step_index])
        return selected_items
    
    def update_button_states(self):
        """Update button enabled/disabled states based on mathematical constraints (mirrors Textual TUI)."""
        has_plate = bool(self.current_plate)
        is_initialized = self._is_current_plate_initialized()
        has_steps = len(self.pipeline_steps) > 0
        has_selection = len(self.get_selected_steps()) > 0

        # Mathematical constraints (mirrors Textual TUI logic):
        # - Pipeline editing requires initialization
        # - Step operations require steps to exist
        # - Edit requires valid selection
        self.buttons["add_step"].setEnabled(has_plate and is_initialized)
        self.buttons["auto_load_pipeline"].setEnabled(has_plate and is_initialized)
        self.buttons["del_step"].setEnabled(has_steps)
        self.buttons["edit_step"].setEnabled(has_steps and has_selection)
        self.buttons["code_pipeline"].setEnabled(has_plate and is_initialized)  # Same as add button - orchestrator init is sufficient
    
    def update_status(self, message: str):
        """
        Update status label.
        
        Args:
            message: Status message to display
        """
        self.status_label.setText(message)
    
    def on_selection_changed(self):
        """Handle step list selection changes using utility."""
        def on_selected(selected_steps):
            self.selected_step = getattr(selected_steps[0], 'name', '')
            self.step_selected.emit(selected_steps[0])

        def on_cleared():
            self.selected_step = ""

        # Use utility to handle selection with prevention
        handle_selection_change_with_prevention(
            self.step_list,
            self.get_selected_steps,
            lambda item_data: getattr(item_data, 'name', str(item_data)),
            lambda: bool(self.pipeline_steps),
            lambda: self.selected_step,
            on_selected,
            on_cleared
        )

        self.update_button_states()

    def on_item_double_clicked(self, item: QListWidgetItem):
        """Handle double-click on step item."""
        step_index = item.data(Qt.ItemDataRole.UserRole)
        if step_index is not None and 0 <= step_index < len(self.pipeline_steps):
            # Double-click triggers edit
            self.action_edit_step()

    def on_steps_reordered(self, from_index: int, to_index: int):
        """
        Handle step reordering from drag and drop.

        Args:
            from_index: Original position of the moved step
            to_index: New position of the moved step
        """
        # Update the underlying pipeline_steps list to match the visual order
        current_steps = list(self.pipeline_steps)

        # Move the step in the data model
        step = current_steps.pop(from_index)
        current_steps.insert(to_index, step)

        # Update pipeline steps
        self.pipeline_steps = current_steps
        self._normalize_step_scope_tokens()

        # Emit pipeline changed signal to notify other components
        self.pipeline_changed.emit(self.pipeline_steps)

        # Refresh UI to update scope mapping and preview labels
        self.update_step_list()

        # Update status message
        step_name = getattr(step, 'name', 'Unknown Step')
        direction = "up" if to_index < from_index else "down"
        self.status_message.emit(f"Moved step '{step_name}' {direction}")



    def on_pipeline_changed(self, steps: List[FunctionStep]):
        """
        Handle pipeline changes.
        
        Args:
            steps: New pipeline steps
        """
        # Save pipeline to current plate if one is selected
        if self.current_plate:
            self.save_pipeline_for_plate(self.current_plate, steps)


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


    def _find_main_window(self):
        """Find the main window by traversing parent hierarchy."""
        widget = self
        while widget:
            if hasattr(widget, 'floating_windows'):
                return widget
            widget = widget.parent()
        return None

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

    def closeEvent(self, event):
        """Handle widget close event to disconnect signals and prevent memory leaks."""
        # Unregister from cross-window refresh signals
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        ParameterFormManager.unregister_external_listener(self)

        # Call parent closeEvent
        super().closeEvent(event)
