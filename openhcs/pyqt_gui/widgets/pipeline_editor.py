"""
Pipeline Editor Widget for PyQt6

Pipeline step management with full feature parity to Textual TUI version.
Uses hybrid approach: extracted business logic + clean PyQt6 UI.
"""

import logging
import inspect
from typing import List, Dict, Optional, Callable, Tuple
from pathlib import Path

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QListWidget,
    QListWidgetItem, QLabel, QSplitter, QStyledItemDelegate, QStyle,
    QStyleOptionViewItem, QApplication
)
from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QFont, QPainter, QColor, QPen, QFontMetrics

from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.config import GlobalPipelineConfig
from openhcs.io.filemanager import FileManager
from openhcs.core.steps.function_step import FunctionStep
from openhcs.pyqt_gui.widgets.mixins import (
    preserve_selection_during_update,
    handle_selection_change_with_prevention
)
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.config import PyQtGUIConfig, get_default_pyqt_gui_config

logger = logging.getLogger(__name__)


class StepListItemDelegate(QStyledItemDelegate):
    """Custom delegate to render step name in white and preview text in grey without breaking hover/selection/borders."""
    def __init__(self, name_color: QColor, preview_color: QColor, selected_text_color: QColor, parent=None):
        super().__init__(parent)
        self.name_color = name_color
        self.preview_color = preview_color
        self.selected_text_color = selected_text_color

    def paint(self, painter: QPainter, option, index) -> None:
        # Prepare a copy to let style draw backgrounds, hover, selection, borders, etc.
        opt = QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)

        # Capture text and prevent default text draw
        text = opt.text or ""
        opt.text = ""

        painter.save()
        # Let the current style paint the item (background, selection, hover, separators)
        style = opt.widget.style() if opt.widget else QApplication.style()
        style.drawControl(QStyle.ControlElement.CE_ItemViewItem, opt, painter, opt.widget)

        # Check if item is selected
        is_selected = opt.state & QStyle.StateFlag.State_Selected

        # Check if step is disabled (stored in UserRole+1)
        is_disabled = index.data(Qt.ItemDataRole.UserRole + 1) or False

        # Now custom-draw the text with mixed colors
        rect = opt.rect.adjusted(6, 0, -6, 0)

        # Use strikethrough font for disabled steps
        font = QFont(opt.font)
        if is_disabled:
            font.setStrikeOut(True)
        painter.setFont(font)

        fm = QFontMetrics(font)
        baseline_y = rect.y() + (rect.height() + fm.ascent() - fm.descent()) // 2

        sep_idx = text.find("  (")
        if sep_idx != -1 and text.endswith(")"):
            name_part = text[:sep_idx]
            preview_part = text[sep_idx:]

            # Use white for both parts when selected, otherwise use normal colors
            if is_selected:
                painter.setPen(QPen(self.selected_text_color))
                painter.drawText(rect.x(), baseline_y, name_part)
                name_width = fm.horizontalAdvance(name_part)
                painter.drawText(rect.x() + name_width, baseline_y, preview_part)
            else:
                painter.setPen(QPen(self.name_color))
                painter.drawText(rect.x(), baseline_y, name_part)
                name_width = fm.horizontalAdvance(name_part)

                painter.setPen(QPen(self.preview_color))
                painter.drawText(rect.x() + name_width, baseline_y, preview_part)
        else:
            painter.setPen(QPen(self.selected_text_color if is_selected else self.name_color))
            painter.drawText(rect.x(), baseline_y, text)

        painter.restore()

class ReorderableListWidget(QListWidget):
    """
    Custom QListWidget that properly handles drag and drop reordering.
    Emits a signal when items are moved so the parent can update the data model.
    """

    items_reordered = pyqtSignal(int, int)  # from_index, to_index

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setDragDropMode(QListWidget.DragDropMode.InternalMove)

    def dropEvent(self, event):
        """Handle drop events and emit reorder signal."""
        # Get the item being dropped and its original position
        source_item = self.currentItem()
        if not source_item:
            super().dropEvent(event)
            return

        source_index = self.row(source_item)

        # Let the default drop behavior happen first
        super().dropEvent(event)

        # Find the new position of the item
        target_index = self.row(source_item)

        # Only emit signal if position actually changed
        if source_index != target_index:
            self.items_reordered.emit(source_index, target_index)


class PipelineEditorWidget(QWidget):
    """
    PyQt6 Pipeline Editor Widget.

    Manages pipeline steps with add, edit, delete, load, save functionality.
    Preserves all business logic from Textual version with clean PyQt6 UI.
    """

    # Config attribute name to display abbreviation mapping
    # Maps step config attribute names to their preview text indicators
    STEP_CONFIG_INDICATORS = {
        'step_materialization_config': 'MAT',
        'napari_streaming_config': 'NAP',
        'fiji_streaming_config': 'FIJI',
        'step_well_filter_config': 'FILT',
    }

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
        
        # Setup UI
        self.setup_ui()
        self.setup_connections()
        self.update_button_states()
        
        logger.debug("Pipeline editor widget initialized")

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
            }}
            QListWidget::item:selected {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.selection_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
            }}
            QListWidget::item:hover {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.hover_bg)};
            }}
        """)
        # Set custom delegate to render white name and grey preview
        try:
            name_color = QColor(self.color_scheme.to_hex(self.color_scheme.text_primary))
            preview_color = QColor(self.color_scheme.to_hex(self.color_scheme.text_disabled))
            selected_text_color = QColor("#FFFFFF")  # White text when selected
            self.step_list.setItemDelegate(StepListItemDelegate(name_color, preview_color, selected_text_color, self.step_list))
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

        # CRITICAL: Register as external listener for cross-window refresh signals
        # This makes preview labels reactive to live context changes
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        ParameterFormManager.register_external_listener(
            self,
            self._on_cross_window_context_changed,
            self._on_cross_window_context_refreshed
        )
    
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
    
    def format_item_for_display(self, step: FunctionStep) -> Tuple[str, str]:
        """
        Format step for display in the list with constructor value preview.

        Args:
            step: FunctionStep to format

        Returns:
            Tuple of (display_text, step_name)
        """
        step_name = getattr(step, 'name', 'Unknown Step')

        # Build preview of key constructor values
        preview_parts = []

        # Function preview
        func = getattr(step, 'func', None)
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
                group_by = getattr(step.processing_config, 'group_by', None) if hasattr(step, 'processing_config') else None

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
        var_components = getattr(step, 'variable_components', None)
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
        group_by = getattr(step, 'group_by', None)
        if group_by and group_by.value is not None:  # Check for GroupBy.NONE
            group_name = getattr(group_by, 'name', str(group_by))
            preview_parts.append(f"group_by={group_name}")

        # Input source preview (access from processing_config)
        input_source = getattr(step.processing_config, 'input_source', None) if hasattr(step, 'processing_config') else None
        if input_source:
            source_name = getattr(input_source, 'name', str(input_source))
            if source_name != 'PREVIOUS_STEP':  # Only show if not default
                preview_parts.append(f"input={source_name}")

        # Optional configurations preview - use lazy resolution system for enabled fields
        # CRITICAL: Must resolve through context hierarchy (Global -> Pipeline -> Step)
        # to match the same resolution that step editor placeholders use
        from openhcs.core.config import WellFilterConfig
        import dataclasses

        config_indicators = []
        for config_attr, indicator in self.STEP_CONFIG_INDICATORS.items():
            config = getattr(step, config_attr, None)
            if config is None:
                continue

            # Check if config has 'enabled' field via dataclass introspection
            has_enabled = dataclasses.is_dataclass(config) and 'enabled' in {f.name for f in dataclasses.fields(config)}

            if has_enabled:
                resolved_enabled = self._resolve_config_attr(step, config, 'enabled')
                if not resolved_enabled:
                    continue

            # Build indicator text with well_filter suffix if applicable
            indicator_text = indicator
            if isinstance(config, WellFilterConfig):
                resolved_well_filter = self._resolve_config_attr(step, config, 'well_filter')
                if resolved_well_filter is not None:
                    # Format well_filter for display
                    if isinstance(resolved_well_filter, list):
                        wf_display = str(len(resolved_well_filter))
                    elif isinstance(resolved_well_filter, int):
                        wf_display = str(resolved_well_filter)
                    else:
                        wf_display = str(resolved_well_filter)

                    # Add +/- prefix for INCLUDE/EXCLUDE mode
                    from openhcs.core.config import WellFilterMode
                    resolved_mode = self._resolve_config_attr(step, config, 'well_filter_mode')
                    mode_prefix = '-' if resolved_mode == WellFilterMode.EXCLUDE else '+'

                    indicator_text = f"{indicator}{mode_prefix}{wf_display}"

            config_indicators.append(indicator_text)

        if config_indicators:
            preview_parts.append(f"configs=[{','.join(config_indicators)}]")

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



        def handle_save(edited_step):
            """Handle step save from editor."""
            # Check if step already exists in pipeline (for Shift+Click saves)
            if edited_step not in self.pipeline_steps:
                self.pipeline_steps.append(edited_step)
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
                    self.pipeline_steps[i] = edited_step
                    break

            # Update the display
            self.update_step_list()
            self.pipeline_changed.emit(self.pipeline_steps)
            self.status_message.emit(f"Updated step: {edited_step.name}")

        # SIMPLIFIED: Orchestrator context is automatically available through type-based registry
        # No need for explicit context management - dual-axis resolver handles it automatically
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
        # This ensures the step editor's placeholders update when pipeline config is saved
        if self.plate_manager and hasattr(self.plate_manager, 'orchestrator_config_changed'):
            self.plate_manager.orchestrator_config_changed.connect(editor.on_orchestrator_config_changed)
            logger.debug("Connected orchestrator_config_changed signal to step editor")

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

            # Get the pipeline_steps from the namespace
            if 'pipeline_steps' in namespace:
                new_pipeline_steps = namespace['pipeline_steps']
                # Update the pipeline with new steps
                self.pipeline_steps = new_pipeline_steps
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
        logger.debug("Pipeline code edited, processing changes...")
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
                    logger.info(f"Detected old-format step constructor, retrying with migration patch: {e}")
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
        logger.debug(f"Saved pipeline for plate: {plate_path}")
    
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

        self.update_step_list()
        self.update_button_states()
        logger.debug(f"Current plate changed: {plate_path}")

    def _broadcast_to_event_bus(self, pipeline_steps: list):
        """Broadcast pipeline changed event to global event bus.

        Args:
            pipeline_steps: Updated list of FunctionStep objects
        """
        if self.event_bus:
            self.event_bus.emit_pipeline_changed(pipeline_steps)
            logger.debug(f"Broadcasted pipeline_changed to event bus ({len(pipeline_steps)} steps)")

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

    def _resolve_config_attr(self, step: FunctionStep, config: object, attr_name: str) -> object:
        """
        Resolve any config attribute through lazy resolution system using LIVE context.

        CRITICAL: Uses ParameterFormManager._collect_live_context_from_other_windows() mechanism
        to collect live values from all open windows, then builds context stack the same way
        step editor does for placeholder resolution.

        Args:
            step: FunctionStep containing the config
            config: Config dataclass instance (e.g., LazyNapariStreamingConfig)
            attr_name: Name of the attribute to resolve (e.g., 'enabled', 'well_filter')

        Returns:
            Resolved attribute value (type depends on attribute)
        """
        from openhcs.config_framework.context_manager import config_context
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        from openhcs.core.config import PipelineConfig, GlobalPipelineConfig
        from openhcs.config_framework.global_config import get_current_global_config
        import dataclasses

        orchestrator = self._get_current_orchestrator()
        if not orchestrator:
            # No orchestrator - return None to show placeholder instead of raising error
            return None

        try:
            # Collect live context DIRECTLY from all managers in this scope hierarchy
            # CRITICAL: We can't use manager._collect_live_context_from_other_windows() because
            # that skips managers of the same type, but we NEED the PipelineConfig manager's values!
            # CRITICAL: Use hierarchical scope matching - include child scopes like "plate::step"
            plate_scope = self.current_plate

            live_context_dict = {}
            step_scope = f"{plate_scope}::{step.name}"

            for manager in ParameterFormManager._active_form_managers:
                # Include managers from:
                # 1. Global scope (None)
                # 2. Exact plate scope match
                # 3. Exact step scope match (for THIS specific step)
                is_visible = (
                    manager.scope_id is None or  # Global scope
                    manager.scope_id == plate_scope or  # Exact plate match
                    manager.scope_id == step_scope  # Exact step match
                )

                if is_visible:
                    # CRITICAL: Get ALL current values (including None from resets), not just user-modified
                    # When user resets a field to None, it's removed from user_modified_values,
                    # but we need to see that None to properly resolve the preview label
                    live_values = manager.get_current_values()
                    obj_type = type(manager.object_instance)
                    live_context_dict[obj_type] = live_values

            # Build context stack: GlobalPipelineConfig → PipelineConfig → Step
            # Use live values if available, otherwise use stored values

            # Build context objects with live values merged in
            # Generic pattern: for each type in live_context_dict, merge live values into base object
            from types import SimpleNamespace

            context_objects = []

            # 1. GlobalPipelineConfig
            global_config = get_current_global_config(GlobalPipelineConfig)
            context_objects.append(self._merge_live_values(global_config, live_context_dict.get(GlobalPipelineConfig)))

            # 2. PipelineConfig
            pipeline_config = orchestrator.pipeline_config
            context_objects.append(self._merge_live_values(pipeline_config, live_context_dict.get(PipelineConfig)))

            # 3. Step (if a step editor is open for THIS specific step)
            # We matched by scope_id above, so if there's a FunctionStep in live_context_dict,
            # it's guaranteed to be for THIS step
            step_type = type(step)
            step_live_values = live_context_dict.get(step_type)

            step_to_use = step
            if step_live_values:
                step_to_use = self._merge_live_values(step, step_live_values)
                context_objects.append(step_to_use)
            else:
                context_objects.append(step)

            # CRITICAL: Get config from the merged step (step_to_use), not the original step!
            # This ensures we're resolving the config object that has live values merged in
            # Use introspection to find which attribute holds this config
            config_attr_name = None
            for step_attr in self.STEP_CONFIG_INDICATORS.keys():
                if getattr(step, step_attr, None) is config:
                    config_attr_name = step_attr
                    break

            if config_attr_name:
                config_to_resolve = getattr(step_to_use, config_attr_name, config)
            else:
                config_to_resolve = config

            # Build nested context stack and resolve
            def resolve_with_contexts(contexts, index=0):
                if index >= len(contexts):
                    return getattr(config_to_resolve, attr_name)
                with config_context(contexts[index]):
                    return resolve_with_contexts(contexts, index + 1)

            resolved_value = resolve_with_contexts(context_objects)
            return resolved_value

        except Exception as e:
            import traceback
            logger.warning(f"Failed to resolve config.{attr_name} for {type(config).__name__}: {e}")
            logger.warning(f"Traceback: {traceback.format_exc()}")
            # Fallback to raw value
            raw_value = object.__getattribute__(config, attr_name)
            return raw_value

    def _merge_live_values(self, base_obj: object, live_values: dict | None) -> object:
        """
        Generic helper to merge live values into a base object.

        Args:
            base_obj: Base object (dataclass or regular object)
            live_values: Live values dict from form manager (or None)

        Returns:
            New object with live values merged in (or original if no live values)
        """
        if not live_values:
            return base_obj

        # Reconstruct nested dataclasses
        live_values = self._reconstruct_nested_for_context(live_values, base_obj)

        # Merge into base object
        import dataclasses
        if dataclasses.is_dataclass(base_obj):
            return dataclasses.replace(base_obj, **live_values)
        else:
            from types import SimpleNamespace
            return SimpleNamespace(**{**vars(base_obj), **live_values})

    def _reconstruct_nested_for_context(self, live_values: dict, base_instance) -> dict:
        """Reconstruct nested dataclasses from (type, dict) tuples to instances.

        This is a simplified version of ParameterFormManager._reconstruct_nested_dataclasses()
        for use in pipeline editor context resolution.
        """
        import dataclasses
        from dataclasses import is_dataclass

        reconstructed = {}
        for field_name, value in live_values.items():
            if isinstance(value, tuple) and len(value) == 2:
                dataclass_type, field_dict = value
                if is_dataclass(dataclass_type):
                    # Merge into base instance's nested dataclass
                    if base_instance and hasattr(base_instance, field_name):
                        base_nested = getattr(base_instance, field_name)
                        if base_nested is not None and is_dataclass(base_nested):
                            reconstructed[field_name] = dataclasses.replace(base_nested, **field_dict)
                        else:
                            reconstructed[field_name] = dataclass_type(**field_dict)
                    else:
                        reconstructed[field_name] = dataclass_type(**field_dict)
                else:
                    reconstructed[field_name] = value
            else:
                reconstructed[field_name] = value
        return reconstructed

    def _on_cross_window_context_changed(self, field_path: str, new_value: object,
                                         editing_object: object, context_object: object):
        """Handle cross-window context changes to update preview labels.

        Reacts to any config change that could affect resolved values through the context hierarchy.
        """
        self.update_step_list()

    def _on_cross_window_context_refreshed(self, editing_object: object, context_object: object):
        """Handle cascading placeholder refreshes from upstream windows.

        Reacts to any context refresh that could affect resolved values.
        """
        self.update_step_list()
    
    # ========== UI Helper Methods ==========
    
    def update_step_list(self):
        """Update the step list widget using selection preservation mixin."""
        # If no orchestrator, show placeholder
        orchestrator = self._get_current_orchestrator()
        if not orchestrator:
            self.step_list.clear()
            placeholder_item = QListWidgetItem("No plate selected - select a plate to view pipeline")
            placeholder_item.setData(Qt.ItemDataRole.UserRole, None)
            self.step_list.addItem(placeholder_item)
            self.update_button_states()
            return

        def format_step_item(step, step_index):
            """Format step item for display."""
            display_text, step_name = self.format_item_for_display(step)
            return display_text, step_index  # Store index instead of step object

        def update_func():
            """Update function that clears and rebuilds the list."""
            self.step_list.clear()

            for step_index, step in enumerate(self.pipeline_steps):
                display_text, index_data = format_step_item(step, step_index)
                item = QListWidgetItem(display_text)
                item.setData(Qt.ItemDataRole.UserRole, index_data)  # Store index, not step
                item.setData(Qt.ItemDataRole.UserRole + 1, not step.enabled)  # Store disabled status for strikethrough
                item.setToolTip(self._create_step_tooltip(step))
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

        # Emit pipeline changed signal to notify other components
        self.pipeline_changed.emit(self.pipeline_steps)

        # Update status message
        step_name = getattr(step, 'name', 'Unknown Step')
        direction = "up" if to_index < from_index else "down"
        self.status_message.emit(f"Moved step '{step_name}' {direction}")

        logger.debug(f"Reordered step '{step_name}' from index {from_index} to {to_index}")

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
            logger.info("Refreshed pipeline config placeholders after global config change")

    def closeEvent(self, event):
        """Handle widget close event to disconnect signals and prevent memory leaks."""
        # Unregister from cross-window refresh signals
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        ParameterFormManager.unregister_external_listener(self)
        logger.debug("Pipeline editor: Unregistered from cross-window refresh signals")

        # Call parent closeEvent
        super().closeEvent(event)


