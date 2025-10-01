"""
Pipeline Editor Widget for PyQt6

Pipeline step management with full feature parity to Textual TUI version.
Uses hybrid approach: extracted business logic + clean PyQt6 UI.
"""

import logging
import asyncio
import inspect
import contextlib
from typing import List, Dict, Optional, Callable, Tuple
from pathlib import Path

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QListWidget,
    QListWidgetItem, QLabel, QMessageBox, QFileDialog, QFrame,
    QSplitter, QTextEdit, QScrollArea, QStyledItemDelegate, QStyle,
    QStyleOptionViewItem, QApplication
)
from PyQt6.QtCore import Qt, pyqtSignal, QMimeData
from PyQt6.QtGui import QFont, QDrag, QPainter, QColor, QPen, QFontMetrics

from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.config import GlobalPipelineConfig
from openhcs.config_framework.global_config import set_current_global_config, get_current_global_config
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
    def __init__(self, name_color: QColor, preview_color: QColor, parent=None):
        super().__init__(parent)
        self.name_color = name_color
        self.preview_color = preview_color

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

        # Now custom-draw the text with mixed colors
        rect = opt.rect.adjusted(6, 0, -6, 0)
        painter.setFont(opt.font)
        fm = QFontMetrics(opt.font)
        baseline_y = rect.y() + (rect.height() + fm.ascent() - fm.descent()) // 2

        sep_idx = text.find("  (")
        if sep_idx != -1 and text.endswith(")"):
            name_part = text[:sep_idx]
            preview_part = text[sep_idx:]

            painter.setPen(QPen(self.name_color))
            painter.drawText(rect.x(), baseline_y, name_part)
            name_width = fm.horizontalAdvance(name_part)

            painter.setPen(QPen(self.preview_color))
            painter.drawText(rect.x() + name_width, baseline_y, preview_part)
        else:
            painter.setPen(QPen(self.name_color))
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
        
        # Title
        title_label = QLabel("Pipeline Editor")
        title_label.setFont(QFont("Arial", 12, QFont.Weight.Bold))
        title_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)}; padding: 5px;")
        layout.addWidget(title_label)
        
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
            }}
            QListWidget::item:hover {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.hover_bg)};
            }}
        """)
        # Set custom delegate to render white name and grey preview
        try:
            name_color = QColor(self.color_scheme.to_hex(self.color_scheme.text_primary))
            preview_color = QColor(self.color_scheme.to_hex(self.color_scheme.text_disabled))
            self.step_list.setItemDelegate(StepListItemDelegate(name_color, preview_color, self.step_list))
        except Exception:
            # Fallback silently if color scheme isn't ready
            pass
        splitter.addWidget(self.step_list)
        
        # Button panel
        button_panel = self.create_button_panel()
        splitter.addWidget(button_panel)
        
        # Status section
        status_frame = self.create_status_section()
        layout.addWidget(status_frame)
        
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
            ("Load", "load_pipeline", "Load pipeline from file"),
            ("Save", "save_pipeline", "Save pipeline to file"),
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
    
    def create_status_section(self) -> QWidget:
        """
        Create the status section.
        
        Returns:
            Widget containing status information
        """
        frame = QWidget()
        frame.setStyleSheet(f"""
            QWidget {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.window_bg)};
                border: none;
                padding: 2px;
            }}
        """)

        layout = QVBoxLayout(frame)
        layout.setContentsMargins(2, 2, 2, 2)
        layout.setSpacing(2)
        
        # Status label
        self.status_label = QLabel("Ready")
        self.status_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.status_success)}; font-weight: bold;")
        layout.addWidget(self.status_label)
        
        return frame
    
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
            "load_pipeline": self.action_load_pipeline,
            "save_pipeline": self.action_save_pipeline,
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
                if len(func) == 1:
                    func_name = getattr(func[0], '__name__', str(func[0]))
                    preview_parts.append(f"func={func_name}")
                else:
                    preview_parts.append(f"func=[{len(func)} functions]")
            elif callable(func):
                func_name = getattr(func, '__name__', str(func))
                preview_parts.append(f"func={func_name}")
            elif isinstance(func, dict):
                preview_parts.append(f"func={{dict with {len(func)} keys}}")

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

        # Input source preview
        input_source = getattr(step, 'input_source', None)
        if input_source:
            source_name = getattr(input_source, 'name', str(input_source))
            if source_name != 'PREVIOUS_STEP':  # Only show if not default
                preview_parts.append(f"input={source_name}")

        # Optional configurations preview
        config_indicators = []
        if hasattr(step, 'step_materialization_config') and step.step_materialization_config:
            config_indicators.append("MAT")
        if hasattr(step, 'napari_streaming_config') and step.napari_streaming_config:
            config_indicators.append("NAP")
        if hasattr(step, 'fiji_streaming_config') and step.fiji_streaming_config:
            config_indicators.append("FIJI")
        if hasattr(step, 'step_well_filter_config') and step.step_well_filter_config:
            config_indicators.append("FILT")

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

        # Input source
        input_source = getattr(step, 'input_source', None)
        if input_source:
            source_name = getattr(input_source, 'name', str(input_source))
            tooltip_lines.append(f"Input Source: {source_name}")
        else:
            tooltip_lines.append("Input Source: None")

        # Additional configurations with details
        config_details = []
        if hasattr(step, 'step_materialization_config') and step.step_materialization_config:
            config_details.append("• Materialization Config: Enabled")
        if hasattr(step, 'napari_streaming_config') and step.napari_streaming_config:
            napari_config = step.napari_streaming_config
            port = getattr(napari_config, 'napari_port', 'default')
            config_details.append(f"• Napari Streaming: Port {port}")
        if hasattr(step, 'fiji_streaming_config') and step.fiji_streaming_config:
            config_details.append("• Fiji Streaming: Enabled")
        if hasattr(step, 'step_well_filter_config') and step.step_well_filter_config:
            well_config = step.step_well_filter_config
            well_filter = getattr(well_config, 'well_filter', 'default')
            config_details.append(f"• Well Filter: {well_filter}")

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
            self.pipeline_steps.append(edited_step)
            self.update_step_list()
            self.pipeline_changed.emit(self.pipeline_steps)
            self.status_message.emit(f"Added new step: {edited_step.name}")

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
        editor.show()
        editor.raise_()
        editor.activateWindow()
    
    def action_delete_step(self):
        """Handle Delete Step button (extracted from Textual version)."""
        selected_items = self.get_selected_steps()
        if not selected_items:
            self.service_adapter.show_error_dialog("No steps selected to delete.")
            return
        
        # Remove selected steps
        steps_to_remove = set(getattr(item, 'name', '') for item in selected_items)
        new_steps = [step for step in self.pipeline_steps if getattr(step, 'name', '') not in steps_to_remove]
        
        self.pipeline_steps = new_steps
        self.update_step_list()
        self.pipeline_changed.emit(self.pipeline_steps)
        
        deleted_count = len(selected_items)
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
        editor.show()
        editor.raise_()
        editor.activateWindow()
    
    def action_load_pipeline(self):
        """Handle Load Pipeline button (adapted from Textual version)."""

        from openhcs.core.path_cache import PathCacheKey

        # Use cached file dialog (mirrors Textual TUI pattern)
        file_path = self.service_adapter.show_cached_file_dialog(
            cache_key=PathCacheKey.PIPELINE_FILES,
            title="Load Pipeline",
            file_filter="Pipeline Files (*.pipeline);;All Files (*)",
            mode="open"
        )

        if file_path:
            self.load_pipeline_from_file(file_path)
    
    def action_save_pipeline(self):
        """Handle Save Pipeline button (adapted from Textual version)."""
        if not self.pipeline_steps:
            self.service_adapter.show_error_dialog("No pipeline steps to save.")
            return

        from openhcs.core.path_cache import PathCacheKey

        # Use cached file dialog (mirrors Textual TUI pattern)
        file_path = self.service_adapter.show_cached_file_dialog(
            cache_key=PathCacheKey.PIPELINE_FILES,
            title="Save Pipeline",
            file_filter="Pipeline Files (*.pipeline);;All Files (*)",
            mode="save"
        )

        if file_path:
            self.save_pipeline_to_file(file_path)
    
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

            # Launch editor with callback
            editor_service.edit_code(
                initial_content=python_code,
                title="Edit Pipeline Steps",
                callback=self._handle_edited_pipeline_code,
                use_external=use_external
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
                self.service_adapter.show_error_dialog("Invalid code format received from editor")
                return

            # CRITICAL FIX: Execute code with lazy dataclass constructor patching to preserve None vs concrete distinction
            namespace = {}
            with self._patch_lazy_constructors():
                exec(edited_code, namespace)

            # Get the pipeline_steps from the namespace
            if 'pipeline_steps' in namespace:
                new_pipeline_steps = namespace['pipeline_steps']
                # Update the pipeline with new steps
                self.pipeline_steps = new_pipeline_steps
                self.update_step_list()
                self.pipeline_changed.emit(self.pipeline_steps)
                self.status_message.emit(f"Pipeline updated with {len(new_pipeline_steps)} steps")
            else:
                self.service_adapter.show_error_dialog("No 'pipeline_steps = [...]' assignment found in edited code")

        except SyntaxError as e:
            self.service_adapter.show_error_dialog(f"Invalid Python syntax: {e}")
        except Exception as e:
            logger.error(f"Failed to parse edited pipeline code: {e}")
            self.service_adapter.show_error_dialog(f"Failed to parse pipeline code: {str(e)}")

    def _patch_lazy_constructors(self):
        """Context manager that patches lazy dataclass constructors to preserve None vs concrete distinction."""
        from contextlib import contextmanager
        from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
        import dataclasses

        @contextmanager
        def patch_context():
            # Store original constructors
            original_constructors = {}

            # Find all lazy dataclass types that need patching
            from openhcs.core.config import LazyZarrConfig, LazyStepMaterializationConfig, LazyWellFilterConfig
            lazy_types = [LazyZarrConfig, LazyStepMaterializationConfig, LazyWellFilterConfig]

            # Add any other lazy types that might be used
            for lazy_type in lazy_types:
                if LazyDefaultPlaceholderService.has_lazy_resolution(lazy_type):
                    # Store original constructor
                    original_constructors[lazy_type] = lazy_type.__init__

                    # Create patched constructor that uses raw values
                    def create_patched_init(original_init, dataclass_type):
                        def patched_init(self, **kwargs):
                            # Use raw value approach instead of calling original constructor
                            # This prevents lazy resolution during code execution
                            for field in dataclasses.fields(dataclass_type):
                                value = kwargs.get(field.name, None)
                                object.__setattr__(self, field.name, value)

                            # Initialize any required lazy dataclass attributes
                            if hasattr(dataclass_type, '_is_lazy_dataclass'):
                                object.__setattr__(self, '_is_lazy_dataclass', True)

                        return patched_init

                    # Apply the patch
                    lazy_type.__init__ = create_patched_init(original_constructors[lazy_type], lazy_type)

            try:
                yield
            finally:
                # Restore original constructors
                for lazy_type, original_init in original_constructors.items():
                    lazy_type.__init__ = original_init

        return patch_context()

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
    
    # ========== UI Helper Methods ==========
    
    def update_step_list(self):
        """Update the step list widget using selection preservation mixin."""
        def format_step_item(step):
            """Format step item for display."""
            display_text, step_name = self.format_item_for_display(step)
            return display_text, step

        def update_func():
            """Update function that clears and rebuilds the list."""
            self.step_list.clear()

            for step in self.pipeline_steps:
                display_text, step_data = format_step_item(step)
                item = QListWidgetItem(display_text)
                item.setData(Qt.ItemDataRole.UserRole, step_data)
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
            step_data = item.data(Qt.ItemDataRole.UserRole)
            if step_data:
                selected_items.append(step_data)
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
        self.buttons["load_pipeline"].setEnabled(has_plate and is_initialized)
        self.buttons["del_step"].setEnabled(has_steps)
        self.buttons["edit_step"].setEnabled(has_steps and has_selection)
        self.buttons["save_pipeline"].setEnabled(has_steps)
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
        step_data = item.data(Qt.ItemDataRole.UserRole)
        if step_data:
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
            self.form_manager._refresh_all_placeholders()
            logger.info("Refreshed pipeline config placeholders after global config change")


