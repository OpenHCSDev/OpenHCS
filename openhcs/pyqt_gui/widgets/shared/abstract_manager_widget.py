"""
Abstract Manager Widget - Base class for item list managers.

Consolidates shared UI infrastructure and CRUD patterns from PlateManagerWidget
and PipelineEditorWidget.

Following OpenHCS ABC patterns:
- BaseFormDialog: Lightweight base, subclass controls initialization
- ParameterFormManager: Combined metaclass for PyQt6 compatibility
- Template Method Pattern: Base defines flow, subclasses implement hooks
"""

from abc import ABC, abstractmethod, ABCMeta
from typing import List, Tuple, Dict, Optional, Any, Callable, Iterable
import copy
import inspect
import logging
import os

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QListWidget,
    QListWidgetItem, QLabel, QSplitter, QSizePolicy
)
from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QFont

from openhcs.pyqt_gui.widgets.shared.reorderable_list_widget import ReorderableListWidget
from openhcs.pyqt_gui.widgets.shared.list_item_delegate import MultilinePreviewItemDelegate
from openhcs.pyqt_gui.widgets.mixins import (
    CrossWindowPreviewMixin,
    handle_selection_change_with_prevention,
)
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.config_framework import LiveContextResolver
from openhcs.config_framework.global_config import get_current_global_config
from openhcs.core.config import GlobalPipelineConfig

logger = logging.getLogger(__name__)


# Combined metaclass for ABC + PyQt6 QWidget (matches ParameterFormManager pattern)
class _CombinedMeta(ABCMeta, type(QWidget)):
    """Combined metaclass for ABC + PyQt6 QWidget."""
    pass


class AbstractManagerWidget(QWidget, CrossWindowPreviewMixin, ABC, metaclass=_CombinedMeta):
    """
    Abstract base class for item list manager widgets.

    Consolidates UI infrastructure and CRUD operations from PlateManagerWidget
    and PipelineEditorWidget using template method pattern.

    Subclasses MUST:
    1. Define TITLE, BUTTON_CONFIGS, PREVIEW_FIELD_CONFIGS, ACTION_REGISTRY class attributes
    2. Implement all abstract methods for item-specific behavior
    3. Call super().__init__(...) BEFORE subclass-specific state
    4. Call setup_ui() after subclass state is initialized

    Init Order (CRITICAL):
        1. Subclass-specific state initialization
        2. super().__init__(...) - creates base infrastructure (auto-processes PREVIEW_FIELD_CONFIGS)
        3. setup_ui() - create widgets
        4. setup_connections() - wire signals (optional, can be in base if simple)
    """

    # === Subclass MUST override these class attributes ===
    TITLE: str = "Manager"
    BUTTON_CONFIGS: List[Tuple[str, str, str]] = []  # [(label, action_id, tooltip), ...]
    BUTTON_GRID_COLUMNS: int = 4  # Number of columns in button grid (0 = single row with all buttons)
    ACTION_REGISTRY: Dict[str, str] = {}  # action_id -> method_name
    DYNAMIC_ACTIONS: Dict[str, str] = {}  # action_id -> resolver_method_name (for toggles)
    ITEM_NAME_SINGULAR: str = "item"
    ITEM_NAME_PLURAL: str = "items"

    # Declarative preview field configuration (processed automatically in __init__)
    # Format: List[Union[str, Tuple[str, Callable]]]
    #   - str: field name, uses CONFIG_INDICATORS from config_preview_formatters
    #   - Tuple[str, Callable]: (field_path, formatter_function)
    # Example:
    #   PREVIEW_FIELD_CONFIGS = [
    #       'napari_streaming_config',  # Uses CONFIG_INDICATORS['napari_streaming_config'] = 'NAP'
    #       ('num_workers', lambda v: f'W:{v if v is not None else 0}'),  # Custom formatter
    #   ]
    PREVIEW_FIELD_CONFIGS: List[Any] = []  # Override in subclasses

    # === Declarative Item Hooks (replaces trivial one-liner methods) ===
    # Subclass declares this dict instead of overriding 9 simple abstract methods.
    # ABC interprets these values to provide default implementations.
    #
    # Keys:
    #   'id_accessor': str | tuple - How to get item ID
    #       - str: dict key access, e.g., 'path' -> item['path']
    #       - ('attr', 'name'): getattr access -> getattr(item, 'name', '')
    #   'backing_attr': str - Attribute name for backing list, e.g., 'plates' -> self.plates
    #   'selection_attr': str - Attribute for current selection ID, e.g., 'selected_plate_path'
    #   'selection_signal': str - Signal to emit on selection change, e.g., 'plate_selected'
    #   'selection_emit_id': bool - True: emit ID, False: emit full item (default: True)
    #   'selection_clear_value': Any - Value to emit when selection cleared (default: '')
    #   'items_changed_signal': str | None - Signal to emit on items changed (default: None)
    #   'preserve_selection_pred': Callable[[self], bool] - Predicate for selection preservation
    #   'list_item_data': 'item' | 'index' - What to store in UserRole (default: 'item')
    #
    # Example (PlateManager):
    #   ITEM_HOOKS = {
    #       'id_accessor': 'path',
    #       'backing_attr': 'plates',
    #       'selection_attr': 'selected_plate_path',
    #       'selection_signal': 'plate_selected',
    #       'selection_emit_id': True,
    #       'selection_clear_value': '',
    #       'items_changed_signal': None,
    #       'preserve_selection_pred': lambda self: bool(self.orchestrators),
    #       'list_item_data': 'item',
    #   }
    ITEM_HOOKS: Dict[str, Any] = {}

    # Common signals
    status_message = pyqtSignal(str)

    def __init__(self, service_adapter, color_scheme=None, gui_config=None, parent=None):
        """
        Initialize base widget.

        Args:
            service_adapter: REQUIRED - provides async execution, dialogs, etc.
            color_scheme: Color scheme for styling (optional, uses service adapter if None)
            gui_config: GUI configuration (optional, for DualEditorWindow in PipelineEditor)
            parent: Parent widget

        Subclass __init__ MUST follow this pattern:
            # 1. Subclass-specific state (BEFORE super().__init__)
            self.pipeline_steps = []
            self.selected_step = ""
            # ...

            # 2. Initialize base class (auto-processes PREVIEW_FIELD_CONFIGS)
            super().__init__(service_adapter, color_scheme, gui_config, parent)

            # 3. Setup UI (AFTER subclass state is ready)
            self.setup_ui()
            self.setup_connections()  # Optional
            self.update_button_states()
        """
        super().__init__(parent)

        # Core dependencies (REQUIRED)
        self.service_adapter = service_adapter
        self.color_scheme = color_scheme or service_adapter.get_current_color_scheme()
        self.gui_config = gui_config or self._get_default_gui_config()
        self.style_generator = StyleSheetGenerator(self.color_scheme)  # Create internally
        self.event_bus = service_adapter.get_event_bus() if service_adapter else None

        # UI components (created in setup_ui)
        self.buttons: Dict[str, QPushButton] = {}
        self.status_label: Optional[QLabel] = None
        self.item_list: Optional[ReorderableListWidget] = None

        # Live context resolver for config attribute resolution
        self._live_context_resolver = LiveContextResolver()

        # Initialize CrossWindowPreviewMixin
        self._init_cross_window_preview_mixin()

        # Process declarative preview field configs (AFTER mixin init)
        self._process_preview_field_configs()

    def _get_default_gui_config(self):
        """Get default GUI config fallback."""
        from openhcs.pyqt_gui.config import get_default_pyqt_gui_config
        return get_default_pyqt_gui_config()

    def _process_preview_field_configs(self) -> None:
        """
        Process declarative PREVIEW_FIELD_CONFIGS and register preview fields.

        Called automatically in __init__ after CrossWindowPreviewMixin initialization.
        Supports two formats:
        - str: field name, uses CONFIG_INDICATORS from config_preview_formatters
        - Tuple[str, Callable]: (field_path, formatter_function)
        """
        for config in self.PREVIEW_FIELD_CONFIGS:
            if isinstance(config, str):
                # Simple field name - uses CONFIG_INDICATORS
                self.enable_preview_for_field(config)
            elif isinstance(config, tuple) and len(config) == 2:
                # (field_path, formatter) tuple
                field_path, formatter = config
                self.enable_preview_for_field(field_path, formatter)
            else:
                logger.warning(f"Invalid PREVIEW_FIELD_CONFIGS entry: {config}")

    # ========== UI Infrastructure (Concrete) ==========

    def setup_ui(self) -> None:
        """
        Create UI with QSplitter for resizable list/buttons layout.

        Uses VERTICAL orientation (list above buttons) to match current behavior.
        Subclass can override to add custom elements (e.g., PlateManager status scrolling).
        """
        main_layout = QVBoxLayout(self)
        main_layout.setContentsMargins(2, 2, 2, 2)
        main_layout.setSpacing(2)

        # Header (title + status)
        header = self._create_header()
        main_layout.addWidget(header)

        # QSplitter: list widget ABOVE buttons (VERTICAL orientation)
        splitter = QSplitter(Qt.Orientation.Vertical)

        # Top: item list
        self.item_list = self._create_list_widget()
        splitter.addWidget(self.item_list)

        # Bottom: button panel
        button_panel = self._create_button_panel()
        splitter.addWidget(button_panel)

        # Set initial sizes: list takes all space, buttons collapse to minimum height
        # Use large value for list and 1 for buttons to make buttons start at minimum size
        splitter.setSizes([1000, 1])

        # Set stretch factors: list expands, buttons stay at minimum
        splitter.setStretchFactor(0, 1)  # List widget expands
        splitter.setStretchFactor(1, 0)  # Button panel stays at minimum height

        main_layout.addWidget(splitter)

    def _create_header(self) -> QWidget:
        """
        Create header with title and status label.

        Subclass can override to add custom widgets (e.g., PlateManager's status scrolling).
        """
        header = QWidget()
        header_layout = QHBoxLayout(header)
        header_layout.setContentsMargins(5, 5, 5, 5)

        # Title label
        title_label = QLabel(self.TITLE)
        title_label.setFont(QFont("Arial", 12, QFont.Weight.Bold))
        title_label.setStyleSheet(
            f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};"
        )
        header_layout.addWidget(title_label)
        header_layout.addStretch()

        # Status label
        self.status_label = QLabel("Ready")
        self.status_label.setStyleSheet(
            f"color: {self.color_scheme.to_hex(self.color_scheme.status_success)}; "
            f"font-weight: bold;"
        )
        header_layout.addWidget(self.status_label)

        return header

    def _create_list_widget(self) -> ReorderableListWidget:
        """Create styled ReorderableListWidget with multiline delegate."""
        list_widget = ReorderableListWidget()
        list_widget.setStyleSheet(
            self.style_generator.generate_list_widget_style()
        )

        # Use multiline delegate for preview labels with colors from scheme
        cs = self.color_scheme
        delegate = MultilinePreviewItemDelegate(
            name_color=cs.to_qcolor(cs.text_primary),
            preview_color=cs.to_qcolor(cs.text_secondary),
            selected_text_color=cs.to_qcolor(cs.selection_text),
            parent=list_widget
        )
        list_widget.setItemDelegate(delegate)

        return list_widget

    def _create_button_panel(self) -> QWidget:
        """
        Create button panel from BUTTON_CONFIGS using grid layout.

        Uses BUTTON_GRID_COLUMNS to determine number of columns:
        - 0: Single row with all buttons (1 x N grid)
        - N: N columns, buttons wrap to next row
        """
        from PyQt6.QtWidgets import QGridLayout
        panel = QWidget()
        layout = QGridLayout(panel)
        layout.setContentsMargins(5, 5, 5, 5)
        layout.setSpacing(5)

        # Determine number of columns (0 means single row)
        num_cols = self.BUTTON_GRID_COLUMNS or len(self.BUTTON_CONFIGS)

        for i, (label, action_id, tooltip) in enumerate(self.BUTTON_CONFIGS):
            button = QPushButton(label)
            button.setToolTip(tooltip)
            button.setStyleSheet(self.style_generator.generate_button_style())
            button.clicked.connect(lambda checked, a=action_id: self.handle_button_action(a))
            self.buttons[action_id] = button

            row = i // num_cols
            col = i % num_cols
            layout.addWidget(button, row, col)

        return panel

    def _setup_connections(self) -> None:
        """
        Setup signal connections for list widget events.

        Subclass can override to add additional connections.
        """
        # Selection changes
        self.item_list.itemSelectionChanged.connect(self._on_selection_changed)

        # Double-click
        self.item_list.itemDoubleClicked.connect(self._on_item_double_clicked)

        # Reordering
        self.item_list.items_reordered.connect(self._on_items_reordered)

        # Status messages
        self.status_message.connect(self.update_status)

    # ========== Action Dispatch (Concrete) ==========

    def handle_button_action(self, action: str) -> None:
        """
        Dispatch button action using ACTION_REGISTRY or DYNAMIC_ACTIONS.

        DYNAMIC_ACTIONS allows for runtime action resolution (e.g., Run/Stop toggle).
        Supports both sync and async methods.

        Args:
            action: Action identifier from button click
        """
        # Check for dynamic action (like run/stop toggle)
        if action in self.DYNAMIC_ACTIONS:
            resolver_method_name = self.DYNAMIC_ACTIONS[action]
            resolved_action_name = getattr(self, resolver_method_name)()  # Call resolver
            action_func = getattr(self, resolved_action_name)
        elif action in self.ACTION_REGISTRY:
            method_name = self.ACTION_REGISTRY[action]
            action_func = getattr(self, method_name)
        else:
            logger.warning(f"Unknown action: {action}")
            return

        # Handle async methods
        if inspect.iscoroutinefunction(action_func):
            self.run_async_action(action_func)
        else:
            action_func()

    def run_async_action(self, async_func: Callable) -> None:
        """
        Execute async action via service adapter.

        Args:
            async_func: Async function to execute
        """
        self.service_adapter.execute_async_operation(async_func)

    # ========== CRUD Template Methods (Concrete) ==========

    def action_delete(self) -> None:
        """
        Template: Delete selected items.

        Flow: get items → validate → delete → update → emit → status
        """
        items = self.get_selected_items()
        if not items:
            self.service_adapter.show_error_dialog(f"No {self.ITEM_NAME_PLURAL} selected")
            return

        if self._validate_delete(items):
            self._perform_delete(items)
            self.update_item_list()
            self._emit_items_changed()
            self.status_message.emit(f"Deleted {len(items)} {self.ITEM_NAME_PLURAL}")

    def action_edit(self) -> None:
        """
        Template: Edit first selected item.

        Flow: get items → validate → show editor
        """
        items = self.get_selected_items()
        if not items:
            self.service_adapter.show_error_dialog(f"No {self.ITEM_NAME_SINGULAR} selected")
            return

        self._show_item_editor(items[0])

    def action_code(self) -> None:
        """
        Template: Open code editor.

        Validates before opening editor (allows subclass-specific guards).
        PlateManager overrides this entirely for multi-plate export.
        PipelineEditor uses this template with code editor hooks.

        Flow: validate → get code → get metadata → show editor
        """
        # Validate action (subclass can block with error dialog)
        if not self._validate_code_action():
            return

        code = self._get_code_content()
        if not code:
            self.service_adapter.show_error_dialog("No code to display")
            return

        title = self._get_code_editor_title()
        code_type = self._get_code_type()
        code_data = self._get_code_data()
        self._show_code_editor(code, title, self._handle_edited_code, code_type, code_data)

    # ========== Unified Helper Methods (Concrete) ==========

    def get_selected_items(self) -> List[Any]:
        """
        Get currently selected items.

        Delegates item extraction to subclass hook.
        """
        selected_items = []
        for list_item in self.item_list.selectedItems():
            item = self._get_item_from_list_item(list_item)
            if item is not None:
                selected_items.append(item)
        return selected_items

    def _resolve_config_attr(self, item: Any, config: object, attr_name: str,
                             live_context_snapshot=None) -> object:
        """
        Resolve any config attribute through lazy resolution system using LIVE context.

        Generic implementation that works for both:
        - PlateManager: 2-element stack [global, pipeline_config]
        - PipelineEditor: 3-element stack [global, pipeline_config, step]

        Args:
            item: Semantic item for context stack building
                  - PlateManager: orchestrator or plate dict
                  - PipelineEditor: FunctionStep
            config: Config dataclass instance (e.g., NapariStreamingConfig)
            attr_name: Name of the attribute to resolve (e.g., 'enabled', 'well_filter')
            live_context_snapshot: Optional pre-collected LiveContextSnapshot

        Returns:
            Resolved attribute value
        """
        try:
            # Subclass builds full context stack from semantic item
            context_stack = self._get_context_stack_for_resolution(item)

            resolved_value = self._live_context_resolver.resolve_config_attr(
                config_obj=config,
                attr_name=attr_name,
                context_stack=context_stack,
                live_context=live_context_snapshot.values if live_context_snapshot else {},
                cache_token=live_context_snapshot.token if live_context_snapshot else 0
            )
            return resolved_value
        except Exception as e:
            logger.warning(f"Failed to resolve config.{attr_name}: {e}")
            return object.__getattribute__(config, attr_name)

    def _merge_with_live_values(self, obj: Any, live_values: Dict[str, Any]) -> Any:
        """
        Merge object with live values from ParameterFormManager.

        Uses LiveContextResolver to reconstruct nested dataclass values.
        Generic implementation works for PipelineConfig, FunctionStep, etc.

        Args:
            obj: Dataclass instance to merge (PipelineConfig or FunctionStep)
            live_values: Dict of field_name -> value from ParameterFormManager

        Returns:
            New instance with live values merged
        """
        if not live_values:
            return obj

        try:
            obj_clone = copy.deepcopy(obj)
        except Exception:
            obj_clone = copy.copy(obj)

        reconstructed_values = self._live_context_resolver.reconstruct_live_values(live_values)
        for field_name, value in reconstructed_values.items():
            setattr(obj_clone, field_name, value)

        return obj_clone

    # ========== Code Editor Support (Concrete) ==========

    def _show_code_editor(self, code: str, title: str, callback: Callable,
                          code_type: str, code_data: Dict[str, Any]) -> None:
        """
        Launch code editor with external editor support.

        Honors OPENHCS_USE_EXTERNAL_EDITOR environment variable.

        Args:
            code: Initial code content
            title: Editor window title
            callback: Callback for edited code
            code_type: Code type identifier (e.g., "pipeline", "orchestrator")
            code_data: Additional metadata for editor
        """
        from openhcs.pyqt_gui.services.simple_code_editor import SimpleCodeEditorService

        editor_service = SimpleCodeEditorService(self)

        # Check if user wants external editor
        use_external = os.environ.get('OPENHCS_USE_EXTERNAL_EDITOR', '').lower() in ('1', 'true', 'yes')

        editor_service.edit_code(
            initial_content=code,
            title=title,
            callback=callback,
            use_external=use_external,
            code_type=code_type,
            code_data=code_data
        )

    # ========== Event Handlers (Concrete) ==========

    def _on_selection_changed(self) -> None:
        """
        Handle selection change with deselection prevention.

        Uses handle_selection_change_with_prevention to prevent clearing
        selection when items exist (current behavior).
        """
        def on_selected(items):
            self._handle_selection_changed(items)

        def on_cleared():
            self._handle_selection_cleared()

        handle_selection_change_with_prevention(
            self.item_list,
            self.get_selected_items,
            self._get_item_id,
            self._should_preserve_selection,
            self._get_current_selection_id,
            on_selected,
            on_cleared
        )

        self.update_button_states()

    def _on_item_double_clicked(self, list_item: QListWidgetItem) -> None:
        """
        Handle double-click. Calls overridable hook.

        Default routes to edit, subclass can override for custom behavior
        (e.g., PlateManager uses init-only pattern).
        """
        item = self._get_item_from_list_item(list_item)
        if item is not None:
            self._handle_item_double_click(item)

    def _on_items_reordered(self, from_index: int, to_index: int) -> None:
        """
        Handle item reordering from drag/drop.

        Emits status message to preserve user feedback from current behavior.
        Delegates actual data mutation to subclass hook.

        Args:
            from_index: Source index
            to_index: Destination index
        """
        # Get item before reordering (for status message)
        list_item = self.item_list.item(from_index)
        item = self._get_item_from_list_item(list_item)
        item_id = self._get_item_id(item) if item else "Unknown"

        # Delegate to subclass for data mutation
        self._handle_items_reordered(from_index, to_index)
        self._emit_items_changed()
        self.update_item_list()

        # Emit status message (matches current behavior)
        direction = "up" if to_index < from_index else "down"
        item_name = self.ITEM_NAME_SINGULAR
        self.status_message.emit(f"Moved {item_name} '{item_id}' {direction}")

    def update_status(self, message: str) -> None:
        """
        Update status label.

        Subclass can override for custom behavior (e.g., scrolling animation).
        """
        if self.status_label:
            self.status_label.setText(message)

    # ========== Code Editor Hooks (Concrete with defaults) ==========

    def _validate_code_action(self) -> bool:
        """
        Validate code action before opening editor.

        Default: Always allow (PlateManager overrides action_code entirely, doesn't use this)
        PipelineEditor: Check current_plate, show error if none selected

        Returns:
            True to proceed, False to abort (subclass shows error dialog)
        """
        return True  # Default: allow

    def _get_code_content(self) -> str:
        """
        Generate code string for editor.

        Default implementation (not abstract) - PlateManager overrides action_code entirely.

        PipelineEditor implementation:
            from openhcs.debug.pickle_to_python import generate_complete_pipeline_steps_code
            return generate_complete_pipeline_steps_code(
                pipeline_steps=list(self.pipeline_steps),
                clean_mode=True
            )

        PlateManager: Not called (overrides action_code entirely)
        """
        return ""  # Default: no code (subclass must override if using template)

    def _get_code_type(self) -> str:
        """
        Return code type identifier for editor metadata.

        Used by SimpleCodeEditorService for feature toggles.

        Examples:
            PipelineEditor: return "pipeline"
            PlateManager: Not called (overrides action_code entirely)
        """
        return "python"  # Default code type

    def _get_code_data(self) -> Dict[str, Any]:
        """
        Return additional metadata for code editor.

        Used for clean_mode toggle and regeneration parameters.

        PipelineEditor example:
            return {
                'clean_mode': True,
                'pipeline_steps': self.pipeline_steps
            }

        PlateManager: Not called (overrides action_code entirely)
        """
        return {}  # Default: no metadata

    def _get_code_editor_title(self) -> str:
        """
        Return title for code editor window.

        Examples:
            PipelineEditor: f"Pipeline Code: {orchestrator.plate_path}"
            PlateManager: Not called (overrides action_code entirely)
        """
        return "Code Editor"  # Default title

    def _handle_edited_code(self, code: str) -> None:
        """
        Template: Execute edited code and apply to widget state.

        Unified code execution flow:
        1. Pre-processing hook (PlateManager opens pipeline editor)
        2. Execute code with lazy constructor patching
        3. Migration fallback for old-format code (PipelineEditor)
        4. Apply extracted variables to state (hook)
        5. Post-processing: broadcast, trigger refresh

        Subclasses implement hooks:
        - _pre_code_execution() - Pre-processing (optional, default no-op)
        - _handle_code_execution_error(code, error, namespace) - Migration fallback (optional)
        - _apply_executed_code(namespace) -> bool - Extract and apply variables (REQUIRED)
        - _post_code_execution() - Post-processing (optional, default no-op)
        """
        code_type = self._get_code_type()
        logger.debug(f"{code_type} code edited, processing changes...")
        try:
            # Ensure we have a string
            if not isinstance(code, str):
                logger.error(f"Expected string, got {type(code)}: {code}")
                raise ValueError("Invalid code format received from editor")

            # Pre-processing hook
            self._pre_code_execution()

            # Execute code with lazy constructor patching
            namespace = {}
            try:
                with self._patch_lazy_constructors():
                    exec(code, namespace)
            except TypeError as e:
                # Migration fallback hook (returns new namespace or None to re-raise)
                migrated_namespace = self._handle_code_execution_error(code, e, namespace)
                if migrated_namespace is not None:
                    namespace = migrated_namespace
                else:
                    raise

            # Apply extracted variables to state (subclass hook)
            if not self._apply_executed_code(namespace):
                raise ValueError(self._get_code_missing_error_message())

            # Post-processing: broadcast, trigger refresh
            self._post_code_execution()

        except (SyntaxError, Exception) as e:
            import traceback
            full_traceback = traceback.format_exc()
            logger.error(f"Failed to parse edited {code_type} code: {e}\nFull traceback:\n{full_traceback}")
            # Re-raise so the code editor can handle it (keep dialog open, move cursor to error line)
            raise

    # === Code Execution Hooks (for _handle_edited_code template) ===

    def _pre_code_execution(self) -> None:
        """
        Pre-processing before code execution (optional hook).

        PlateManager: Open pipeline editor window
        PipelineEditor: No-op
        """
        pass  # Default: no-op

    def _handle_code_execution_error(self, code: str, error: Exception, namespace: dict) -> Optional[dict]:
        """
        Handle code execution error, optionally returning migrated namespace.

        Return new namespace dict to continue, or None to re-raise the error.

        PipelineEditor: Handle old-format step constructors (group_by/variable_components)
        PlateManager: Return None (no migration support)
        """
        return None  # Default: re-raise error

    def _apply_executed_code(self, namespace: dict) -> bool:
        """
        Apply executed code namespace to widget state.

        Extract expected variables from namespace and update internal state.
        Return True if successful, False if required variables missing.

        PipelineEditor: Extract 'pipeline_steps', update self.pipeline_steps
        PlateManager: Extract 'plate_paths', 'pipeline_data', etc.
        """
        logger.warning(f"{type(self).__name__}._apply_executed_code not implemented")
        return False  # Default: fail (subclass must override)

    def _get_code_missing_error_message(self) -> str:
        """
        Error message when expected code variables are missing.

        PipelineEditor: "No 'pipeline_steps = [...]' assignment found in edited code"
        PlateManager: "No valid assignments found in edited code"
        """
        return "No valid assignments found in edited code"

    def _post_code_execution(self) -> None:
        """
        Post-processing after successful code execution (optional hook).

        Both: Trigger cross-window refresh via ParameterFormManager
        PlateManager: Also emit pipeline_data_changed, etc.
        """
        # Default: trigger cross-window refresh (common to both)
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        ParameterFormManager.trigger_global_cross_window_refresh()

    # === Broadcast Utility ===

    def _broadcast_to_event_bus(self, event_type: str, data: Any) -> None:
        """
        Broadcast event to global event bus.

        Generic broadcast method that dispatches to event_bus.emit_{event_type}_changed().

        Args:
            event_type: Event type ('pipeline', 'config')
            data: Data to broadcast (pipeline_steps list, config object)

        Usage:
            self._broadcast_to_event_bus('pipeline', steps)
            self._broadcast_to_event_bus('config', config)
        """
        if self.event_bus:
            emit_method = getattr(self.event_bus, f'emit_{event_type}_changed', None)
            if emit_method:
                emit_method(data)
                logger.debug(f"Broadcasted {event_type}_changed to event bus")
            else:
                logger.warning(f"Event bus has no emit_{event_type}_changed method")

    def _handle_item_double_click(self, item: Any) -> None:
        """
        Default double-click behavior: Edit item.

        Subclass can override for custom logic (e.g., PlateManager init-only pattern).
        """
        self.action_edit()

    # ========== Utility Methods (Concrete) ==========

    def _find_main_window(self):
        """Find the main window by traversing parent hierarchy."""
        widget = self
        while widget:
            if hasattr(widget, 'floating_windows'):
                return widget
            widget = widget.parent()
        return None

    def _patch_lazy_constructors(self):
        """Context manager that patches lazy dataclass constructors to preserve None vs concrete distinction."""
        from openhcs.introspection import patch_lazy_constructors
        return patch_lazy_constructors()

    # ========== List Update Template ==========

    def update_item_list(self) -> None:
        """
        Template: Update the item list with in-place optimization.

        Flow:
        1. Check for placeholder condition → show placeholder if needed
        2. Pre-update hook (collect context, normalize state)
        3. Update with optimization: in-place text update if structure unchanged
        4. Post-update hook (auto-select first if needed)
        5. Update button states
        """
        from openhcs.pyqt_gui.widgets.mixins import preserve_selection_during_update

        # Check for placeholder
        placeholder = self._get_list_placeholder()
        if placeholder is not None:
            self.item_list.clear()
            text, data = placeholder
            placeholder_item = QListWidgetItem(text)
            placeholder_item.setData(Qt.ItemDataRole.UserRole, data)
            self.item_list.addItem(placeholder_item)
            self.update_button_states()
            return

        # Pre-update hook (collect live context, normalize state)
        update_context = self._pre_update_list()

        def update_func():
            """Update with in-place optimization when structure unchanged."""
            backing_items = self._get_backing_items()
            current_count = self.item_list.count()
            expected_count = len(backing_items)

            if current_count == expected_count and current_count > 0:
                # Structure unchanged - update text in place (optimization)
                for index, item_obj in enumerate(backing_items):
                    list_item = self.item_list.item(index)
                    if list_item is None:
                        continue

                    display_text = self._format_list_item(item_obj, index, update_context)
                    if list_item.text() != display_text:
                        list_item.setText(display_text)

                    list_item.setData(Qt.ItemDataRole.UserRole, self._get_list_item_data(item_obj, index))
                    list_item.setToolTip(self._get_list_item_tooltip(item_obj))

                    # Extra data (e.g., enabled flag)
                    for role_offset, value in self._get_list_item_extra_data(item_obj, index).items():
                        list_item.setData(Qt.ItemDataRole.UserRole + role_offset, value)
            else:
                # Structure changed - rebuild list
                self.item_list.clear()
                for index, item_obj in enumerate(backing_items):
                    display_text = self._format_list_item(item_obj, index, update_context)
                    list_item = QListWidgetItem(display_text)
                    list_item.setData(Qt.ItemDataRole.UserRole, self._get_list_item_data(item_obj, index))
                    list_item.setToolTip(self._get_list_item_tooltip(item_obj))

                    for role_offset, value in self._get_list_item_extra_data(item_obj, index).items():
                        list_item.setData(Qt.ItemDataRole.UserRole + role_offset, value)

                    self.item_list.addItem(list_item)

            # Post-update (e.g., auto-select first)
            self._post_update_list()

        # Preserve selection during update
        preserve_selection_during_update(
            self.item_list,
            self._get_item_id,
            self._should_preserve_selection,
            update_func
        )
        self.update_button_states()

    # ========== Abstract Methods (Subclass MUST implement) ==========

    @abstractmethod
    def action_add(self) -> None:
        """
        Add item(s). Subclass owns flow (directory chooser vs dialog).

        PlateManager: Directory chooser, multi-select, add_plate_callback
        PipelineEditor: Dialog with FunctionStep selection
        """
        ...

    @abstractmethod
    def update_button_states(self) -> None:
        """
        Enable/disable buttons based on current state.

        PlateManager: Based on selection and orchestrator state (init/compile/run)
        PipelineEditor: Based on selection and current_plate
        """
        ...

    # === CRUD Hooks (declarative via ITEM_HOOKS where possible) ===

    def _get_item_from_list_item(self, list_item: QListWidgetItem) -> Any:
        """Extract item from QListWidgetItem. Interprets ITEM_HOOKS['list_item_data']."""
        data = list_item.data(Qt.ItemDataRole.UserRole)
        if self.ITEM_HOOKS.get('list_item_data') == 'index':
            # Data is index, look up in backing list
            items = self._get_backing_items()
            return items[data] if data is not None and 0 <= data < len(items) else None
        # Data is the item itself
        return data

    def _validate_delete(self, items: List[Any]) -> bool:
        """Check if delete is allowed. Default: True. Override for restrictions."""
        return True

    @abstractmethod
    def _perform_delete(self, items: List[Any]) -> None:
        """
        Remove items from internal list.

        PlateManager: Remove from self.plates, cleanup orchestrators
        PipelineEditor: Remove from self.pipeline_steps, update orchestrator
        """
        ...

    @abstractmethod
    def _show_item_editor(self, item: Any) -> None:
        """
        Show editor for item.

        PlateManager: Open config window for plate orchestrator
        PipelineEditor: Open DualEditorWindow for step
        """
        ...

    # === UI Hooks (declarative via ITEM_HOOKS) ===

    def _get_item_id(self, item: Any) -> str:
        """Get unique ID for selection preservation. Interprets ITEM_HOOKS['id_accessor']."""
        accessor = self.ITEM_HOOKS.get('id_accessor', 'id')
        if isinstance(accessor, tuple) and accessor[0] == 'attr':
            return getattr(item, accessor[1], '')
        return item.get(accessor) if isinstance(item, dict) else getattr(item, accessor, '')

    def _should_preserve_selection(self) -> bool:
        """Predicate for selection preservation. Interprets ITEM_HOOKS['preserve_selection_pred']."""
        pred = self.ITEM_HOOKS.get('preserve_selection_pred')
        return pred(self) if pred else False

    @abstractmethod
    def format_item_for_display(self, item: Any, live_ctx=None) -> Tuple[str, str]:
        """
        Format item for display with preview.

        Returns:
            Tuple of (display_text, item_id_for_selection)

        PlateManager: return (multiline_text, plate['path'])
        PipelineEditor: return (display_text, step.name)
        """
        ...

    # === List Update Hooks (partially declarative via ITEM_HOOKS) ===

    def _get_backing_items(self) -> List[Any]:
        """Get backing list. Interprets ITEM_HOOKS['backing_attr']."""
        return getattr(self, self.ITEM_HOOKS['backing_attr'])

    @abstractmethod
    def _format_list_item(self, item: Any, index: int, context: Any) -> str:
        """Format item for list display. Subclass must implement."""
        ...

    def _get_list_item_data(self, item: Any, index: int) -> Any:
        """Get UserRole data. Interprets ITEM_HOOKS['list_item_data']."""
        strategy = self.ITEM_HOOKS.get('list_item_data', 'item')
        return index if strategy == 'index' else item

    @abstractmethod
    def _get_list_item_tooltip(self, item: Any) -> str:
        """
        Get tooltip for list item.

        PlateManager: return f"Status: {orchestrator.state.value}" or ""
        PipelineEditor: return self._create_step_tooltip(item)
        """
        ...

    def _get_list_item_extra_data(self, item: Any, index: int) -> Dict[int, Any]:
        """
        Get extra UserRole+N data for list item (optional).

        Returns dict mapping role_offset to value.

        PlateManager: return {} (no extra data)
        PipelineEditor: return {1: not step.enabled}
        """
        return {}  # Default: no extra data

    def _get_list_placeholder(self) -> Optional[Tuple[str, Any]]:
        """
        Get placeholder (text, data) when list should show placeholder.

        Return None if no placeholder needed.

        PlateManager: return None (no placeholder)
        PipelineEditor: return ("No plate selected...", None) if no orchestrator
        """
        return None  # Default: no placeholder

    def _pre_update_list(self) -> Any:
        """
        Pre-update hook: normalize state, collect context.

        Returns context object passed to _format_list_item.

        PlateManager: return None
        PipelineEditor: normalize scope tokens, collect live context, return snapshot
        """
        return None  # Default: no context

    def _post_update_list(self) -> None:
        """
        Post-update hook: auto-select first if needed.

        PlateManager: auto-select first plate if no selection
        PipelineEditor: no-op
        """
        pass  # Default: no-op

    # === Preview Field Resolution (shared by both widgets) ===

    def _resolve_preview_field_value(
        self,
        item: Any,
        config_source: Any,
        field_path: str,
        live_context_snapshot: Any = None,
        fallback_context: Optional[Dict[str, Any]] = None,
    ) -> Any:
        """
        Resolve a preview field path using the live context resolver.

        For dotted paths like 'path_planning_config.well_filter':
        1. Use getattr to navigate to the config object (preserves lazy type)
        2. Use _resolve_config_attr only for the final attribute (triggers MRO resolution)

        Args:
            item: Semantic item for context stack (orchestrator/plate dict or step)
            config_source: Root config object to resolve from (pipeline_config or step)
            field_path: Dot-separated field path (e.g., 'napari_streaming_config' or 'vfs_config.backend')
            live_context_snapshot: Optional live context for resolving lazy values
            fallback_context: Optional context dict for fallback resolver

        Returns:
            Resolved value or None
        """
        parts = field_path.split('.')

        if len(parts) == 1:
            # Simple field - resolve directly
            return self._resolve_config_attr(
                item,
                config_source,
                parts[0],
                live_context_snapshot
            )

        # Dotted path: navigate to parent config using getattr, then resolve final attr
        # This preserves the lazy type (e.g., LazyPathPlanningConfig) so MRO resolution works
        current_obj = config_source
        for part in parts[:-1]:
            if current_obj is None:
                return self._apply_preview_field_fallback(field_path, fallback_context)
            current_obj = getattr(current_obj, part, None)

        if current_obj is None:
            return self._apply_preview_field_fallback(field_path, fallback_context)

        # Resolve final attribute using live context resolver (triggers MRO inheritance)
        resolved_value = self._resolve_config_attr(
            item,
            current_obj,
            parts[-1],
            live_context_snapshot
        )

        if resolved_value is None:
            return self._apply_preview_field_fallback(field_path, fallback_context)

        return resolved_value

    # === Config Preview Building (shared by both widgets) ===

    def _build_preview_labels(
        self,
        item: Any,
        config_source: Any,
        live_context_snapshot: Any = None,
        fallback_context: Optional[Dict[str, Any]] = None,
    ) -> List[str]:
        """
        Build preview labels for all enabled preview fields.

        Unified logic that works for both PipelineEditor (step configs) and
        PlateManager (pipeline configs). Uses CrossWindowPreviewMixin's
        get_enabled_preview_fields() and format_preview_value().

        Args:
            item: Semantic item for context stack (orchestrator/plate dict or step)
            config_source: Config object to get preview fields from (pipeline_config or step)
            live_context_snapshot: Optional live context for resolving lazy values
            fallback_context: Optional context dict for fallback resolvers

        Returns:
            List of formatted preview labels (e.g., ["NAP", "W:4", "Seq:C,Z"])
        """
        from openhcs.pyqt_gui.widgets.config_preview_formatters import format_config_indicator

        labels = []

        for field_path in self.get_enabled_preview_fields():
            value = self._resolve_preview_field_value(
                item=item,
                config_source=config_source,
                field_path=field_path,
                live_context_snapshot=live_context_snapshot,
                fallback_context=fallback_context,
            )

            if value is None:
                continue

            # Check if value is a dataclass config object
            if hasattr(value, '__dataclass_fields__'):
                # Config object - use centralized formatter with resolver
                def resolve_attr(parent_obj, config_obj, attr_name, context,
                                 i=item, snapshot=live_context_snapshot):
                    return self._resolve_config_attr(i, config_obj, attr_name, snapshot)

                formatted = format_config_indicator(field_path, value, resolve_attr)
            else:
                # Simple value - use mixin's format_preview_value
                formatted = self.format_preview_value(field_path, value)

            if formatted:
                labels.append(formatted)

        return labels

    def _build_config_indicators(
        self,
        item: Any,
        config_source: Any,
        config_attrs: Iterable[str],
        live_context_snapshot: Any = None
    ) -> List[str]:
        """
        Build config indicator strings for display (direct attribute iteration).

        Alternative to _build_preview_labels() for cases where you want to iterate
        over specific config attributes rather than using get_enabled_preview_fields().

        Args:
            item: Semantic item for context stack (orchestrator or step)
            config_source: Object to get config attributes from (pipeline_config or step)
            config_attrs: Iterable of config attribute names to check
            live_context_snapshot: Optional live context for resolving lazy values

        Returns:
            List of formatted indicator strings (e.g., ["NAP", "FIJI", "MAT"])
        """
        from openhcs.pyqt_gui.widgets.config_preview_formatters import format_config_indicator

        indicators = []
        for config_attr in config_attrs:
            config = getattr(config_source, config_attr, None)
            if config is None:
                continue

            # Create resolver function that uses live context
            def resolve_attr(parent_obj, config_obj, attr_name, context,
                             i=item, snapshot=live_context_snapshot):
                return self._resolve_config_attr(i, config_obj, attr_name, snapshot)

            # Use centralized formatter (single source of truth)
            indicator_text = format_config_indicator(config_attr, config, resolve_attr)

            if indicator_text:
                indicators.append(indicator_text)

        return indicators

    @abstractmethod
    def _get_current_orchestrator(self):
        """
        Get orchestrator for current context.

        PlateManager: return self.orchestrators.get(self.selected_plate_path)
        PipelineEditor: return self._current_orchestrator (explicitly injected)
        """
        ...

    # REMOVED: _configure_preview_fields() - now uses declarative PREVIEW_FIELD_CONFIGS
    # Preview fields are configured automatically in __init__ via _process_preview_field_configs()

    # === Selection Hooks (declarative via ITEM_HOOKS) ===

    def _handle_selection_changed(self, items: List[Any]) -> None:
        """Handle selection change. Interprets ITEM_HOOKS for attr/signal."""
        item = items[0]
        item_id = self._get_item_id(item)
        setattr(self, self.ITEM_HOOKS['selection_attr'], item_id)
        signal = getattr(self, self.ITEM_HOOKS['selection_signal'])
        signal.emit(item_id if self.ITEM_HOOKS.get('selection_emit_id', True) else item)

    def _handle_selection_cleared(self) -> None:
        """Handle selection cleared. Interprets ITEM_HOOKS for attr/signal/clear_value."""
        setattr(self, self.ITEM_HOOKS['selection_attr'], '')
        signal = getattr(self, self.ITEM_HOOKS['selection_signal'])
        signal.emit(self.ITEM_HOOKS.get('selection_clear_value', ''))

    def _get_current_selection_id(self) -> str:
        """Get current selection ID. Interprets ITEM_HOOKS['selection_attr']."""
        return getattr(self, self.ITEM_HOOKS['selection_attr'])

    # === Reorder Hook (declarative base + optional post-hook) ===

    def _handle_items_reordered(self, from_index: int, to_index: int) -> None:
        """Reorder backing list and call _post_reorder() hook."""
        items = self._get_backing_items()
        item = items.pop(from_index)
        items.insert(to_index, item)
        self._post_reorder()

    def _post_reorder(self) -> None:
        """Post-reorder hook. Override for additional cleanup (e.g., normalize tokens)."""
        pass

    # === Items Changed Hook (declarative via ITEM_HOOKS) ===

    def _emit_items_changed(self) -> None:
        """Emit items changed signal. Interprets ITEM_HOOKS['items_changed_signal']."""
        signal_name = self.ITEM_HOOKS.get('items_changed_signal')
        if signal_name:
            signal = getattr(self, signal_name)
            signal.emit(self._get_backing_items())

    # === Config Resolution Hook (subclass must implement) ===

    @abstractmethod
    def _get_context_stack_for_resolution(self, item: Any) -> List[Any]:
        """Build context stack for config resolution. Subclass must implement."""
        ...

    # === CrossWindowPreviewMixin Hook (declarative default) ===

    def _handle_full_preview_refresh(self) -> None:
        """Full refresh of all previews. Default: update_item_list()."""
        self.update_item_list()
