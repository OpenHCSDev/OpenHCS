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
from dataclasses import dataclass, field, is_dataclass
from typing import List, Tuple, Dict, Optional, Any, Callable, Iterable, Union, TYPE_CHECKING
import copy
import inspect
import logging
import os

if TYPE_CHECKING:
    from objectstate import ObjectState

# Type alias for formatters: either a method name string or a callable
FieldFormatter = Union[str, Callable[[Any], Optional[str]]]


@dataclass(frozen=True)
class ListItemFormat:
    """
    Type-safe declarative configuration for list item display format.

    Replaces Dict-based LIST_ITEM_FORMAT with a proper dataclass.

    Attributes:
        first_line: Field paths shown after item name on first line (e.g., ('func',))
        preview_line: Field paths shown on the └─ preview line
        detail_line_field: Field path for detail line (e.g., 'path')
        show_config_indicators: Whether to show NAP/FIJI/MAT from PREVIEW_FIELD_CONFIGS
        formatters: Dict mapping field path to formatter (method name str or callable)

    Field abbreviations are declared on config classes via @global_pipeline_config(field_abbreviations=...)
    and looked up from FIELD_ABBREVIATIONS_REGISTRY. This keeps abbreviations with the config, not the widget.

    Formatters receive the field value and return a label string (or None to skip).
    Method name strings are resolved on the widget instance at runtime.

    Example:
        LIST_ITEM_FORMAT = ListItemFormat(
            first_line=('func',),
            preview_line=('processing_config.variable_components', 'processing_config.group_by'),
            formatters={
                'func': '_format_func_preview',
                'processing_config.group_by': lambda v: f"group_by={v.name}" if v else None,
            },
        )
    """
    first_line: Tuple[str, ...] = ()
    preview_line: Tuple[str, ...] = ()
    detail_line_field: Optional[str] = None
    show_config_indicators: bool = True
    formatters: Dict[str, FieldFormatter] = field(default_factory=dict)

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton,
    QListWidgetItem, QLabel, QSplitter, QScrollArea, QSizePolicy
)
from PyQt6.QtCore import Qt, QRect, pyqtSignal, QTimer
from PyQt6.QtGui import QFont, QColor, QBrush

from pyqt_formgen.core import ReorderableListWidget
from pyqt_formgen.widgets.shared.list_item_delegate import (
    MultilinePreviewItemDelegate,
    LAYOUT_ROLE,
    DIRTY_FIELDS_ROLE,
    SIG_DIFF_FIELDS_ROLE,
    Segment,
    StyledText,
    StyledTextLayout,
)
# Backwards compat alias
SEGMENTS_ROLE = LAYOUT_ROLE
from objectstate import ObjectStateRegistry
from pyqt_formgen.widgets.mixins import (
    CrossWindowPreviewMixin,
    handle_selection_change_with_prevention,
)
from pyqt_formgen.theming import StyleSheetGenerator
from objectstate import LiveContextResolver
from pyqt_formgen.animation import FlashMixin, get_flash_color, WindowFlashOverlay
from pyqt_formgen.widgets.shared.scope_visual_config import ListItemType

logger = logging.getLogger(__name__)


# Combined metaclass for ABC + PyQt6 QWidget (matches ParameterFormManager pattern)
class _CombinedMeta(ABCMeta, type(QWidget)):
    """Combined metaclass for ABC + PyQt6 QWidget."""
    pass


class AbstractManagerWidget(QWidget, CrossWindowPreviewMixin, FlashMixin, ABC, metaclass=_CombinedMeta):
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
    #   - str: field name - label auto-discovered from PREVIEW_LABEL_REGISTRY
    #         (set via @global_pipeline_config(preview_label='NAP'))
    #   - Tuple[str, Callable]: (field_path, formatter_function) for custom formatting
    # Example:
    #   PREVIEW_FIELD_CONFIGS = [
    #       'napari_streaming_config',   # Auto: preview_label='NAP' from decorator
    #       ('num_workers', lambda v: f'W:{v if v is not None else 0}'),  # Custom formatter
    #   ]
    PREVIEW_FIELD_CONFIGS: List[Any] = []  # Override in subclasses

    # === Declarative List Item Format Config ===
    # Type-safe configuration for list item display. See ListItemFormat dataclass.
    # Override in subclasses with ListItemFormat(...) instance.
    LIST_ITEM_FORMAT: Optional[ListItemFormat] = None

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

    # Custom data role for scope border color (kept local to avoid delegate coupling)
    SCOPE_BORDER_ROLE = Qt.ItemDataRole.UserRole + 10

    # Status scrolling: enable marquee animation for long status messages
    ENABLE_STATUS_SCROLLING: bool = False

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

        # Status scrolling state (only used when ENABLE_STATUS_SCROLLING = True)
        self._status_scroll: Optional[QWidget] = None  # QScrollArea when scrolling enabled
        self._status_scroll_timer: Optional[Any] = None  # QTimer for animation
        self._status_scroll_position: int = 0
        self._status_single_message_width: int = 0
        self._current_status_message: str = "Ready"

        # Live context resolver for config attribute resolution
        self._live_context_resolver = LiveContextResolver()

        # Flash animation state: {scope_id: (ObjectState, callback)}
        self._flash_subscriptions: Dict[str, tuple] = {}
        # Dirty state subscriptions: {scope_id: (ObjectState, callback)}
        # Enables reactive dirty markers without polling
        self._dirty_subscriptions: Dict[str, tuple] = {}
        # Time-travel limbo: backing items saved during unregister for re-registration
        self._time_travel_limbo_items: Dict[str, Any] = {}
        # Scope to list item mapping for WindowFlashOverlay rect lookup
        self._scope_to_list_item: Dict[str, QListWidgetItem] = {}
        # Per-update-cycle scope cache: item_id -> scope_id (cleared at start of each update)
        self._item_scope_cache: Dict[int, str] = {}
        self._init_visual_update_mixin()  # Initialize VisualUpdateMixin state

        # Initialize CrossWindowPreviewMixin for preview field configuration API
        # (We override _on_live_context_changed to use unified batching)
        self._init_cross_window_preview_mixin()

        # Process declarative preview field configs (AFTER mixin init)
        self._process_preview_field_configs()

    def _get_default_gui_config(self):
        """Get default GUI config fallback."""
        from pyqt_formgen.protocols import get_form_config
        return get_form_config()

    def _process_preview_field_configs(self) -> None:
        """
        Process declarative PREVIEW_FIELD_CONFIGS and register preview fields.

        Called automatically in __init__ after CrossWindowPreviewMixin initialization.
        Supports two formats:
        - str: field name (auto-discovers preview_label from registry)
        - Tuple[str, Callable]: (field_path, formatter_function)
        """
        for config in self.PREVIEW_FIELD_CONFIGS:
            if isinstance(config, str):
                # Simple field name - auto-discovers from registry
                self.enable_preview_for_field(config)
            elif isinstance(config, tuple) and len(config) == 2:
                # (field_path, formatter) tuple
                field_path, formatter = config
                self.enable_preview_for_field(field_path, formatter)
            else:
                logger.warning(f"Invalid PREVIEW_FIELD_CONFIGS entry: {config}")

    def _discover_preview_fields_from_registry(self, config_source: Any) -> List[str]:
        """
        Auto-discover preview fields from PREVIEW_LABEL_REGISTRY.

        Scans config_source's dataclass fields and returns field names
        whose types are registered in PREVIEW_LABEL_REGISTRY.

        Args:
            config_source: Dataclass instance to scan for registered preview types

        Returns:
            List of field names whose types have preview labels registered
        """
        from dataclasses import fields, is_dataclass
        from typing import get_origin, get_args, Union
        from objectstate.lazy_factory import PREVIEW_LABEL_REGISTRY

        if not is_dataclass(config_source):
            return []

        discovered = []
        for f in fields(config_source):
            field_type = f.type

            # Unwrap Optional[T] -> T
            if get_origin(field_type) is Union:
                args = get_args(field_type)
                field_type = next((t for t in args if t is not type(None)), field_type)

            # Check if type is in registry
            if field_type in PREVIEW_LABEL_REGISTRY:
                discovered.append(f.name)
                continue

            # Check base classes (for lazy wrapper types)
            if isinstance(field_type, type):
                for base in field_type.__mro__[1:]:
                    if base in PREVIEW_LABEL_REGISTRY:
                        discovered.append(f.name)
                        break

        return discovered

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

        When ENABLE_STATUS_SCROLLING is True, uses QScrollArea for marquee animation.
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

        if self.ENABLE_STATUS_SCROLLING:
            # Status label in scrollable area for marquee animation
            self._status_scroll = QScrollArea()
            self._status_scroll.setWidgetResizable(False)
            self._status_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
            self._status_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
            self._status_scroll.setFrameShape(QScrollArea.Shape.NoFrame)
            self._status_scroll.setAlignment(Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignRight)
            self._status_scroll.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
            self._status_scroll.setFixedHeight(20)
            self._status_scroll.setContentsMargins(0, 0, 0, 0)
            self._status_scroll.setStyleSheet("QScrollArea { padding: 0px; margin: 0px; background: transparent; }")

            self.status_label = QLabel("Ready")
            self.status_label.setStyleSheet(
                f"color: {self.color_scheme.to_hex(self.color_scheme.status_success)}; "
                f"font-weight: bold; padding: 0px; margin: 0px;"
            )
            self.status_label.setTextFormat(Qt.TextFormat.PlainText)
            self.status_label.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)
            self.status_label.setFixedHeight(20)
            self.status_label.setContentsMargins(0, 0, 0, 0)
            self.status_label.setAlignment(Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignRight)

            self._status_scroll.setWidget(self.status_label)
            header_layout.addWidget(self._status_scroll, 1)

            # Trigger initial layout
            QTimer.singleShot(0, lambda: self.status_label.adjustSize())
        else:
            header_layout.addStretch()
            # Simple status label without scrolling
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
            parent=list_widget,
            manager=self  # Pass manager reference for flash opacity lookup
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

        # Subscribe to ObjectStateRegistry lifecycle for time-travel binding
        from objectstate import ObjectStateRegistry
        ObjectStateRegistry.add_unregister_callback(self._on_registry_unregister)
        ObjectStateRegistry.add_register_callback(self._on_registry_register)

    def _on_registry_unregister(self, scope_key: str, state: 'ObjectState') -> None:
        """Handle ObjectState unregistration (time-travel: remove item from UI).

        Uses ITEM_HOOKS['scope_id_attr'] to find backing item by scope_id.
        """
        # Find backing item by matching scope_id
        item = self._find_backing_item_by_scope(scope_key)
        if item is None:
            return

        backing_items = self._get_backing_items()
        if item in backing_items:
            backing_items.remove(item)
            self.update_item_list()
            logger.debug(f"⏱️ TIME_TRAVEL: Removed item from UI: {scope_key}")

    def _on_registry_register(self, scope_key: str, state: 'ObjectState') -> None:
        """Handle ObjectState registration (time-travel: add item back to UI).

        Only processes during time-travel. Normal registration is handled elsewhere.
        Uses _time_travel_limbo_items to restore backing items.
        """
        from objectstate import ObjectStateRegistry

        # Only process during time-travel (normal registration handled elsewhere)
        if not ObjectStateRegistry._in_time_travel:
            return

        # Find backing item from limbo (saved when unregistered)
        item = self._time_travel_limbo_items.pop(scope_key, None)
        if item is None:
            return

        backing_items = self._get_backing_items()
        if item not in backing_items:
            insert_idx = self._get_item_insert_index(item, scope_key)
            if insert_idx is not None:
                backing_items.insert(insert_idx, item)
            else:
                backing_items.append(item)
            self.update_item_list()
            logger.debug(f"⏱️ TIME_TRAVEL: Added item back to UI: {scope_key}")

    def _find_backing_item_by_scope(self, scope_key: str) -> Optional[Any]:
        """Find backing item that matches the given scope_key.

        Uses ITEM_HOOKS['scope_id_builder'] or 'scope_id_attr' to match items.
        Returns None if no match or neither hook is configured.
        """
        hooks = self.ITEM_HOOKS
        scope_id_builder = hooks.get("scope_id_builder")
        scope_id_attr = hooks.get("scope_id_attr")

        if not scope_id_builder and not scope_id_attr:
            return None

        for idx, item in enumerate(self._get_backing_items()):
            # Use builder if available (for computed scope_ids like PipelineEditor)
            if scope_id_builder:
                item_scope = scope_id_builder(item, idx, self)
            elif isinstance(item, dict):
                item_scope = item.get(scope_id_attr)
            else:
                item_scope = getattr(item, scope_id_attr, None)

            if item_scope == scope_key:
                # Save to limbo for potential re-registration
                self._time_travel_limbo_items[scope_key] = item
                return item
        return None

    def _get_item_insert_index(self, item: Any, scope_key: str) -> Optional[int]:
        """Get the index at which to insert item during time-travel re-registration.

        Subclass can override to maintain correct ordering.
        Default: returns None (append to end).
        """
        return None

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
                             live_context_snapshot=None, full_path: str = None) -> object:
        """
        Resolve config attribute using ObjectState (no context stack rebuild).

        Looks up the ObjectState by scope_id and uses its cached resolved values.
        ObjectState already handles context stack building and caching internally.

        Args:
            item: Semantic item (used to get scope_id via subclass hook)
            config: Config dataclass instance (used to find nested state)
            attr_name: Name of the attribute to resolve
            live_context_snapshot: IGNORED - kept for API compatibility
            full_path: Optional full dotted path for nested field lookup (e.g., 'path_planning_config.well_filter')

        Returns:
            Resolved attribute value
        """
        from objectstate import ObjectStateRegistry

        try:
            # Get scope from item via cached lookup (avoids repeated calls during update cycle)
            item_scope = self._get_cached_scope(item)

            # Look up ObjectState by scope
            state = ObjectStateRegistry.get_by_scope(item_scope)
            if state is None:
                # No ObjectState registered - fall back to raw attribute
                return object.__getattribute__(config, attr_name)

            # Determine lookup path - either explicitly provided or derived from config type
            if full_path:
                lookup_path = full_path
            else:
                # Use ObjectState's resolve_for_type to find the correct path
                # This is the RIGHT BOUNDARY for nested config resolution
                config_type = type(config)
                resolved = state.resolve_for_type(config_type, attr_name)
                if resolved is not None:
                    return resolved
                # Fall back to direct lookup for top-level fields
                lookup_path = attr_name

            # With flat storage, all fields are in state.parameters with dotted paths
            resolved = state.get_resolved_value(lookup_path)
            if resolved is not None:
                return resolved

            # Check if it's a nested config by looking at _path_to_type
            # If lookup_path is in _path_to_type, it's a nested config - reconstruct it
            if lookup_path in state._path_to_type:
                # Reconstruct nested config from flat parameters
                nested_prefix = lookup_path
                nested_type = state._path_to_type[lookup_path]

                # Collect all parameters for this nested config
                prefix_dot = f'{nested_prefix}.'
                nested_params = {}
                for path, value in state.parameters.items():
                    if path.startswith(prefix_dot):
                        remainder = path[len(prefix_dot):]
                        # Only direct children
                        if '.' not in remainder:
                            nested_params[remainder] = value

                # CRITICAL: Do NOT filter out None values!
                # In OpenHCS, None has semantic meaning: "inherit from parent context"
                # When a user explicitly resets a field to None, we MUST pass that None
                # to the dataclass constructor so lazy resolution can walk up the MRO.

                # Instantiate nested config with ALL parameters including None values
                if nested_params:
                    return nested_type(**nested_params)
                else:
                    return nested_type()

            # Fall back to raw attribute if not in resolved cache
            return object.__getattribute__(config, attr_name)

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
        from pyqt_formgen.widgets.editors.simple_code_editor import SimpleCodeEditorService

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
        Update status label with optional auto-scrolling marquee.

        When ENABLE_STATUS_SCROLLING is True and text is too long, duplicates
        text and starts seamless looping animation.
        """
        if not self.status_label:
            return

        self._current_status_message = message

        if not self.ENABLE_STATUS_SCROLLING or not self._status_scroll:
            # Simple mode: just set text
            self.status_label.setText(message)
            return

        # Scrolling mode: check if text needs animation
        self.status_label.setText(message)
        self.status_label.adjustSize()

        # Calculate single message width for seamless loop reset
        separator = "     "
        temp_label = QLabel(f"{message}{separator}")
        temp_label.setFont(self.status_label.font())
        temp_label.adjustSize()
        self._status_single_message_width = temp_label.width()

        # Check if scrolling needed
        label_width = self.status_label.width()
        scroll_width = self._status_scroll.viewport().width()

        if label_width > scroll_width:
            # Duplicate text for seamless loop
            display_text = f"{message}{separator}{message}{separator}"
            self.status_label.setText(display_text)
            self.status_label.adjustSize()

        self._restart_status_scrolling()

    def _restart_status_scrolling(self) -> None:
        """Restart status scrolling animation if text is too long."""
        if not self._status_scroll:
            return

        # Stop existing timer
        if self._status_scroll_timer:
            self._status_scroll_timer.stop()
            self._status_scroll_timer = None

        # Reset position
        self._status_scroll.horizontalScrollBar().setValue(0)
        self._status_scroll_position = 0

        # Check if scrolling needed
        label_width = self.status_label.width()
        scroll_width = self._status_scroll.viewport().width()

        if label_width > scroll_width:
            # Start animation timer
            self._status_scroll_timer = QTimer(self)
            self._status_scroll_timer.setTimerType(Qt.TimerType.PreciseTimer)
            self._status_scroll_timer.timeout.connect(self._auto_scroll_status)
            self._status_scroll_timer.start(50)  # 20 fps scrolling

    def _auto_scroll_status(self) -> None:
        """Auto-scroll status text in seamless loop."""
        if not self._status_scroll or not self.status_label:
            return

        scrollbar = self._status_scroll.horizontalScrollBar()
        max_scroll = scrollbar.maximum()

        if max_scroll == 0:
            if self._status_scroll_timer:
                self._status_scroll_timer.stop()
            return

        # Advance scroll position
        self._status_scroll_position += 2  # Scroll speed

        # Reset at duplicate boundary for seamless loop
        reset_point = self._status_single_message_width or (max_scroll / 2)
        if self._status_scroll_position >= reset_point:
            self._status_scroll_position = 0

        scrollbar.setValue(int(self._status_scroll_position))

    def resizeEvent(self, event) -> None:
        """Handle resize to recalculate status scrolling."""
        super().resizeEvent(event)
        if self.ENABLE_STATUS_SCROLLING and self._status_scroll:
            # Re-apply message to recalculate duplication
            self.update_status(self._current_status_message)

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
            from pyqt_formgen.core.code_generator import generate_complete_pipeline_steps_code
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
        ObjectStateRegistry.increment_token()

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
        from objectstate import patch_lazy_constructors
        return patch_lazy_constructors()

    # ========== List Item Flash Animation ==========

    def _subscribe_flash_for_item(self, item: Any, list_item: QListWidgetItem, scope_id: str = None) -> None:
        """Subscribe to ObjectState changes for flash animation and register with overlay.

        Args:
            item: The backing data item
            list_item: The QListWidgetItem to flash
            scope_id: Pre-computed scope_id (uses cached lookup if not provided)
        """
        if scope_id is None:
            scope_id = self._get_cached_scope(item)
        logger.debug(f"⚡ FLASH_DEBUG _subscribe_flash_for_item: item={type(item).__name__}, scope_id={scope_id}")
        if not scope_id:
            logger.debug(f"⚡ FLASH_DEBUG: No scope_id for item {item}, returning")
            return

        # Store mapping for overlay rect lookup
        self._scope_to_list_item[scope_id] = list_item

        if scope_id in self._flash_subscriptions:
            logger.debug(f"⚡ FLASH_DEBUG: Already subscribed to {scope_id}, skipping")
            return

        # Register FlashElement with WindowFlashOverlay
        from pyqt_formgen.animation import FlashElement, WindowFlashOverlay

        def get_list_item_rect(window: QWidget) -> Optional[QRect]:
            """Get list item rect in window coordinates (clipped to viewport)."""
            if scope_id not in self._scope_to_list_item:
                logger.debug(f"⚡ FLASH_DEBUG get_list_item_rect: scope_id {scope_id} NOT in _scope_to_list_item (has {len(self._scope_to_list_item)} keys)")
                return None
            item = self._scope_to_list_item[scope_id]
            if item is None:
                logger.debug(f"⚡ FLASH_DEBUG get_list_item_rect: item is None for {scope_id}")
                return None

            # Get visual rect from list widget
            visual_rect = self.item_list.visualItemRect(item)
            if visual_rect.isEmpty():
                logger.debug(f"⚡ FLASH_DEBUG get_list_item_rect: visual_rect is empty for {scope_id}")
                return None

            # Clip to viewport (only flash visible portion)
            viewport = self.item_list.viewport()
            if viewport is None:
                logger.debug(f"⚡ FLASH_DEBUG get_list_item_rect: viewport is None for {scope_id}")
                return None

            # Intersect with viewport rect to get only visible portion
            viewport_rect = viewport.rect()
            clipped_rect = visual_rect.intersected(viewport_rect)
            if clipped_rect.isEmpty():
                logger.debug(f"⚡ FLASH_DEBUG get_list_item_rect: clipped_rect is empty for {scope_id}")
                return None

            # Map from VIEWPORT to window coordinates
            global_pos = viewport.mapToGlobal(clipped_rect.topLeft())
            local_pos = window.mapFromGlobal(global_pos)
            logger.debug(f"⚡ FLASH_DEBUG get_list_item_rect: SUCCESS for {scope_id}, rect={QRect(local_pos, clipped_rect.size())}")
            return QRect(local_pos, clipped_rect.size())

        def get_model_index():
            """Get QModelIndex for targeted item update (avoids full viewport repaint)."""
            if scope_id not in self._scope_to_list_item:
                return None
            item = self._scope_to_list_item[scope_id]
            if item is None:
                return None
            # Use indexFromItem directly - O(1) vs row() which may be O(n)
            return self.item_list.indexFromItem(item)

        element = FlashElement(
            key=scope_id,
            get_rect_in_window=get_list_item_rect,
            needs_scroll_clipping=False,
            source_id=f"list_item:{id(self)}:{scope_id}",  # Unique per manager instance + scope
            skip_overlay_paint=True,  # Delegate handles painting flash behind text
            delegate_widget=self.item_list,  # List widget for targeted updates
            get_model_index=get_model_index  # For targeted item updates (avoids full viewport repaint)
        )
        overlay = WindowFlashOverlay.get_for_window(self)
        logger.debug(f"⚡ FLASH_DEBUG: get_for_window returned overlay={overlay}, window={self.window()}")
        if overlay:
            overlay.register_element(element)
            logger.debug(f"⚡ FLASH_DEBUG: Registered element for {scope_id}, overlay has {len(overlay._elements)} keys")
        else:
            logger.debug(f"⚡ FLASH_DEBUG: No overlay for window, cannot register list item {scope_id}")

        # Subscribe to ObjectState changes
        from objectstate import ObjectStateRegistry
        state = ObjectStateRegistry.get_by_scope(scope_id)
        logger.debug(f"⚡ FLASH_DEBUG: ObjectStateRegistry.get_by_scope({scope_id}) = {state}")
        if not state:
            logger.debug(f"⚡ FLASH_DEBUG: No ObjectState for scope {scope_id}, returning")
            return

        def on_change(changed_paths):
            logger.debug(f"⚡ FLASH_DEBUG on_change CALLBACK FIRED: scope={scope_id}, paths={changed_paths}")
            self.queue_flash(scope_id)  # Global flash - list items flash in ALL windows
            # CRITICAL: Also refresh list item text when resolved values change
            # on_state_changed only fires when dirty SET changes, not when values change
            # So if func was already dirty and we reorder, text needs to update too
            self.queue_visual_update()

        state.on_resolved_changed(on_change)
        self._flash_subscriptions[scope_id] = (state, on_change)
        logger.debug(f"⚡ FLASH_DEBUG: Subscribed to {scope_id}, total subscriptions={len(self._flash_subscriptions)}")

        # Subscribe to dirty state changes for reactive dirty markers
        if scope_id not in self._dirty_subscriptions:
            def on_state_changed():
                """Update list item text when materialized state changes."""
                logger.debug(f"🔧 DIRTY_DEBUG on_state_changed: scope={scope_id}")
                self.queue_visual_update()  # Refresh list item text

            state.on_state_changed(on_state_changed)
            self._dirty_subscriptions[scope_id] = (state, on_state_changed)
            logger.debug(f"🔧 DIRTY_DEBUG: Subscribed to dirty changes for {scope_id}")

    # VisualUpdateMixin implementation - list items use WindowFlashOverlay (no custom methods needed)

    def _visual_repaint(self) -> None:
        """Trigger single repaint after all items updated (VisualUpdateMixin)."""
        if self.item_list:
            self.item_list.update()

    def _execute_text_update(self) -> None:
        """Execute text/placeholder update (VisualUpdateMixin)."""
        self.update_item_list()

    def _on_live_context_changed(self) -> None:
        """Override CrossWindowPreviewMixin to use unified visual update batching."""
        self.queue_visual_update()

    def _cleanup_flash_subscriptions(self) -> None:
        """Unsubscribe all flash and dirty callbacks and clear scope mappings."""
        logger.debug(f"⚡ FLASH_DEBUG _cleanup_flash_subscriptions: self={type(self).__name__}, clearing {len(self._flash_subscriptions)} flash + {len(self._dirty_subscriptions)} dirty subscriptions")

        # Cleanup flash subscriptions
        for scope_id, (state, on_change_callback) in list(self._flash_subscriptions.items()):
            logger.debug(f"⚡ FLASH_DEBUG: Unsubscribing from {scope_id}")
            try:
                state.off_resolved_changed(on_change_callback)
            except Exception as e:
                logger.debug(f"⚡ FLASH_DEBUG: Error unsubscribing from {scope_id}: {e}")

            # CRITICAL: Also unregister the FlashElement from the overlay
            # Otherwise stale geometry callbacks will point to deleted QListWidgetItems
            overlay = WindowFlashOverlay.get_for_window(self)
            if overlay:
                logger.debug(f"⚡ FLASH_DEBUG: Unregistering FlashElement for {scope_id}")
                overlay.unregister_element(scope_id)

        # Cleanup dirty state subscriptions
        for scope_id, (state, on_dirty_callback) in list(self._dirty_subscriptions.items()):
            try:
                state.off_state_changed(on_dirty_callback)
            except Exception as e:
                logger.debug(f"🔧 DIRTY_DEBUG: Error unsubscribing dirty from {scope_id}: {e}")

        self._flash_subscriptions.clear()
        self._dirty_subscriptions.clear()
        self._scope_to_list_item.clear()
        logger.debug(f"⚡ FLASH_DEBUG: Subscriptions cleared")

    # ========== Scope Coloring (optional) ==========

    def _get_list_item_scope(self, item: Any, index: int) -> Optional[Tuple[str, Any]]:
        """Resolve scope info for list item via ITEM_HOOKS."""
        hooks = self.ITEM_HOOKS
        item_type = hooks.get("scope_item_type")
        if not item_type:
            return None

        scope_id = None
        builder = hooks.get("scope_id_builder")
        if builder:
            scope_id = builder(item, index, self)
        else:
            scope_id_attr = hooks.get("scope_id_attr")
            if scope_id_attr:
                if isinstance(item, dict):
                    scope_id = item.get(scope_id_attr)
                else:
                    scope_id = getattr(item, scope_id_attr, None)

        return (scope_id, item_type) if scope_id else None

    def _apply_list_item_scope_color(self, list_item: QListWidgetItem, item: Any, index: int) -> None:
        """Apply scope-based background and border colors to list item.

        Stores full ScopeColorScheme so delegate can paint layered borders
        matching the corresponding window's border style.

        The actual list position (index) is passed to get_scope_color_scheme
        so that border patterns reflect the item's CURRENT position in the list,
        not the token number which is stable across reordering.
        """
        scope_info = self._get_list_item_scope(item, index)
        if not scope_info:
            return

        scope_id, item_type = scope_info
        from pyqt_formgen.widgets.shared.scope_color_utils import get_scope_color_scheme
        from pyqt_formgen.widgets.shared.list_item_delegate import FLASH_KEY_ROLE

        # Pass actual list position for border pattern (not token number)
        scheme = get_scope_color_scheme(scope_id, step_index=index)

        bg_color = item_type.get_background_color(scheme)
        if bg_color:
            list_item.setBackground(bg_color)

        # Store full scheme for layered border rendering (not just border color)
        list_item.setData(self.SCOPE_BORDER_ROLE, scheme)

        # Store flash key so delegate can paint flash behind text
        list_item.setData(FLASH_KEY_ROLE, scope_id)

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
        from pyqt_formgen.widgets.mixins import preserve_selection_during_update

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

        # Clear scope cache at start of update cycle - will be populated lazily
        self._item_scope_cache.clear()

        def update_func():
            """Update list items and subscriptions."""
            backing_items = self._get_backing_items()
            current_count = self.item_list.count()
            expected_count = len(backing_items)

            # Check if items have actually changed (not just count)
            # This detects plate switches where count is same but items are different
            items_changed = False
            if current_count == expected_count and current_count > 0:
                # Compare current scope_ids with subscribed scope_ids
                current_scope_ids = {self._get_cached_scope(item) for item in backing_items}
                subscribed_scope_ids = set(self._flash_subscriptions.keys())
                items_changed = current_scope_ids != subscribed_scope_ids
                logger.debug(f"⚡ FLASH_DEBUG: count={current_count}, current_scopes={current_scope_ids}, subscribed_scopes={subscribed_scope_ids}, items_changed={items_changed}")

            if current_count == expected_count and current_count > 0 and not items_changed:
                # Same count AND same items - update text in place (optimization)
                # DON'T cleanup subscriptions - they're still valid, just update text
                for index, item_obj in enumerate(backing_items):
                    list_item = self.item_list.item(index)
                    if list_item is None:
                        continue

                    display_text = self._format_list_item(item_obj, index, update_context)
                    if list_item.text() != display_text:
                        list_item.setText(display_text)

                    list_item.setData(Qt.ItemDataRole.UserRole, self._get_list_item_data(item_obj, index))
                    list_item.setToolTip(self._get_list_item_tooltip(item_obj))

                    for role_offset, value in self._get_list_item_extra_data(item_obj, index).items():
                        list_item.setData(Qt.ItemDataRole.UserRole + role_offset, value)

                    # Per-field styling roles (segments + dirty/sig-diff field sets)
                    self._set_item_styling_roles(list_item, display_text, item_obj)

                    # Apply scope-based colors
                    self._apply_list_item_scope_color(list_item, item_obj, index)

                    # Only subscribe if not already subscribed (use cached scope)
                    scope_id = self._get_cached_scope(item_obj)
                    if scope_id and scope_id not in self._flash_subscriptions:
                        self._subscribe_flash_for_item(item_obj, list_item, scope_id)
            else:
                # Count changed OR items changed - rebuild list AND subscriptions
                self._cleanup_flash_subscriptions()
                self._scope_to_list_item.clear()
                self.item_list.clear()
                for index, item_obj in enumerate(backing_items):
                    display_text = self._format_list_item(item_obj, index, update_context)
                    list_item = QListWidgetItem(display_text)
                    list_item.setData(Qt.ItemDataRole.UserRole, self._get_list_item_data(item_obj, index))
                    list_item.setToolTip(self._get_list_item_tooltip(item_obj))

                    for role_offset, value in self._get_list_item_extra_data(item_obj, index).items():
                        list_item.setData(Qt.ItemDataRole.UserRole + role_offset, value)

                    # Per-field styling roles (segments + dirty/sig-diff field sets)
                    self._set_item_styling_roles(list_item, display_text, item_obj)

                    # Apply scope-based colors
                    self._apply_list_item_scope_color(list_item, item_obj, index)

                    self.item_list.addItem(list_item)
                    # Pass cached scope to avoid double lookup
                    scope_id = self._get_cached_scope(item_obj)
                    self._subscribe_flash_for_item(item_obj, list_item, scope_id)

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

    def _format_list_item(self, item: Any, index: int, context: Any) -> str:
        """Format item for list display.

        Calls _format_item_content() which may return:
        - str: Plain text (no styling)
        - StyledText with segments: Per-field dirty/sig-diff styling via delegate
        """
        return self._format_item_content(item, index, context)

    @abstractmethod
    def _format_item_content(self, item: Any, index: int, context: Any) -> str:
        """Format item content for list display. Subclass must implement.

        May return StyledText with segments for per-field styling.
        """
        ...

    def _get_item_dirty_fields(self, item: Any) -> set:
        """Get set of dirty field paths for per-field styling."""
        try:
            scope_id = self._get_cached_scope(item)
            state = ObjectStateRegistry.get_by_scope(scope_id)
            return state.dirty_fields if state else set()
        except Exception:
            return set()

    def _get_item_sig_diff_fields(self, item: Any) -> set:
        """Get set of signature-diff field paths for per-field styling."""
        try:
            scope_id = self._get_cached_scope(item)
            state = ObjectStateRegistry.get_by_scope(scope_id)
            return state.signature_diff_fields if state else set()
        except Exception:
            return set()

    def _set_item_styling_roles(self, list_item: 'QListWidgetItem', display_text: Any, item_obj: Any) -> None:
        """Set per-field styling roles on a list item.

        Call this from any code that updates list items outside of _update_list()
        (e.g., single-item refresh methods in subclasses).

        Args:
            list_item: The QListWidgetItem to set roles on
            display_text: The display text (StyledText with layout, or plain str)
            item_obj: The backing data object for dirty/sig-diff field lookup
        """
        if isinstance(display_text, StyledText) and display_text.layout:
            list_item.setData(LAYOUT_ROLE, display_text.layout)
            list_item.setData(DIRTY_FIELDS_ROLE, self._get_item_dirty_fields(item_obj))
            list_item.setData(SIG_DIFF_FIELDS_ROLE, self._get_item_sig_diff_fields(item_obj))

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

    # === Config Preview Building ===

    def _build_preview_segments(
        self,
        state: Optional['ObjectState'],
    ) -> List[Tuple[str, str]]:
        """
        Build preview segments from PREVIEW_FIELD_CONFIGS (NAP, FIJI, MAT).
        Reads from ObjectState's pre-cached resolved values. No fallbacks.

        Returns:
            List of (formatted_label, field_path) tuples
        """
        if state is None:
            return []

        from pyqt_formgen.protocols import PreviewFormatterRegistry

        segments = []
        for field_path in self.get_enabled_preview_fields():
            value = state.get_resolved_value(field_path)
            if value is None:
                continue

            # Dataclass configs use format_config_indicator
            if is_dataclass(value) and not isinstance(value, type):
                formatted = PreviewFormatterRegistry.format_field(value, field_path.split('.')[-1])
                if formatted is None:
                    formatted = self._get_preview_label_for_config(value)
            else:
                formatted = self.format_preview_value(field_path, value)

            if formatted:
                segments.append((formatted, field_path))

        return segments

    def _build_styled_display_text(
        self,
        item_name: str,
        segments: List[Tuple[str, Optional[str]]],
    ) -> 'StyledText':
        """
        Build StyledText with inline preview format for per-field styling.

        Produces format: "▶ ItemName  (seg1 | seg2 | seg3)"

        Uses structured StyledTextLayout - delegate renders directly from structure.

        Args:
            item_name: Display name of the item
            segments: List of (label_text, field_path) tuples for preview items

        Returns:
            StyledText with layout for per-field dirty/sig-diff styling
        """
        # Convert tuples to Segment objects
        preview_segments = [Segment(text=label, field_path=path) for label, path in segments]

        layout = StyledTextLayout(
            name=Segment(text=item_name, field_path=''),  # Root path - matches any dirty/sig-diff
            first_line_segments=preview_segments,  # For inline format, segments go on first line
            multiline=False,
        )
        return StyledText(layout)

    def _build_multiline_styled_text(
        self,
        item_name: str,
        segments: List[Tuple[str, Optional[str]]],
        status_prefix: str = "",
        detail_line: str = "",
        config_segments: Optional[List[Tuple[str, Optional[str]]]] = None,
        first_line_segments: Optional[List[Tuple[str, Optional[str]]]] = None,
        item: Any = None,
        state: Optional['ObjectState'] = None,
    ) -> 'StyledText':
        """
        Build StyledText with multiline preview format for per-field styling.

        Produces format:
            ▶ ItemName (first_seg1 | first_seg2)
              detail_line
              └─ seg1 | seg2 | configs=[CFG1, CFG2]

        Uses structured StyledTextLayout - delegate renders directly from structure.

        Args:
            item_name: Display name of the item
            segments: List of (label_text, field_path) tuples for preview line
            status_prefix: Optional status prefix (e.g., "✓ Init")
            detail_line: Optional second line (e.g., path or description)
            config_segments: Optional config segments (NAP, FIJI, MAT) shown in brackets
            first_line_segments: Optional segments to show on first line after name
            item: Optional item for auto-including sig-diff fields in preview
            state: ObjectState with pre-cached resolved values (passed from entry point)

        Returns:
            StyledText with layout for per-field dirty/sig-diff styling
        """
        # Auto-include sig-diff fields that aren't already in segments
        if item is not None and state is not None:
            sig_diff_fields = self._get_item_sig_diff_fields(item)
            existing_paths = {path for _, path in segments if path}
            if config_segments:
                existing_paths.update(path for _, path in config_segments if path)
            if first_line_segments:
                existing_paths.update(path for _, path in first_line_segments if path)

            for field_path in sig_diff_fields:
                # Skip 'name' - it's already shown as the item title
                if field_path == 'name':
                    continue
                # Skip if already covered by existing segment (exact or prefix)
                if any(field_path == p or field_path.startswith(p + '.') for p in existing_paths):
                    continue
                # Read resolved value from ObjectState cache
                value = state.get_resolved_value(field_path)
                if value is None:
                    continue
                label = self._format_field_value(field_path, value)
                if label:
                    segments = list(segments) + [(label, field_path)]
                    existing_paths.add(field_path)

        # Convert tuples to Segment objects
        layout = StyledTextLayout(
            name=Segment(text=item_name, field_path=''),
            status_prefix=status_prefix,
            first_line_segments=[Segment(text=l, field_path=p) for l, p in (first_line_segments or [])],
            detail_line=detail_line,
            preview_segments=[Segment(text=l, field_path=p) for l, p in segments],
            config_segments=[Segment(text=l, field_path=p) for l, p in (config_segments or [])],
            multiline=True,
        )
        return StyledText(layout)

    def _build_item_display_from_format(
        self,
        item: Any,
        item_name: str,
        status_prefix: str = "",
        detail_line: str = "",
    ) -> 'StyledText':
        """
        Build StyledText using declarative LIST_ITEM_FORMAT config.

        Gets ObjectState ONCE and passes it down. No fallbacks.

        Args:
            item: The item to format (used for scope lookup and sig-diff detection)
            item_name: Display name
            status_prefix: Optional status prefix (e.g., "✓ Init")
            detail_line: Optional detail line (e.g., path)

        Returns:
            StyledText with segments for per-field styling
        """
        from objectstate import ObjectStateRegistry

        fmt = self.LIST_ITEM_FORMAT
        if fmt is None:
            return self._build_multiline_styled_text(
                item_name=item_name, segments=[], status_prefix=status_prefix,
                detail_line=detail_line, item=item, state=None,
            )

        # Get ObjectState ONCE at entry point
        scope_id = self._get_cached_scope(item) if item else None
        state = ObjectStateRegistry.get_by_scope(scope_id) if scope_id else None

        # Build segments from declared field paths
        first_line_segments = self._format_segments_from_config(state, list(fmt.first_line))
        preview_segments = self._format_segments_from_config(state, list(fmt.preview_line))

        # Config indicators from PREVIEW_FIELD_CONFIGS (NAP, FIJI, MAT)
        config_segments = None
        if fmt.show_config_indicators:
            config_segments = self._build_preview_segments(state=state)

        # Detail line from ObjectState
        if not detail_line and fmt.detail_line_field and state:
            detail_line = state.get_resolved_value(fmt.detail_line_field) or ""

        return self._build_multiline_styled_text(
            item_name=item_name,
            segments=preview_segments,
            status_prefix=status_prefix,
            detail_line=detail_line,
            config_segments=config_segments,
            first_line_segments=first_line_segments,
            item=item,
            state=state,
        )

    def _format_segments_from_config(
        self,
        state: Optional['ObjectState'],
        field_paths: List[str],
    ) -> List[Tuple[str, str]]:
        """
        Build segments from declarative field paths.
        Reads from ObjectState's pre-cached resolved values. No fallbacks.

        Args:
            state: ObjectState with pre-cached resolved values
            field_paths: List of field path strings (e.g., ['func', 'processing_config.group_by'])

        Returns:
            List of (label_text, field_path) tuples for styling
        """
        if state is None:
            return []

        fmt = self.LIST_ITEM_FORMAT
        formatters = fmt.formatters if fmt else {}
        segments = []

        for field_path in field_paths:
            value = state.get_resolved_value(field_path)
            if value is None:
                continue

            # Use custom formatter from ListItemFormat if available
            if field_path in formatters:
                formatter = formatters[field_path]
                if isinstance(formatter, str):
                    formatter_method = getattr(self, formatter, None)
                    if formatter_method:
                        # Try to pass state as second argument for formatters that need it
                        import inspect
                        sig = inspect.signature(formatter_method)
                        if len(sig.parameters) >= 2:
                            label = formatter_method(value, state)
                        else:
                            label = formatter_method(value)
                    else:
                        label = None
                else:
                    label = formatter(value)
            else:
                label = self._format_field_value(field_path, value)

            if label:
                segments.append((label, field_path))

        return segments

    def _format_field_value(self, field_path: str, value: Any) -> Optional[str]:
        """Simple type-based formatting for field values. No fallbacks."""
        if value is None:
            return None

        field_name = field_path.split('.')[-1]
        # Look up abbreviation from registry (declared on config classes)
        abbrev = self._get_field_abbreviation(field_name, type(value))

        # Dataclass config - delegate to config_preview_formatters (returns full indicator)
        if is_dataclass(value) and not isinstance(value, type):
            from pyqt_formgen.protocols import PreviewFormatterRegistry
            formatted = PreviewFormatterRegistry.format_field(value, field_name)
            if formatted is None:
                formatted = self._get_preview_label_for_config(value)
            return formatted

        # All other values: format value, prepend field name
        formatted = self._format_preview_value(value)
        if formatted is None:
            return None
        return f"{abbrev}:{formatted}"

    def _format_preview_value(self, value: Any) -> Optional[str]:
        """Format a value for preview display."""
        from enum import Enum

        if value is None:
            return None
        if isinstance(value, Enum):
            if value.value is None:
                return None
            return value.name
        if isinstance(value, list):
            if not value:
                return None
            if isinstance(value[0], Enum):
                return ','.join(v.value for v in value)
            return f'[{len(value)}]'
        if callable(value) and not isinstance(value, type):
            return getattr(value, '__name__', str(value))
        return str(value)

    def _get_preview_label_for_config(self, config_obj: Any) -> Optional[str]:
        """Return preview label from PREVIEW_LABEL_REGISTRY for a config object."""
        from dataclasses import is_dataclass, fields
        from objectstate.lazy_factory import PREVIEW_LABEL_REGISTRY

        config_type = type(config_obj)
        # Respect enabled field if present
        if is_dataclass(config_obj):
            field_names = {f.name for f in fields(config_obj)}
            if "enabled" in field_names:
                try:
                    if not bool(getattr(config_obj, "enabled")):
                        return None
                except Exception:
                    pass

        if config_type in PREVIEW_LABEL_REGISTRY:
            return PREVIEW_LABEL_REGISTRY[config_type]

        for base in config_type.__mro__[1:]:
            if base in PREVIEW_LABEL_REGISTRY:
                return PREVIEW_LABEL_REGISTRY[base]

        return None

    def _get_field_abbreviation(self, field_name: str, config_type: Optional[type] = None) -> str:
        """Look up field abbreviation from registry."""
        from objectstate.lazy_factory import FIELD_ABBREVIATIONS_REGISTRY

        if config_type is not None:
            if config_type in FIELD_ABBREVIATIONS_REGISTRY:
                abbrevs = FIELD_ABBREVIATIONS_REGISTRY[config_type]
                if field_name in abbrevs:
                    return abbrevs[field_name]
            for base in config_type.__mro__[1:]:
                if base in FIELD_ABBREVIATIONS_REGISTRY:
                    abbrevs = FIELD_ABBREVIATIONS_REGISTRY[base]
                    if field_name in abbrevs:
                        return abbrevs[field_name]

        for abbrevs in FIELD_ABBREVIATIONS_REGISTRY.values():
            if field_name in abbrevs:
                return abbrevs[field_name]

        return field_name

    def _get_nested_attr(self, obj: Any, path: str) -> Any:
        """Get nested attribute value by dotted path."""
        parts = path.split('.')
        for part in parts:
            if obj is None:
                return None
            if isinstance(obj, dict):
                obj = obj.get(part)
            else:
                obj = getattr(obj, part, None)
        return obj

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
        from pyqt_formgen.protocols import PreviewFormatterRegistry

        indicators = []
        for config_attr in config_attrs:
            config = getattr(config_source, config_attr, None)
            if config is None:
                continue

            # Create resolver function that uses live context
            # _resolve_config_attr uses resolve_for_type internally to find the correct path
            def resolve_attr(parent_obj, config_obj, attr_name, context,
                             i=item, snapshot=live_context_snapshot):
                return self._resolve_config_attr(i, config_obj, attr_name, snapshot)

            # Use registered formatter if available
            indicator_text = PreviewFormatterRegistry.format_field(config, config_attr)
            if indicator_text is None:
                indicator_text = self._get_preview_label_for_config(config)

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
        """Handle selection change. Interprets ITEM_HOOKS for attr/signal.

        NOTE: During time-travel, we update the selection attr but DON'T emit
        the signal. This prevents cascading side-effects like set_current_plate()
        clearing pipeline_steps before step unregister callbacks can save to limbo.
        """
        from objectstate import ObjectStateRegistry

        item = items[0]
        item_id = self._get_item_id(item)
        setattr(self, self.ITEM_HOOKS['selection_attr'], item_id)

        # Don't emit selection signal during time-travel to prevent side-effects
        if ObjectStateRegistry._in_time_travel:
            return

        signal = getattr(self, self.ITEM_HOOKS['selection_signal'])
        signal.emit(item_id if self.ITEM_HOOKS.get('selection_emit_id', True) else item)

    def _handle_selection_cleared(self) -> None:
        """Handle selection cleared. Interprets ITEM_HOOKS for attr/signal/clear_value.

        NOTE: During time-travel, we update the selection attr but DON'T emit
        the signal. This prevents cascading side-effects.
        """
        from objectstate import ObjectStateRegistry

        setattr(self, self.ITEM_HOOKS['selection_attr'], '')

        # Don't emit selection signal during time-travel to prevent side-effects
        if ObjectStateRegistry._in_time_travel:
            return

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
    def _get_scope_for_item(self, item: Any) -> str:
        """Get scope_id for an item (for ObjectState lookup). Subclass must implement."""
        ...

    def _get_cached_scope(self, item: Any) -> str:
        """Get scope_id with per-update-cycle caching.

        Uses _item_scope_cache to avoid repeated _get_scope_for_item calls
        during a single update cycle. Cache is cleared at start of each update.
        """
        item_id = id(item)
        if item_id not in self._item_scope_cache:
            self._item_scope_cache[item_id] = self._get_scope_for_item(item) or ''
        return self._item_scope_cache[item_id]

    # === CrossWindowPreviewMixin Hook (overridden by VisualUpdateMixin) ===

    def _handle_full_preview_refresh(self) -> None:
        """Override: Replaced by _execute_text_update via VisualUpdateMixin."""
        # This is only called if CrossWindowPreviewMixin's timer fires (shouldn't happen
        # since we override _on_live_context_changed), but kept for safety
        self.update_item_list()
