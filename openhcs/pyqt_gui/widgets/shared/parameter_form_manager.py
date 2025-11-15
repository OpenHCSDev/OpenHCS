"""
Dramatically simplified PyQt parameter form manager.

This demonstrates how the widget implementation can be drastically simplified
by leveraging the comprehensive shared infrastructure we've built.
"""

import dataclasses
import logging
from dataclasses import dataclass, field
from typing import Any, Dict, Type, Optional, Tuple
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QScrollArea, QLabel, QPushButton,
    QLineEdit, QCheckBox, QComboBox, QGroupBox, QSpinBox, QDoubleSpinBox
)
from PyQt6.QtCore import Qt, pyqtSignal, QTimer, QObject, QRunnable, QThreadPool
import weakref

# Performance monitoring
from openhcs.utils.performance_monitor import timer, get_monitor

# Type-based dispatch tables - NO duck typing, explicit type checks only
# Import all widget types needed for dispatch
from openhcs.pyqt_gui.widgets.shared.checkbox_group_widget import CheckboxGroupWidget
from openhcs.pyqt_gui.widgets.shared.no_scroll_spinbox import NoneAwareCheckBox, NoScrollSpinBox, NoScrollDoubleSpinBox, NoScrollComboBox
from openhcs.pyqt_gui.widgets.enhanced_path_widget import EnhancedPathWidget

# Forward reference for NoneAwareIntEdit and NoneAwareLineEdit (defined below in this file)
# These will be resolved at runtime when the dispatch is actually used

WIDGET_UPDATE_DISPATCH = [
    (QComboBox, 'update_combo_box'),
    (CheckboxGroupWidget, 'update_checkbox_group'),
    # NoneAware widgets with set_value() method - checked by type, not duck typing
    # Note: NoneAwareIntEdit and NoneAwareLineEdit are defined later in this file
    ('NoneAwareCheckBox', lambda w, v: w.set_value(v)),
    ('NoneAwareIntEdit', lambda w, v: w.set_value(v)),
    ('NoneAwareLineEdit', lambda w, v: w.set_value(v)),
    (EnhancedPathWidget, lambda w, v: w.set_path(v)),
    # Qt built-in widgets with setValue() method
    (QSpinBox, lambda w, v: w.setValue(v if v is not None else w.minimum())),
    (QDoubleSpinBox, lambda w, v: w.setValue(v if v is not None else w.minimum())),
    (NoScrollSpinBox, lambda w, v: w.setValue(v if v is not None else w.minimum())),
    (NoScrollDoubleSpinBox, lambda w, v: w.setValue(v if v is not None else w.minimum())),
    # Qt built-in widgets with setText() method
    (QLineEdit, lambda w, v: v is not None and w.setText(str(v)) or (v is None and w.clear())),
]

WIDGET_GET_DISPATCH = [
    (QComboBox, lambda w: w.itemData(w.currentIndex()) if w.currentIndex() >= 0 else None),
    (CheckboxGroupWidget, lambda w: w.get_selected_values()),
    # NoneAware widgets with get_value() method - checked by type, not duck typing
    ('NoneAwareCheckBox', lambda w: w.get_value()),
    ('NoneAwareIntEdit', lambda w: w.get_value()),
    ('NoneAwareLineEdit', lambda w: w.get_value()),
    (EnhancedPathWidget, lambda w: w.get_path()),
    # Qt built-in spinboxes with value() method and placeholder support
    (QSpinBox, lambda w: None if (hasattr(w, 'specialValueText') and w.value() == w.minimum() and w.specialValueText()) else w.value()),
    (QDoubleSpinBox, lambda w: None if (hasattr(w, 'specialValueText') and w.value() == w.minimum() and w.specialValueText()) else w.value()),
    (NoScrollSpinBox, lambda w: None if (hasattr(w, 'specialValueText') and w.value() == w.minimum() and w.specialValueText()) else w.value()),
    (NoScrollDoubleSpinBox, lambda w: None if (hasattr(w, 'specialValueText') and w.value() == w.minimum() and w.specialValueText()) else w.value()),
    # Qt built-in QLineEdit with text() method
    (QLineEdit, lambda w: w.text()),
]

logger = logging.getLogger(__name__)

# Import our comprehensive shared infrastructure
from openhcs.ui.shared.parameter_form_service import ParameterFormService
from openhcs.ui.shared.parameter_form_config_factory import pyqt_config

from openhcs.ui.shared.widget_creation_registry import create_pyqt6_registry
from .widget_strategies import PyQt6WidgetEnhancer

# Import PyQt-specific components
from .clickable_help_components import GroupBoxWithHelp, LabelWithHelp
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from .layout_constants import CURRENT_LAYOUT

# SINGLE SOURCE OF TRUTH: All input widget types that can receive styling (dimming, etc.)
# This includes all widgets created by the widget creation registry
# All widget types already imported above for dispatch tables

# Tuple of all input widget types for findChildren() calls
ALL_INPUT_WIDGET_TYPES = (
    QLineEdit, QComboBox, QPushButton, QCheckBox, QLabel,
    QSpinBox, QDoubleSpinBox, NoScrollSpinBox, NoScrollDoubleSpinBox,
    NoScrollComboBox, EnhancedPathWidget
)

# Import OpenHCS core components
# Old field path detection removed - using simple field name matching
from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils





class NoneAwareLineEdit(QLineEdit):
    """QLineEdit that properly handles None values for lazy dataclass contexts."""

    def get_value(self):
        """Get value, returning None for empty text instead of empty string."""
        text = self.text().strip()
        return None if text == "" else text

    def set_value(self, value):
        """Set value, handling None properly."""
        self.setText("" if value is None else str(value))


def _create_optimized_reset_button(field_id: str, param_name: str, reset_callback) -> 'QPushButton':
    """
    Optimized reset button factory - reuses configuration to save ~0.15ms per button.

    This factory creates reset buttons with consistent styling and configuration,
    avoiding repeated property setting overhead.
    """
    from PyQt6.QtWidgets import QPushButton

    button = QPushButton("Reset")
    button.setObjectName(f"{field_id}_reset")
    button.setMaximumWidth(60)  # Standard reset button width
    button.clicked.connect(reset_callback)
    return button


class NoneAwareIntEdit(QLineEdit):
    """QLineEdit that only allows digits and properly handles None values for integer fields."""

    def __init__(self, parent=None):
        super().__init__(parent)
        # Set up input validation to only allow digits
        from PyQt6.QtGui import QIntValidator
        self.setValidator(QIntValidator())

    def get_value(self):
        """Get value, returning None for empty text or converting to int."""
        text = self.text().strip()
        if text == "":
            return None
        try:
            return int(text)
        except ValueError:
            return None

    def set_value(self, value):
        """Set value, handling None properly."""
        if value is None:
            self.setText("")
        else:
            self.setText(str(value))


class _PlaceholderRefreshSignals(QObject):
    """Signals exposed by placeholder refresh worker."""

    completed = pyqtSignal(int, dict)
    failed = pyqtSignal(int, str)


class _PlaceholderRefreshTask(QRunnable):
    """Background task that resolves placeholder text without blocking the UI thread."""

    def __init__(self, manager: 'ParameterFormManager', generation: int,
                 parameters_snapshot: Dict[str, Any], placeholder_plan: Dict[str, bool],
                 live_context_snapshot: Optional['LiveContextSnapshot']):
        super().__init__()
        self._manager_ref = weakref.ref(manager)
        self._generation = generation
        self._parameters_snapshot = parameters_snapshot
        self._placeholder_plan = placeholder_plan
        self._live_context_snapshot = live_context_snapshot
        self.signals = _PlaceholderRefreshSignals()

        # CRITICAL: Capture thread-local GlobalPipelineConfig from main thread
        # Worker threads don't inherit thread-local storage, so we need to capture it here
        # and restore it in the worker thread before resolving placeholders
        from openhcs.config_framework.context_manager import get_base_global_config
        self._global_config_snapshot = get_base_global_config()

    def run(self):
        manager = self._manager_ref()
        if manager is None:
            return
        try:
            # CRITICAL: Restore thread-local GlobalPipelineConfig in worker thread
            # This ensures placeholder resolution sees the same global config as the main thread
            if self._global_config_snapshot is not None:
                from openhcs.config_framework.global_config import set_global_config_for_editing
                from openhcs.core.config import GlobalPipelineConfig
                set_global_config_for_editing(GlobalPipelineConfig, self._global_config_snapshot)

            placeholder_map = manager._compute_placeholder_map_async(
                self._parameters_snapshot,
                self._placeholder_plan,
                self._live_context_snapshot,
            )
            self.signals.completed.emit(self._generation, placeholder_map)
        except Exception as exc:
            logger.warning("Placeholder refresh worker failed: %s", exc)
            self.signals.failed.emit(self._generation, repr(exc))


@dataclass(frozen=True)
class LiveContextSnapshot:
    token: int
    values: Dict[type, Dict[str, Any]]
    scoped_values: Dict[str, Dict[type, Dict[str, Any]]] = field(default_factory=dict)


class ParameterFormManager(QWidget):
    """
    PyQt6 parameter form manager with simplified implementation using generic object introspection.

    This implementation leverages the new context management system and supports any object type:
    - Dataclasses (via dataclasses.fields())
    - ABC constructors (via inspect.signature())
    - Step objects (via attribute scanning)
    - Any object with parameters

    Key improvements:
    - Generic object introspection replaces manual parameter specification
    - Context-driven resolution using config_context() system
    - Automatic parameter extraction from object instances
    - Unified interface for all object types
    - Dramatically simplified constructor (4 parameters vs 12+)
    """

    parameter_changed = pyqtSignal(str, object)  # param_name, value

    # Class-level signal for cross-window context changes
    # Emitted when a form changes a value that might affect other open windows
    # Args: (field_path, new_value, editing_object, context_object)
    context_value_changed = pyqtSignal(str, object, object, object)

    # Class-level signal for cascading placeholder refreshes
    # Emitted when a form's placeholders are refreshed due to upstream changes
    # This allows downstream windows to know they should re-collect live context
    # Args: (editing_object, context_object)
    context_refreshed = pyqtSignal(object, object)

    # Class-level registry of all active form managers for cross-window updates
    # CRITICAL: This is scoped per orchestrator/plate using scope_id to prevent cross-contamination
    _active_form_managers = []

    # Class-level registry of external listeners (e.g., PipelineEditorWidget)
    # These are objects that want to receive cross-window signals but aren't ParameterFormManager instances
    # Format: [(listener_object, value_changed_handler, refresh_handler), ...]
    _external_listeners = []

    # Class constants for UI preferences (moved from constructor parameters)
    DEFAULT_USE_SCROLL_AREA = False
    DEFAULT_PLACEHOLDER_PREFIX = "Default"
    DEFAULT_COLOR_SCHEME = None

    # Performance optimization: Skip expensive operations for nested configs
    OPTIMIZE_NESTED_WIDGETS = True

    # Performance optimization: Async widget creation for large forms
    ASYNC_WIDGET_CREATION = True  # Create widgets progressively to avoid UI blocking
    ASYNC_THRESHOLD = 5  # Minimum number of parameters to trigger async widget creation
    INITIAL_SYNC_WIDGETS = 10  # Number of widgets to create synchronously for fast initial render
    ASYNC_PLACEHOLDER_REFRESH = True  # Resolve placeholders off the UI thread when possible
    _placeholder_thread_pool = QThreadPool.globalInstance()

    # Trailing debounce delays (ms) - timer restarts on each change, only executes after changes stop
    # This prevents expensive placeholder refreshes on every keystroke during rapid typing
    PARAMETER_CHANGE_DEBOUNCE_MS = 100  # Debounce for same-window placeholder refreshes
    CROSS_WINDOW_REFRESH_DELAY_MS = 100  # Debounce for cross-window placeholder refreshes

    _live_context_token_counter = 0

    # Class-level token cache for live context collection
    _live_context_cache: Optional['TokenCache'] = None  # Initialized on first use

    @classmethod
    def should_use_async(cls, param_count: int) -> bool:
        """Determine if async widget creation should be used based on parameter count.

        Args:
            param_count: Number of parameters in the form

        Returns:
            True if async widget creation should be used, False otherwise
        """
        return cls.ASYNC_WIDGET_CREATION and param_count > cls.ASYNC_THRESHOLD

    @classmethod
    def collect_live_context(cls, scope_filter: Optional[str] = None) -> LiveContextSnapshot:
        """
        Collect live context from all active form managers in scope.

        This is a class method that can be called from anywhere (e.g., PipelineEditor)
        to get the current live context for resolution.

        PERFORMANCE: Caches the snapshot and only invalidates when token changes.
        The token is incremented whenever any form value changes.

        Args:
            scope_filter: Optional scope filter (e.g., 'plate_path' or 'x::y::z')
                         If None, collects from all scopes

        Returns:
            LiveContextSnapshot with token and values dict
        """
        # Initialize cache on first use
        if cls._live_context_cache is None:
            from openhcs.config_framework import TokenCache, CacheKey
            cls._live_context_cache = TokenCache(lambda: cls._live_context_token_counter)

        from openhcs.config_framework import CacheKey
        cache_key = CacheKey.from_args(scope_filter)

        def compute_live_context() -> LiveContextSnapshot:
            """Compute live context from all active form managers."""
            import logging
            logger = logging.getLogger(__name__)
            logger.debug(f"❌ collect_live_context: CACHE MISS (token={cls._live_context_token_counter}, scope={scope_filter})")

            from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
            from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService

            live_context = {}
            scoped_live_context: Dict[str, Dict[type, Dict[str, Any]]] = {}
            alias_context = {}

            for manager in cls._active_form_managers:
                # Apply scope filter if provided
                if scope_filter is not None and manager.scope_id is not None:
                    if not cls._is_scope_visible_static(manager.scope_id, scope_filter):
                        continue

                # Collect values
                live_values = manager.get_user_modified_values()
                obj_type = type(manager.object_instance)

                # Map by the actual type
                live_context[obj_type] = live_values

                # Track scope-specific mappings (for step-level overlays)
                if manager.scope_id:
                    scoped_live_context.setdefault(manager.scope_id, {})[obj_type] = live_values

                # Also map by the base/lazy equivalent type for flexible matching
                base_type = get_base_type_for_lazy(obj_type)
                if base_type and base_type != obj_type:
                    alias_context.setdefault(base_type, live_values)

                lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(obj_type)
                if lazy_type and lazy_type != obj_type:
                    alias_context.setdefault(lazy_type, live_values)

            # Apply alias mappings only where no direct mapping exists
            for alias_type, values in alias_context.items():
                if alias_type not in live_context:
                    live_context[alias_type] = values

            # Create snapshot with current token (don't increment - that happens on value change)
            token = cls._live_context_token_counter
            return LiveContextSnapshot(token=token, values=live_context, scoped_values=scoped_live_context)

        # Use token cache to get or compute
        snapshot = cls._live_context_cache.get_or_compute(cache_key, compute_live_context)

        import logging
        logger = logging.getLogger(__name__)
        if snapshot.token == cls._live_context_token_counter:
            logger.debug(f"✅ collect_live_context: CACHE HIT (token={cls._live_context_token_counter}, scope={scope_filter})")

        return snapshot

    @staticmethod
    def _is_scope_visible_static(manager_scope: str, filter_scope: str) -> bool:
        """
        Static version of _is_scope_visible for class method use.

        Check if scopes match (prefix matching for hierarchical scopes).
        Supports generic hierarchical scope strings like 'x::y::z'.
        """
        return (
            manager_scope == filter_scope or
            manager_scope.startswith(f"{filter_scope}::") or
            filter_scope.startswith(f"{manager_scope}::")
        )

    @classmethod
    def register_external_listener(cls, listener: object,
                                   value_changed_handler,
                                   refresh_handler):
        """Register an external listener for cross-window signals.

        External listeners are objects (like PipelineEditorWidget) that want to receive
        cross-window signals but aren't ParameterFormManager instances.

        Args:
            listener: The listener object (for identification)
            value_changed_handler: Handler for context_value_changed signal (required)
            refresh_handler: Handler for context_refreshed signal (optional, can be None)
        """
        # Add to registry
        cls._external_listeners.append((listener, value_changed_handler, refresh_handler))

        # Connect all existing managers to this listener
        for manager in cls._active_form_managers:
            if value_changed_handler:
                manager.context_value_changed.connect(value_changed_handler)
            if refresh_handler:
                manager.context_refreshed.connect(refresh_handler)

        logger.debug(f"Registered external listener: {listener.__class__.__name__}")

    @classmethod
    def unregister_external_listener(cls, listener: object):
        """Unregister an external listener.

        Args:
            listener: The listener object to unregister
        """
        # Find and remove from registry
        cls._external_listeners = [
            (l, vh, rh) for l, vh, rh in cls._external_listeners if l is not listener
        ]

        logger.debug(f"Unregistered external listener: {listener.__class__.__name__}")

    @classmethod
    def trigger_global_cross_window_refresh(cls):
        """Trigger cross-window refresh for all active form managers.

        This is called when global config changes (e.g., from plate manager code editor)
        to ensure all open windows refresh their placeholders with the new values.

        CRITICAL: Also emits context_refreshed signal for each manager so that
        downstream components (like function pattern editor) can refresh their state.

        CRITICAL: Also notifies external listeners (like PipelineEditor) directly,
        especially important when all managers are unregistered (e.g., after cancel).
        """
        logger.debug(f"Triggering global cross-window refresh for {len(cls._active_form_managers)} active managers")
        for manager in cls._active_form_managers:
            try:
                manager._refresh_with_live_context()
                # CRITICAL: Emit context_refreshed signal so dual editor window can refresh function editor
                # This ensures group_by selector syncs with GlobalPipelineConfig changes
                manager.context_refreshed.emit(manager.object_instance, manager.context_obj)
            except Exception as e:
                logger.warning(f"Failed to refresh manager during global refresh: {e}")

        # CRITICAL: Notify external listeners directly (e.g., PipelineEditor)
        # This is especially important when all managers are unregistered (e.g., after cancel)
        # and there are no managers left to emit signals
        logger.debug(f"Notifying {len(cls._external_listeners)} external listeners")
        for listener, value_changed_handler, refresh_handler in cls._external_listeners:
            if refresh_handler:  # Skip if None
                try:
                    # Call refresh handler with None for both editing_object and context_object
                    # since this is a global refresh not tied to a specific object
                    refresh_handler(None, None)
                except Exception as e:
                    logger.warning(f"Failed to notify external listener {listener.__class__.__name__}: {e}")

    def _notify_external_listeners_refreshed(self):
        """Notify external listeners that context has been refreshed.

        This is called when a manager emits context_refreshed signal but external
        listeners also need to be notified directly (e.g., after reset).
        """
        logger.info(f"🔍 _notify_external_listeners_refreshed called from {self.field_id}, notifying {len(self._external_listeners)} listeners")
        for listener, value_changed_handler, refresh_handler in self._external_listeners:
            if refresh_handler:  # Skip if None
                try:
                    logger.info(f"🔍   Calling refresh_handler for {listener.__class__.__name__}")
                    refresh_handler(self.object_instance, self.context_obj)
                except Exception as e:
                    logger.warning(f"Failed to notify external listener {listener.__class__.__name__}: {e}")

    def __init__(self, object_instance: Any, field_id: str, parent=None, context_obj=None, exclude_params: Optional[list] = None, initial_values: Optional[Dict[str, Any]] = None, parent_manager=None, read_only: bool = False, scope_id: Optional[str] = None, color_scheme=None):
        """
        Initialize PyQt parameter form manager with generic object introspection.

        Args:
            object_instance: Any object to build form for (dataclass, ABC constructor, step, etc.)
            field_id: Unique identifier for the form
            parent: Optional parent widget
            context_obj: Context object for placeholder resolution (orchestrator, pipeline_config, etc.)
            exclude_params: Optional list of parameter names to exclude from the form
            initial_values: Optional dict of parameter values to use instead of extracted defaults
            parent_manager: Optional parent ParameterFormManager (for nested configs)
            read_only: If True, make all widgets read-only and hide reset buttons
            scope_id: Optional scope identifier (e.g., plate_path) to limit cross-window updates to same orchestrator
            color_scheme: Optional color scheme for styling (uses DEFAULT_COLOR_SCHEME or default if None)
        """
        with timer(f"ParameterFormManager.__init__ ({field_id})", threshold_ms=5.0):
            QWidget.__init__(self, parent)

            # Store core configuration
            self.object_instance = object_instance
            self.field_id = field_id
            self.context_obj = context_obj
            self.exclude_params = exclude_params or []
            self.read_only = read_only

            # CRITICAL: Store scope_id for cross-window update scoping
            # If parent_manager exists, inherit its scope_id (nested forms belong to same orchestrator)
            # Otherwise use provided scope_id or None (global scope)
            self.scope_id = parent_manager.scope_id if parent_manager else scope_id

            # OPTIMIZATION: Store parent manager reference early so setup_ui() can detect nested configs
            self._parent_manager = parent_manager

            # Track completion callbacks for async widget creation
            self._on_build_complete_callbacks = []
            # Track callbacks to run after placeholder refresh (for enabled styling that needs resolved values)
            self._on_placeholder_refresh_complete_callbacks = []

            # Debounced parameter-change refresh bookkeeping
            self._pending_debounced_exclude_param: Optional[str] = None
            if self.PARAMETER_CHANGE_DEBOUNCE_MS > 0:
                self._parameter_change_timer = QTimer(self)
                self._parameter_change_timer.setSingleShot(True)
                self._parameter_change_timer.timeout.connect(self._run_debounced_placeholder_refresh)
            else:
                self._parameter_change_timer = None

            # Async placeholder refresh bookkeeping
            self._has_completed_initial_placeholder_refresh = False
            self._placeholder_refresh_generation = 0
            self._pending_placeholder_metadata = {}
            self._active_placeholder_task = None
            self._cached_global_context_token = None
            self._cached_global_context_instance = None
            self._cached_parent_contexts: Dict[int, Tuple[int, Any]] = {}

            # Placeholder text cache (value-based, not token-based)
            # Key: (param_name, hash of live context values) -> placeholder text
            # This prevents unnecessary re-resolution when unrelated configs change
            # No size limit needed - cache naturally stays small (< 20 params × few context states)
            self._placeholder_text_cache: Dict[Tuple, str] = {}

            # Cache for entire _refresh_all_placeholders operation (token-based)
            # Key: (exclude_param, live_context_token) -> prevents redundant refreshes
            from openhcs.config_framework import TokenCache
            self._placeholder_refresh_cache = TokenCache(lambda: type(self)._live_context_token_counter)

            # Initialize service layer first (needed for parameter extraction)
            with timer("  Service initialization", threshold_ms=1.0):
                self.service = ParameterFormService()

            # Auto-extract parameters and types using generic introspection
            with timer("  Extract parameters from object", threshold_ms=2.0):
                self.parameters, self.parameter_types, self.dataclass_type = self._extract_parameters_from_object(object_instance, self.exclude_params)

                # CRITICAL FIX: Override with initial_values if provided (for function kwargs)
                if initial_values:
                    for param_name, value in initial_values.items():
                        if param_name in self.parameters:
                            self.parameters[param_name] = value

                # Initialize widget value cache from extracted parameters
                self._current_value_cache: Dict[str, Any] = dict(self.parameters)
                self._placeholder_candidates = {
                    name for name, val in self.parameters.items() if val is None
                }

            # DELEGATE TO SERVICE LAYER: Analyze form structure using service
            # Use UnifiedParameterAnalyzer-derived descriptions as the single source of truth
            with timer("  Analyze form structure", threshold_ms=5.0):
                parameter_info = getattr(self, '_parameter_descriptions', {})
                self.form_structure = self.service.analyze_parameters(
                    self.parameters, self.parameter_types, field_id, parameter_info, self.dataclass_type
                )

            # Auto-detect configuration settings
            with timer("  Auto-detect config settings", threshold_ms=1.0):
                self.global_config_type = self._auto_detect_global_config_type()
                self.placeholder_prefix = self.DEFAULT_PLACEHOLDER_PREFIX

            # Create configuration object with auto-detected settings
            with timer("  Create config object", threshold_ms=1.0):
                # Use instance color_scheme if provided, otherwise fall back to class default or create new
                resolved_color_scheme = color_scheme or self.DEFAULT_COLOR_SCHEME or PyQt6ColorScheme()
                config = pyqt_config(
                    field_id=field_id,
                    color_scheme=resolved_color_scheme,
                    function_target=object_instance,  # Use object_instance as function_target
                    use_scroll_area=self.DEFAULT_USE_SCROLL_AREA
                )
                # IMPORTANT: Keep parameter_info consistent with the analyzer output to avoid losing descriptions
                config.parameter_info = parameter_info
                config.dataclass_type = self.dataclass_type
                config.global_config_type = self.global_config_type
                config.placeholder_prefix = self.placeholder_prefix

                # Auto-determine editing mode based on object type analysis
                config.is_lazy_dataclass = self._is_lazy_dataclass()
                config.is_global_config_editing = not config.is_lazy_dataclass

            # Initialize core attributes
            with timer("  Initialize core attributes", threshold_ms=1.0):
                self.config = config
                self.param_defaults = self._extract_parameter_defaults()

            # Initialize tracking attributes
            self.widgets = {}
            self.reset_buttons = {}  # Track reset buttons for API compatibility
            self.nested_managers = {}
            self._last_emitted_values: Dict[str, Any] = {}
            self.reset_fields = set()  # Track fields that have been explicitly reset to show inheritance

            # Track which fields have been explicitly set by users
            self._user_set_fields: set = set()

            # Track if initial form load is complete (disable live updates during initial load)
            self._initial_load_complete = False

            # OPTIMIZATION: Block cross-window updates during batch operations (e.g., reset_all)
            self._block_cross_window_updates = False

            # SHARED RESET STATE: Track reset fields across all nested managers within this form
            if hasattr(parent, 'shared_reset_fields'):
                # Nested manager: use parent's shared reset state
                self.shared_reset_fields = parent.shared_reset_fields
            else:
                # Root manager: create new shared reset state
                self.shared_reset_fields = set()

            # Store backward compatibility attributes
            self.parameter_info = config.parameter_info
            self.use_scroll_area = config.use_scroll_area
            self.function_target = config.function_target
            self.color_scheme = config.color_scheme

            # Form structure already analyzed above using UnifiedParameterAnalyzer descriptions

            # Get widget creator from registry
            self._widget_creator = create_pyqt6_registry()

            # Context system handles updates automatically
            self._context_event_coordinator = None

            # Set up UI
            with timer("  Setup UI (widget creation)", threshold_ms=10.0):
                self.setup_ui()

            # Connect parameter changes to live placeholder updates
            # When any field changes, refresh all placeholders using current form state
            # CRITICAL: Don't refresh during reset operations - reset handles placeholders itself
            # CRITICAL: Always use live context from other open windows for placeholder resolution
            # CRITICAL: Don't refresh when 'enabled' field changes - it's styling-only and doesn't affect placeholders
            # CRITICAL: Pass the changed param_name so we can skip refreshing it (user just edited it, it's not inherited)
            # CRITICAL: Nested managers must trigger refresh on ROOT manager to collect live context
            if self._parent_manager is None:
                self.parameter_changed.connect(self._on_parameter_changed_root)
            else:
                self.parameter_changed.connect(self._on_parameter_changed_nested)

            # UNIVERSAL ENABLED FIELD BEHAVIOR: Watch for 'enabled' parameter changes and apply styling
            # This works for any form (function parameters, dataclass fields, etc.) that has an 'enabled' parameter
            # When enabled resolves to False, apply visual dimming WITHOUT blocking input
            if 'enabled' in self.parameters:
                self.parameter_changed.connect(self._on_enabled_field_changed_universal)
                # CRITICAL: Apply initial styling based on current enabled value
                # This ensures styling is applied on window open, not just when toggled
                # Register callback to run AFTER placeholders are refreshed (not before)
                # because enabled styling needs the resolved placeholder value from the widget
                self._on_placeholder_refresh_complete_callbacks.append(self._apply_initial_enabled_styling)

            # Register this form manager for cross-window updates (only root managers, not nested)
            if self._parent_manager is None:
                # CRITICAL: Store initial values when window opens for cancel/revert behavior
                # When user cancels, other windows should revert to these initial values, not current edited values
                self._initial_values_on_open = self.get_user_modified_values() if hasattr(self.config, '_resolve_field_value') else self.get_current_values()

                # Connect parameter_changed to emit cross-window context changes
                self.parameter_changed.connect(self._emit_cross_window_change)

                # Connect this instance's signal to all existing instances
                for existing_manager in self._active_form_managers:
                    # Connect this instance to existing instances
                    self.context_value_changed.connect(existing_manager._on_cross_window_context_changed)
                    self.context_refreshed.connect(existing_manager._on_cross_window_context_refreshed)
                    # Connect existing instances to this instance
                    existing_manager.context_value_changed.connect(self._on_cross_window_context_changed)
                    existing_manager.context_refreshed.connect(self._on_cross_window_context_refreshed)

                # Connect this instance to all external listeners
                for listener, value_changed_handler, refresh_handler in self._external_listeners:
                    if value_changed_handler:
                        self.context_value_changed.connect(value_changed_handler)
                    if refresh_handler:
                        self.context_refreshed.connect(refresh_handler)

                # Add this instance to the registry
                self._active_form_managers.append(self)

            # Debounce timer for cross-window placeholder refresh
            self._cross_window_refresh_timer = None

            # CRITICAL: Detect user-set fields for lazy dataclasses
            # Check which parameters were explicitly set (raw non-None values)
            with timer("  Detect user-set fields", threshold_ms=1.0):
                from dataclasses import is_dataclass
                if is_dataclass(object_instance):
                    for field_name, raw_value in self.parameters.items():
                        # SIMPLE RULE: Raw non-None = user-set, Raw None = inherited
                        if raw_value is not None:
                            self._user_set_fields.add(field_name)

            # OPTIMIZATION: Skip placeholder refresh for nested configs - parent will handle it
            # This saves ~5-10ms per nested config × 20 configs = 100-200ms total
            is_nested = self._parent_manager is not None

            # CRITICAL FIX: Don't refresh placeholders here - they need to be refreshed AFTER
            # async widget creation completes. The refresh will be triggered by the build_form()
            # completion callback to ensure all widgets (including nested async forms) are ready.
            # This fixes the issue where optional dataclass placeholders resolve with wrong context
            # because they refresh before nested managers are fully initialized.

            # Mark initial load as complete - enable live placeholder updates from now on
            self._initial_load_complete = True
            if not is_nested:
                self._apply_to_nested_managers(lambda name, manager: setattr(manager, '_initial_load_complete', True))

            # Connect to destroyed signal for cleanup
            self.destroyed.connect(self._on_destroyed)

            # CRITICAL: Refresh placeholders with live context after initial load
            # This ensures new windows immediately show live values from other open windows
            is_root_global_config = (self.config.is_global_config_editing and
                                     self.global_config_type is not None and
                                     self.context_obj is None)
            if is_root_global_config:
                # For root GlobalPipelineConfig, refresh with sibling inheritance
                with timer("  Root global config sibling inheritance refresh", threshold_ms=10.0):
                    self._refresh_all_placeholders()
                    self._apply_to_nested_managers(lambda name, manager: manager._refresh_all_placeholders())
            else:
                # For other windows (PipelineConfig, Step), refresh with live context from other windows
                with timer("  Initial live context refresh", threshold_ms=10.0):
                    self._refresh_with_live_context()

    # ==================== GENERIC OBJECT INTROSPECTION METHODS ====================

    def _extract_parameters_from_object(self, obj: Any, exclude_params: Optional[list] = None) -> Tuple[Dict[str, Any], Dict[str, Type], Type]:
        """
        Extract parameters and types from any object using unified analysis.

        Uses the existing UnifiedParameterAnalyzer for consistent handling of all object types.

        Args:
            obj: Object to extract parameters from
            exclude_params: Optional list of parameter names to exclude
        """
        from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer

        # Use unified analyzer for all object types with exclusions
        param_info_dict = UnifiedParameterAnalyzer.analyze(obj, exclude_params=exclude_params)

        parameters = {}
        parameter_types = {}

        # CRITICAL FIX: Store parameter descriptions for docstring display
        self._parameter_descriptions = {}

        for name, param_info in param_info_dict.items():
            # Use the values already extracted by UnifiedParameterAnalyzer
            # This preserves lazy config behavior (None values for unset fields)
            parameters[name] = param_info.default_value
            parameter_types[name] = param_info.param_type

            # LOG PARAMETER TYPES
            # CRITICAL FIX: Preserve parameter descriptions for help display
            if param_info.description:
                self._parameter_descriptions[name] = param_info.description

        return parameters, parameter_types, type(obj)

    # ==================== WIDGET CREATION METHODS ====================

    def _auto_detect_global_config_type(self) -> Optional[Type]:
        """Auto-detect global config type from context."""
        from openhcs.config_framework import get_base_config_type
        return getattr(self.context_obj, 'global_config_type', get_base_config_type())


    def _extract_parameter_defaults(self) -> Dict[str, Any]:
        """
        Extract parameter defaults from the object.

        For reset functionality: returns the SIGNATURE defaults, not current instance values.
        - For functions: signature defaults
        - For dataclasses: field defaults from class definition
        - For any object: constructor parameter defaults from class definition
        """
        from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer

        # CRITICAL FIX: For reset functionality, we need SIGNATURE defaults, not instance values
        # Analyze the CLASS/TYPE, not the instance, to get signature defaults
        if callable(self.object_instance) and not dataclasses.is_dataclass(self.object_instance):
            # For functions/callables, analyze directly (not their type)
            analysis_target = self.object_instance
        elif dataclasses.is_dataclass(self.object_instance):
            # For dataclass instances, analyze the type to get field defaults
            analysis_target = type(self.object_instance)
        elif hasattr(self.object_instance, '__class__'):
            # For regular object instances (like steps), analyze the class to get constructor defaults
            analysis_target = type(self.object_instance)
        else:
            # For types/classes, analyze directly
            analysis_target = self.object_instance

        # Use unified analyzer to get signature defaults with same exclusions
        param_info_dict = UnifiedParameterAnalyzer.analyze(analysis_target, exclude_params=self.exclude_params)

        return {name: info.default_value for name, info in param_info_dict.items()}

    def _is_lazy_dataclass(self) -> bool:
        """Check if the object represents a lazy dataclass."""
        if hasattr(self.object_instance, '_resolve_field_value'):
            return True
        if self.dataclass_type:
            from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
            return LazyDefaultPlaceholderService.has_lazy_resolution(self.dataclass_type)
        return False

    def create_widget(self, param_name: str, param_type: Type, current_value: Any,
                     widget_id: str, parameter_info: Any = None) -> Any:
        """Create widget using the registry creator function."""
        widget = self._widget_creator(param_name, param_type, current_value, widget_id, parameter_info)

        if widget is None:
            from PyQt6.QtWidgets import QLabel
            widget = QLabel(f"ERROR: Widget creation failed for {param_name}")

        return widget




    @classmethod
    def from_dataclass_instance(cls, dataclass_instance: Any, field_id: str,
                              placeholder_prefix: str = "Default",
                              parent=None, use_scroll_area: bool = True,
                              function_target=None, color_scheme=None,
                              force_show_all_fields: bool = False,
                              global_config_type: Optional[Type] = None,
                              context_event_coordinator=None, context_obj=None,
                              scope_id: Optional[str] = None):
        """
        SIMPLIFIED: Create ParameterFormManager using new generic constructor.

        This method now simply delegates to the simplified constructor that handles
        all object types automatically through generic introspection.

        Args:
            dataclass_instance: The dataclass instance to edit
            field_id: Unique identifier for the form
            context_obj: Context object for placeholder resolution
            scope_id: Optional scope identifier (e.g., plate_path) to limit cross-window updates
            **kwargs: Legacy parameters (ignored - handled automatically)

        Returns:
            ParameterFormManager configured for any object type
        """
        # Validate input
        from dataclasses import is_dataclass
        if not is_dataclass(dataclass_instance):
            raise ValueError(f"{type(dataclass_instance)} is not a dataclass")

        # Use simplified constructor with automatic parameter extraction
        # CRITICAL: Do NOT default context_obj to dataclass_instance
        # This creates circular context bug where form uses itself as parent
        # Caller must explicitly pass context_obj if needed (e.g., Step Editor passes pipeline_config)
        return cls(
            object_instance=dataclass_instance,
            field_id=field_id,
            parent=parent,
            context_obj=context_obj,  # No default - None means inherit from thread-local global only
            scope_id=scope_id,
            color_scheme=color_scheme  # Pass through color_scheme parameter
        )

    @classmethod
    def from_object(cls, object_instance: Any, field_id: str, parent=None, context_obj=None):
        """
        NEW: Create ParameterFormManager for any object type using generic introspection.

        This is the new primary factory method that works with:
        - Dataclass instances and types
        - ABC constructors and functions
        - Step objects with config attributes
        - Any object with parameters

        Args:
            object_instance: Any object to build form for
            field_id: Unique identifier for the form
            parent: Optional parent widget
            context_obj: Context object for placeholder resolution

        Returns:
            ParameterFormManager configured for the object type
        """
        return cls(
            object_instance=object_instance,
            field_id=field_id,
            parent=parent,
            context_obj=context_obj
        )



    def setup_ui(self):
        """Set up the UI layout."""
        from openhcs.utils.performance_monitor import timer

        # OPTIMIZATION: Skip expensive operations for nested configs
        is_nested = hasattr(self, '_parent_manager')

        with timer("    Layout setup", threshold_ms=1.0):
            layout = QVBoxLayout(self)
            # Apply configurable layout settings
            layout.setSpacing(CURRENT_LAYOUT.main_layout_spacing)
            layout.setContentsMargins(*CURRENT_LAYOUT.main_layout_margins)

        # OPTIMIZATION: Skip style generation for nested configs (inherit from parent)
        # This saves ~1-2ms per nested config × 20 configs = 20-40ms
        # ALSO: Skip if parent is a ConfigWindow (which handles styling itself)
        qt_parent = self.parent()
        parent_is_config_window = qt_parent is not None and qt_parent.__class__.__name__ == 'ConfigWindow'
        should_apply_styling = not is_nested and not parent_is_config_window
        if should_apply_styling:
            with timer("    Style generation", threshold_ms=1.0):
                from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
                style_gen = StyleSheetGenerator(self.color_scheme)
                self.setStyleSheet(style_gen.generate_config_window_style())

        # Build form content
        with timer("    Build form", threshold_ms=5.0):
            form_widget = self.build_form()

        # OPTIMIZATION: Never add scroll areas for nested configs
        # This saves ~2ms per nested config × 20 configs = 40ms
        with timer("    Add scroll area", threshold_ms=1.0):
            if self.config.use_scroll_area and not is_nested:
                scroll_area = QScrollArea()
                scroll_area.setWidgetResizable(True)
                scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
                scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
                scroll_area.setWidget(form_widget)
                layout.addWidget(scroll_area)
            else:
                layout.addWidget(form_widget)

    def build_form(self) -> QWidget:
        """Build form UI by delegating to service layer analysis."""
        from openhcs.utils.performance_monitor import timer

        with timer("      Create content widget", threshold_ms=1.0):
            content_widget = QWidget()
            content_layout = QVBoxLayout(content_widget)
            content_layout.setSpacing(CURRENT_LAYOUT.content_layout_spacing)
            content_layout.setContentsMargins(*CURRENT_LAYOUT.content_layout_margins)

        # DELEGATE TO SERVICE LAYER: Use analyzed form structure
        param_count = len(self.form_structure.parameters)
        if self.should_use_async(param_count):
            # Hybrid sync/async widget creation for large forms
            # Create first N widgets synchronously for fast initial render, then remaining async
            with timer(f"      Hybrid widget creation: {param_count} total widgets", threshold_ms=1.0):
                # Track pending nested managers for async completion
                # Only root manager needs to track this, and only for nested managers that will use async
                is_root = self._parent_manager is None
                if is_root:
                    self._pending_nested_managers = {}

                # Split parameters into sync and async batches
                sync_params = self.form_structure.parameters[:self.INITIAL_SYNC_WIDGETS]
                async_params = self.form_structure.parameters[self.INITIAL_SYNC_WIDGETS:]

                # Create initial widgets synchronously for fast render
                if sync_params:
                    with timer(f"        Create {len(sync_params)} initial widgets (sync)", threshold_ms=5.0):
                        for param_info in sync_params:
                            widget = self._create_widget_for_param(param_info)
                            content_layout.addWidget(widget)

                    # Apply placeholders to initial widgets immediately for fast visual feedback
                    # These will be refreshed again at the end when all widgets are ready
                    # CRITICAL: Collect live context even for this early refresh to show unsaved values from open windows
                    with timer(f"        Initial placeholder refresh ({len(sync_params)} widgets)", threshold_ms=5.0):
                        early_live_context = self._collect_live_context_from_other_windows() if self._parent_manager is None else None
                        self._refresh_all_placeholders(live_context=early_live_context)

                def on_async_complete():
                    """Called when all async widgets are created for THIS manager."""
                    # CRITICAL FIX: Don't trigger styling callbacks yet!
                    # They need to wait until ALL nested managers complete their async widget creation
                    # Otherwise findChildren() will return empty lists for nested forms still being built

                    # CRITICAL FIX: Only root manager refreshes placeholders, and only after ALL nested managers are done
                    is_nested = self._parent_manager is not None
                    if is_nested:
                        # Nested manager - notify root that we're done
                        # Find root manager
                        root_manager = self._parent_manager
                        while root_manager._parent_manager is not None:
                            root_manager = root_manager._parent_manager
                        if hasattr(root_manager, '_on_nested_manager_complete'):
                            root_manager._on_nested_manager_complete(self)
                    else:
                        # Root manager - check if all nested managers are done
                        if len(self._pending_nested_managers) == 0:
                            # STEP 1: Apply all styling callbacks now that ALL widgets exist
                            with timer(f"  Apply styling callbacks", threshold_ms=5.0):
                                self._apply_all_styling_callbacks()

                            # STEP 2: Refresh placeholders for ALL widgets (including initial sync widgets)
                            # CRITICAL: Use _refresh_with_live_context() to collect live values from other open windows
                            # This ensures new windows immediately show unsaved changes from already-open windows
                            with timer(f"  Complete placeholder refresh with live context (all widgets ready)", threshold_ms=10.0):
                                self._refresh_with_live_context()

                # Create remaining widgets asynchronously
                if async_params:
                    self._create_widgets_async(content_layout, async_params, on_complete=on_async_complete)
                else:
                    # All widgets were created synchronously, call completion immediately
                    on_async_complete()
        else:
            # Sync widget creation for small forms (<=5 parameters)
            with timer(f"      Create {len(self.form_structure.parameters)} parameter widgets", threshold_ms=5.0):
                for param_info in self.form_structure.parameters:
                    with timer(f"        Create widget for {param_info.name} ({'nested' if param_info.is_nested else 'regular'})", threshold_ms=2.0):
                        widget = self._create_widget_for_param(param_info)
                        content_layout.addWidget(widget)

            # For sync creation, apply styling callbacks and refresh placeholders
            # CRITICAL: Order matters - placeholders must be resolved before enabled styling
            is_nested = self._parent_manager is not None
            if not is_nested:
                # STEP 1: Apply styling callbacks (optional dataclass None-state dimming)
                with timer("  Apply styling callbacks (sync)", threshold_ms=5.0):
                    for callback in self._on_build_complete_callbacks:
                        callback()
                    self._on_build_complete_callbacks.clear()

                # STEP 2: Refresh placeholders (resolve inherited values)
                # CRITICAL: Use _refresh_with_live_context() to collect live values from other open windows
                # This ensures new windows immediately show unsaved changes from already-open windows
                with timer("  Initial placeholder refresh with live context (sync)", threshold_ms=10.0):
                    self._refresh_with_live_context()

                # STEP 3: Apply post-placeholder callbacks (enabled styling that needs resolved values)
                with timer("  Apply post-placeholder callbacks (sync)", threshold_ms=5.0):
                    for callback in self._on_placeholder_refresh_complete_callbacks:
                        callback()
                    self._on_placeholder_refresh_complete_callbacks.clear()
                    # Also apply for nested managers
                    self._apply_to_nested_managers(lambda name, manager: manager._apply_all_post_placeholder_callbacks())

                # STEP 4: Refresh enabled styling (after placeholders are resolved)
                with timer("  Enabled styling refresh (sync)", threshold_ms=5.0):
                    self._apply_to_nested_managers(lambda name, manager: manager._refresh_enabled_styling())
            else:
                # Nested managers just apply their callbacks
                for callback in self._on_build_complete_callbacks:
                    callback()
                self._on_build_complete_callbacks.clear()

        return content_widget

    def _create_widget_for_param(self, param_info):
        """Create widget for a single parameter based on its type."""
        if param_info.is_optional and param_info.is_nested:
            # Optional[Dataclass]: show checkbox
            return self._create_optional_dataclass_widget(param_info)
        elif param_info.is_nested:
            # Direct dataclass (non-optional): nested group without checkbox
            return self._create_nested_dataclass_widget(param_info)
        else:
            # All regular types (including Optional[regular]) use regular widgets with None-aware behavior
            return self._create_regular_parameter_widget(param_info)

    def _create_widgets_async(self, layout, param_infos, on_complete=None):
        """Create widgets asynchronously to avoid blocking the UI.

        Args:
            layout: Layout to add widgets to
            param_infos: List of parameter info objects
            on_complete: Optional callback to run when all widgets are created
        """
        # Create widgets in batches using QTimer to yield to event loop
        batch_size = 3  # Create 3 widgets at a time
        index = 0

        def create_next_batch():
            nonlocal index
            batch_end = min(index + batch_size, len(param_infos))

            for i in range(index, batch_end):
                param_info = param_infos[i]
                widget = self._create_widget_for_param(param_info)
                layout.addWidget(widget)

            index = batch_end

            # Schedule next batch if there are more widgets
            if index < len(param_infos):
                QTimer.singleShot(0, create_next_batch)
            elif on_complete:
                # All widgets created - defer completion callback to next event loop tick
                # This ensures Qt has processed all layout updates and widgets are findable
                QTimer.singleShot(0, on_complete)

        # Start creating widgets
        QTimer.singleShot(0, create_next_batch)

    def _create_regular_parameter_widget(self, param_info) -> QWidget:
        """Create widget for regular parameter - DELEGATE TO SERVICE LAYER."""
        from openhcs.utils.performance_monitor import timer

        with timer(f"          Get display info for {param_info.name}", threshold_ms=0.5):
            display_info = self.service.get_parameter_display_info(param_info.name, param_info.type, param_info.description)
            field_ids = self.service.generate_field_ids_direct(self.config.field_id, param_info.name)

        with timer("          Create container/layout", threshold_ms=0.5):
            container = QWidget()
            layout = QHBoxLayout(container)
            layout.setSpacing(CURRENT_LAYOUT.parameter_row_spacing)
            layout.setContentsMargins(*CURRENT_LAYOUT.parameter_row_margins)

        # Label
        with timer(f"          Create label for {param_info.name}", threshold_ms=0.5):
            label = LabelWithHelp(
                text=display_info['field_label'], param_name=param_info.name,
                param_description=display_info['description'], param_type=param_info.type,
                color_scheme=self.config.color_scheme or PyQt6ColorScheme()
            )
            layout.addWidget(label)

        # Widget
        with timer(f"          Create actual widget for {param_info.name}", threshold_ms=0.5):
            current_value = self.parameters.get(param_info.name)
            widget = self.create_widget(param_info.name, param_info.type, current_value, field_ids['widget_id'])
            widget.setObjectName(field_ids['widget_id'])
            layout.addWidget(widget, 1)

        # Reset button (optimized factory) - skip if read-only
        if not self.read_only:
            with timer("          Create reset button", threshold_ms=0.5):
                reset_button = _create_optimized_reset_button(
                    self.config.field_id,
                    param_info.name,
                    lambda: self.reset_parameter(param_info.name)
                )
                layout.addWidget(reset_button)
                self.reset_buttons[param_info.name] = reset_button

        # Store widgets and connect signals
        with timer("          Store and connect signals", threshold_ms=0.5):
            self.widgets[param_info.name] = widget
            PyQt6WidgetEnhancer.connect_change_signal(widget, param_info.name, self._emit_parameter_change)

        # PERFORMANCE OPTIMIZATION: Don't apply context behavior during widget creation
        # The completion callback (_refresh_all_placeholders) will handle it when all widgets exist
        # This eliminates 400+ expensive calls with incomplete context during async creation
        # and fixes the wrong placeholder bug (context is complete at the end)

        # Make widget read-only if in read-only mode
        if self.read_only:
            self._make_widget_readonly(widget)

        return container

    def _create_optional_regular_widget(self, param_info) -> QWidget:
        """Create widget for Optional[regular_type] - checkbox + regular widget."""
        display_info = self.service.get_parameter_display_info(param_info.name, param_info.type, param_info.description)
        field_ids = self.service.generate_field_ids_direct(self.config.field_id, param_info.name)

        container = QWidget()
        layout = QVBoxLayout(container)

        # Checkbox (using NoneAwareCheckBox for consistency)
        from openhcs.pyqt_gui.widgets.shared.no_scroll_spinbox import NoneAwareCheckBox
        checkbox = NoneAwareCheckBox()
        checkbox.setText(display_info['checkbox_label'])
        checkbox.setObjectName(field_ids['optional_checkbox_id'])
        current_value = self.parameters.get(param_info.name)
        checkbox.setChecked(current_value is not None)
        layout.addWidget(checkbox)

        # Get inner type for the actual widget
        inner_type = ParameterTypeUtils.get_optional_inner_type(param_info.type)

        # Create the actual widget for the inner type
        inner_widget = self._create_regular_parameter_widget_for_type(param_info.name, inner_type, current_value)
        inner_widget.setEnabled(current_value is not None)  # Disable if None
        layout.addWidget(inner_widget)

        # Connect checkbox to enable/disable the inner widget
        def on_checkbox_changed(checked):
            inner_widget.setEnabled(checked)
            if checked:
                # Set to default value for the inner type
                if inner_type == str:
                    default_value = ""
                elif inner_type == int:
                    default_value = 0
                elif inner_type == float:
                    default_value = 0.0
                elif inner_type == bool:
                    default_value = False
                else:
                    default_value = None
                self.update_parameter(param_info.name, default_value)
            else:
                self.update_parameter(param_info.name, None)

        checkbox.toggled.connect(on_checkbox_changed)
        return container

    def _create_regular_parameter_widget_for_type(self, param_name: str, param_type: Type, current_value: Any) -> QWidget:
        """Create a regular parameter widget for a specific type."""
        field_ids = self.service.generate_field_ids_direct(self.config.field_id, param_name)

        # Use the existing create_widget method
        widget = self.create_widget(param_name, param_type, current_value, field_ids['widget_id'])
        if widget:
            return widget

        # Fallback to basic text input
        from PyQt6.QtWidgets import QLineEdit
        fallback_widget = QLineEdit()
        fallback_widget.setText(str(current_value or ""))
        fallback_widget.setObjectName(field_ids['widget_id'])
        return fallback_widget

    def _create_nested_dataclass_widget(self, param_info) -> QWidget:
        """Create widget for nested dataclass - DELEGATE TO SERVICE LAYER."""
        display_info = self.service.get_parameter_display_info(param_info.name, param_info.type, param_info.description)

        # Always use the inner dataclass type for Optional[T] when wiring help/paths
        unwrapped_type = (
            ParameterTypeUtils.get_optional_inner_type(param_info.type)
            if ParameterTypeUtils.is_optional_dataclass(param_info.type)
            else param_info.type
        )

        group_box = GroupBoxWithHelp(
            title=display_info['field_label'], help_target=unwrapped_type,
            color_scheme=self.config.color_scheme or PyQt6ColorScheme()
        )
        current_value = self.parameters.get(param_info.name)
        nested_manager = self._create_nested_form_inline(param_info.name, unwrapped_type, current_value)

        nested_form = nested_manager.build_form()

        # Add Reset All button to GroupBox title
        if not self.read_only:
            from PyQt6.QtWidgets import QPushButton
            reset_all_button = QPushButton("Reset All")
            reset_all_button.setMaximumWidth(80)
            reset_all_button.setToolTip(f"Reset all parameters in {display_info['field_label']} to defaults")
            reset_all_button.clicked.connect(lambda: nested_manager.reset_all_parameters())
            group_box.addTitleWidget(reset_all_button)

        # Use GroupBoxWithHelp's addWidget method instead of creating our own layout
        group_box.addWidget(nested_form)

        self.nested_managers[param_info.name] = nested_manager

        # CRITICAL: Store the GroupBox in self.widgets so enabled handler can find it
        self.widgets[param_info.name] = group_box

        return group_box

    def _create_optional_dataclass_widget(self, param_info) -> QWidget:
        """Create widget for optional dataclass - checkbox integrated into GroupBox title."""
        display_info = self.service.get_parameter_display_info(param_info.name, param_info.type, param_info.description)
        field_ids = self.service.generate_field_ids_direct(self.config.field_id, param_info.name)

        # Get the unwrapped type for the GroupBox
        unwrapped_type = ParameterTypeUtils.get_optional_inner_type(param_info.type)

        # Create GroupBox with custom title widget that includes checkbox
        from PyQt6.QtGui import QFont
        group_box = QGroupBox()

        # Create custom title widget with checkbox + title + help button (all inline)
        title_widget = QWidget()
        title_layout = QHBoxLayout(title_widget)
        title_layout.setSpacing(5)
        title_layout.setContentsMargins(10, 5, 10, 5)

        # Checkbox (compact, no text)
        from openhcs.pyqt_gui.widgets.shared.no_scroll_spinbox import NoneAwareCheckBox
        checkbox = NoneAwareCheckBox()
        checkbox.setObjectName(field_ids['optional_checkbox_id'])
        current_value = self.parameters.get(param_info.name)
        # CRITICAL: Title checkbox ONLY controls None vs Instance, NOT the enabled field
        # Checkbox is checked if config exists (regardless of enabled field value)
        checkbox.setChecked(current_value is not None)
        checkbox.setMaximumWidth(20)
        title_layout.addWidget(checkbox)

        # Title label (clickable to toggle checkbox, matches GroupBoxWithHelp styling)
        title_label = QLabel(display_info['checkbox_label'])
        title_font = QFont()
        title_font.setBold(True)
        title_label.setFont(title_font)
        title_label.mousePressEvent = lambda e: checkbox.toggle()
        title_label.setCursor(Qt.CursorShape.PointingHandCursor)
        title_layout.addWidget(title_label)

        title_layout.addStretch()

        # Reset All button (before help button)
        if not self.read_only:
            from PyQt6.QtWidgets import QPushButton
            reset_all_button = QPushButton("Reset")
            reset_all_button.setMaximumWidth(60)
            reset_all_button.setFixedHeight(20)
            reset_all_button.setToolTip(f"Reset all parameters in {display_info['checkbox_label']} to defaults")
            # Will be connected after nested_manager is created
            title_layout.addWidget(reset_all_button)

        # Help button (matches GroupBoxWithHelp)
        from openhcs.pyqt_gui.widgets.shared.clickable_help_components import HelpButton
        help_btn = HelpButton(help_target=unwrapped_type, text="?", color_scheme=self.color_scheme)
        help_btn.setMaximumWidth(25)
        help_btn.setMaximumHeight(20)
        title_layout.addWidget(help_btn)

        # Set the custom title widget as the GroupBox title
        group_box.setLayout(QVBoxLayout())
        group_box.layout().setSpacing(0)
        group_box.layout().setContentsMargins(0, 0, 0, 0)
        group_box.layout().addWidget(title_widget)

        # Create nested form
        nested_manager = self._create_nested_form_inline(param_info.name, unwrapped_type, current_value)
        nested_form = nested_manager.build_form()
        nested_form.setEnabled(current_value is not None)
        group_box.layout().addWidget(nested_form)

        self.nested_managers[param_info.name] = nested_manager

        # Connect reset button to nested manager's reset_all_parameters
        if not self.read_only:
            reset_all_button.clicked.connect(lambda: nested_manager.reset_all_parameters())

        # Connect checkbox to enable/disable with visual feedback
        def on_checkbox_changed(checked):
            # Title checkbox controls whether config exists (None vs instance)
            # When checked: config exists, inputs are editable
            # When unchecked: config is None, inputs are blocked
            # CRITICAL: This is INDEPENDENT of the enabled field - they both use similar visual styling but are separate concepts
            nested_form.setEnabled(checked)

            if checked:
                # Config exists - create instance preserving the enabled field value
                current_param_value = self.parameters.get(param_info.name)
                if current_param_value is None:
                    # Create new instance with default enabled value (from dataclass default)
                    new_instance = unwrapped_type()
                    self.update_parameter(param_info.name, new_instance)
                else:
                    # Instance already exists, no need to modify it
                    pass

                # Remove dimming for None state (title only)
                # CRITICAL: Don't clear graphics effects on nested form widgets - let enabled field handler manage them
                title_label.setStyleSheet("")
                help_btn.setEnabled(True)

                # CRITICAL: Trigger the nested config's enabled handler to apply enabled styling
                # This ensures that when toggling from None to Instance, the enabled styling is applied
                # based on the instance's enabled field value
                if hasattr(nested_manager, '_apply_initial_enabled_styling'):
                    from PyQt6.QtCore import QTimer
                    QTimer.singleShot(0, nested_manager._apply_initial_enabled_styling)
            else:
                # Config is None - set to None and block inputs
                self.update_parameter(param_info.name, None)

                # Apply dimming for None state
                title_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_disabled)};")
                help_btn.setEnabled(True)
                from PyQt6.QtWidgets import QGraphicsOpacityEffect
                for widget in nested_form.findChildren(ALL_INPUT_WIDGET_TYPES):
                    effect = QGraphicsOpacityEffect()
                    effect.setOpacity(0.4)
                    widget.setGraphicsEffect(effect)

        checkbox.toggled.connect(on_checkbox_changed)

        # NOTE: Enabled field styling is now handled by the universal _on_enabled_field_changed_universal handler
        # which is connected in __init__ for any form that has an 'enabled' parameter

        # Apply initial styling after nested form is fully constructed
        # CRITICAL FIX: Only register callback, don't call immediately
        # Calling immediately schedules QTimer callbacks that block async widget creation
        # The callback will be triggered after all async batches complete
        def apply_initial_styling():
            # Apply styling directly without QTimer delay
            # The callback is already deferred by the async completion mechanism
            on_checkbox_changed(checkbox.isChecked())

        # Register callback with parent manager (will be called after all widgets are created)
        self._on_build_complete_callbacks.append(apply_initial_styling)

        self.widgets[param_info.name] = group_box
        return group_box









    def _create_nested_form_inline(self, param_name: str, param_type: Type, current_value: Any) -> Any:
        """Create nested form - simplified to let constructor handle parameter extraction"""
        # Get actual field path from FieldPathDetector (no artificial "nested_" prefix)
        # For function parameters (no parent dataclass), use parameter name directly
        if self.dataclass_type is None:
            field_path = param_name
        else:
            field_path = self.service.get_field_path_with_fail_loud(self.dataclass_type, param_type)

        # Use current_value if available, otherwise create a default instance of the dataclass type
        # The constructor will handle parameter extraction automatically
        if current_value is not None:
            # If current_value is a dict (saved config), convert it back to dataclass instance
            import dataclasses
            # Unwrap Optional type to get actual dataclass type
            from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
            actual_type = ParameterTypeUtils.get_optional_inner_type(param_type) if ParameterTypeUtils.is_optional(param_type) else param_type

            if isinstance(current_value, dict) and dataclasses.is_dataclass(actual_type):
                # Convert dict back to dataclass instance
                object_instance = actual_type(**current_value)
            else:
                object_instance = current_value
        else:
            # Create a default instance of the dataclass type for parameter extraction
            import dataclasses
            # Unwrap Optional type to get actual dataclass type
            from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
            actual_type = ParameterTypeUtils.get_optional_inner_type(param_type) if ParameterTypeUtils.is_optional(param_type) else param_type

            if dataclasses.is_dataclass(actual_type):
                object_instance = actual_type()
            else:
                object_instance = actual_type

        # DELEGATE TO NEW CONSTRUCTOR: Use simplified constructor
        nested_manager = ParameterFormManager(
            object_instance=object_instance,
            field_id=field_path,
            parent=self,
            context_obj=self.context_obj,
            parent_manager=self  # Pass parent manager so setup_ui() can detect nested configs
        )
        # Inherit lazy/global editing context from parent so resets behave correctly in nested forms
        try:
            nested_manager.config.is_lazy_dataclass = self.config.is_lazy_dataclass
            nested_manager.config.is_global_config_editing = not self.config.is_lazy_dataclass
        except Exception:
            pass

        # Connect nested manager's parameter_changed signal to parent's refresh handler
        # This ensures changes in nested forms trigger placeholder updates in parent and siblings
        nested_manager.parameter_changed.connect(self._on_nested_parameter_changed)

        # Store nested manager
        self.nested_managers[param_name] = nested_manager

        # CRITICAL: Register with root manager if it's tracking async completion
        # Only register if this nested manager will use async widget creation
        # Use centralized logic to determine if async will be used
        import dataclasses
        from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
        actual_type = ParameterTypeUtils.get_optional_inner_type(param_type) if ParameterTypeUtils.is_optional(param_type) else param_type
        if dataclasses.is_dataclass(actual_type):
            param_count = len(dataclasses.fields(actual_type))

            # Find root manager
            root_manager = self
            while root_manager._parent_manager is not None:
                root_manager = root_manager._parent_manager

            # Register with root if it's tracking and this will use async (centralized logic)
            if self.should_use_async(param_count) and hasattr(root_manager, '_pending_nested_managers'):
                # Use a unique key that includes the full path to avoid duplicates
                unique_key = f"{self.field_id}.{param_name}"
                root_manager._pending_nested_managers[unique_key] = nested_manager

        return nested_manager



    def _convert_widget_value(self, value: Any, param_name: str) -> Any:
        """
        Convert widget value to proper type.

        Applies both PyQt-specific conversions (Path, tuple/list parsing) and
        service layer conversions (enums, basic types, Union handling).
        """
        from openhcs.pyqt_gui.widgets.shared.widget_strategies import convert_widget_value_to_type

        param_type = self.parameter_types.get(param_name, type(value))

        # PyQt-specific type conversions first (pass param_name for field-specific handling)
        converted_value = convert_widget_value_to_type(value, param_type, param_name)

        # Then apply service layer conversion (enums, basic types, Union handling, etc.)
        converted_value = self.service.convert_value_to_type(converted_value, param_type, param_name, self.dataclass_type)

        return converted_value

    def _store_parameter_value(self, param_name: str, value: Any) -> None:
        """Update parameter model and corresponding cached value."""
        self.parameters[param_name] = value
        self._current_value_cache[param_name] = value
        if value is None:
            self._placeholder_candidates.add(param_name)
        else:
            self._placeholder_candidates.discard(param_name)

    def _emit_parameter_change(self, param_name: str, value: Any) -> None:
        """Handle parameter change from widget and update parameter data model."""

        # Convert value using unified conversion method
        converted_value = self._convert_widget_value(value, param_name)

        # Update parameter in data model
        self._store_parameter_value(param_name, converted_value)

        # CRITICAL FIX: Track that user explicitly set this field
        # This prevents placeholder updates from destroying user values
        self._user_set_fields.add(param_name)

        # Emit signal only once - this triggers sibling placeholder updates
        self.parameter_changed.emit(param_name, converted_value)



    def update_widget_value(self, widget: QWidget, value: Any, param_name: str = None, skip_context_behavior: bool = False, exclude_field: str = None) -> None:
        """Mathematical simplification: Unified widget update using shared dispatch."""
        self._execute_with_signal_blocking(widget, lambda: self._dispatch_widget_update(widget, value))

        # Only apply context behavior if not explicitly skipped (e.g., during reset operations)
        if not skip_context_behavior:
            self._apply_context_behavior(widget, value, param_name, exclude_field)

    def _dispatch_widget_update(self, widget: QWidget, value: Any) -> None:
        """Type-based dispatch for widget updates - NO duck typing."""
        for matcher, updater in WIDGET_UPDATE_DISPATCH:
            # Type-based matching only
            if isinstance(matcher, type):
                if isinstance(widget, matcher):
                    if isinstance(updater, str):
                        getattr(self, f'_{updater}')(widget, value)
                    else:
                        updater(widget, value)
                    return
            elif isinstance(matcher, str):
                # Forward reference to class defined later in this file
                if type(widget).__name__ == matcher:
                    updater(widget, value)
                    return

    def _clear_widget_to_default_state(self, widget: QWidget) -> None:
        """Clear widget to its default/empty state for reset operations."""
        from PyQt6.QtWidgets import QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox, QTextEdit

        if isinstance(widget, QLineEdit):
            widget.clear()
        elif isinstance(widget, (QSpinBox, QDoubleSpinBox)):
            widget.setValue(widget.minimum())
        elif isinstance(widget, QComboBox):
            widget.setCurrentIndex(-1)  # No selection
        elif isinstance(widget, QCheckBox):
            widget.setChecked(False)
        elif isinstance(widget, QTextEdit):
            widget.clear()
        else:
            # For custom widgets, try to call clear() if available
            if hasattr(widget, 'clear'):
                widget.clear()

    def _update_combo_box(self, widget: QComboBox, value: Any) -> None:
        """Update combo box with value matching."""
        widget.setCurrentIndex(-1 if value is None else
                             next((i for i in range(widget.count()) if widget.itemData(i) == value), -1))

    def _update_checkbox_group(self, widget: QWidget, value: Any) -> None:
        """Update checkbox group using set_value() pattern for proper placeholder handling.

        CRITICAL: Block signals on ALL checkboxes to prevent race conditions.
        Without signal blocking, set_value() triggers stateChanged signals which
        fire the user click handler, creating an infinite loop.
        """
        import traceback

        if not hasattr(widget, '_checkboxes'):
            return

        # CRITICAL: Block signals on ALL checkboxes before updating
        for checkbox in widget._checkboxes.values():
            checkbox.blockSignals(True)

        try:
            if value is None:
                # None means inherit from parent - set all checkboxes to placeholder state
                for checkbox in widget._checkboxes.values():
                    checkbox.set_value(None)
            elif isinstance(value, list):
                # Explicit list - set concrete values using set_value()
                for enum_val, checkbox in widget._checkboxes.items():
                    checkbox.set_value(enum_val in value)
        finally:
            # CRITICAL: Always unblock signals, even if there's an exception
            for checkbox in widget._checkboxes.values():
                checkbox.blockSignals(False)

    def _execute_with_signal_blocking(self, widget: QWidget, operation: callable) -> None:
        """Execute operation with signal blocking - stateless utility."""
        widget.blockSignals(True)
        operation()
        widget.blockSignals(False)

    def _apply_context_behavior(self, widget: QWidget, value: Any, param_name: str, exclude_field: str = None) -> None:
        """CONSOLIDATED: Apply placeholder behavior using single resolution path."""
        if not param_name or not self.dataclass_type:
            return

        if value is None:
            # Allow placeholder application for nested forms even if they're not detected as lazy dataclasses
            # The placeholder service will determine if placeholders are available

            # Build overlay from current form state
            overlay = self.get_current_values()

            # Build context stack: parent context + overlay
            with self._build_context_stack(overlay):
                placeholder_text = self.service.get_placeholder_text(param_name, self.dataclass_type)
                if placeholder_text:
                    PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
        elif value is not None:
            PyQt6WidgetEnhancer._clear_placeholder_state(widget)


    def get_widget_value(self, widget: QWidget) -> Any:
        """Type-based dispatch for widget value extraction - NO duck typing."""
        # CRITICAL: Check if widget is in placeholder state first
        # If it's showing a placeholder, the actual parameter value is None
        if widget.property("is_placeholder_state"):
            return None

        for matcher, extractor in WIDGET_GET_DISPATCH:
            # Type-based matching only
            if isinstance(matcher, type):
                if isinstance(widget, matcher):
                    return extractor(widget)
            elif isinstance(matcher, str):
                # Forward reference to class defined later in this file
                if type(widget).__name__ == matcher:
                    return extractor(widget)
        return None

    # Framework-specific methods for backward compatibility

    def reset_all_parameters(self) -> None:
        """Reset all parameters - just call reset_parameter for each parameter."""
        from openhcs.utils.performance_monitor import timer

        logger.info(f"🔍 reset_all_parameters CALLED for {self.field_id}, parent={self._parent_manager.field_id if self._parent_manager else 'None'}")
        with timer(f"reset_all_parameters ({self.field_id})", threshold_ms=50.0):
            # OPTIMIZATION: Set flag to prevent per-parameter refreshes
            # This makes reset_all much faster by batching all refreshes to the end
            self._in_reset = True

            # OPTIMIZATION: Block cross-window updates during reset
            # This prevents expensive _collect_live_context_from_other_windows() calls
            # during the reset operation. We'll do a single refresh at the end.
            self._block_cross_window_updates = True

            try:
                param_names = list(self.parameters.keys())
                for param_name in param_names:
                    # Call _reset_parameter_impl directly to avoid setting/clearing _in_reset per parameter
                    self._reset_parameter_impl(param_name)
            finally:
                self._in_reset = False
                self._block_cross_window_updates = False

            # CRITICAL: Increment global token after reset to invalidate caches
            # Reset changes values, so other windows need to know their cached context is stale
            type(self)._live_context_token_counter += 1

            # CRITICAL: Emit cross-window signals for all reset fields
            # The _block_cross_window_updates flag blocked normal parameter_changed handlers,
            # so we must emit manually for each field that was reset
            # This ensures external listeners (like PipelineEditor) see the reset changes
            if self._parent_manager is None:
                # Root manager: emit directly for each field
                for param_name in param_names:
                    reset_value = self.parameters.get(param_name)
                    field_path = f"{self.field_id}.{param_name}"
                    self.context_value_changed.emit(field_path, reset_value,
                                                   self.object_instance, self.context_obj)
            else:
                # Nested manager: build full path and emit from root for each field
                root = self._parent_manager
                while root._parent_manager is not None:
                    root = root._parent_manager

                for param_name in param_names:
                    reset_value = self.parameters.get(param_name)

                    # Build full field path by walking up the parent chain
                    path_parts = [param_name]
                    current = self
                    while current._parent_manager is not None:
                        # Find this manager's parameter name in the parent's nested_managers dict
                        parent_param_name = None
                        for pname, manager in current._parent_manager.nested_managers.items():
                            if manager is current:
                                parent_param_name = pname
                                break
                        if parent_param_name:
                            path_parts.insert(0, parent_param_name)
                        current = current._parent_manager

                    # Prepend root field_id
                    path_parts.insert(0, root.field_id)
                    field_path = '.'.join(path_parts)

                    # Emit from root with root's object instance
                    root.context_value_changed.emit(field_path, reset_value,
                                                   root.object_instance, root.context_obj)

            # OPTIMIZATION: Single placeholder refresh at the end instead of per-parameter
            # This is much faster than refreshing after each reset
            # CRITICAL: Use _refresh_with_live_context() to collect live values from other open windows
            # Reset should show inherited values from parent contexts, including unsaved changes
            # CRITICAL: Nested managers must trigger refresh on ROOT manager to collect live context
            if self._parent_manager is None:
                logger.info(f"🔍 reset_all_parameters: ROOT manager {self.field_id}, refreshing and notifying external listeners")
                self._refresh_with_live_context()
                # CRITICAL: Also refresh enabled styling for nested managers after reset
                # This ensures optional dataclass fields respect None/not-None and enabled=True/False states
                # Example: Reset optional dataclass to None → nested fields should be dimmed
                self._apply_to_nested_managers(lambda name, manager: manager._refresh_enabled_styling())
                # CRITICAL: Emit context_refreshed signal to trigger cross-window updates
                # This tells other open windows to refresh their placeholders with the reset values
                # Example: Reset PipelineConfig → Step editors refresh to show reset inherited values
                self.context_refreshed.emit(self.object_instance, self.context_obj)
                # CRITICAL: Also notify external listeners directly (e.g., PipelineEditor)
                self._notify_external_listeners_refreshed()
            else:
                # Nested manager: trigger refresh on root manager
                logger.info(f"🔍 reset_all_parameters: NESTED manager {self.field_id}, finding root and notifying external listeners")
                root = self._parent_manager
                while root._parent_manager is not None:
                    root = root._parent_manager
                logger.info(f"🔍 reset_all_parameters: Found root manager {root.field_id}")
                root._refresh_with_live_context()
                # CRITICAL: Also refresh enabled styling for root's nested managers
                root._apply_to_nested_managers(lambda name, manager: manager._refresh_enabled_styling())
                # CRITICAL: Emit from root manager to trigger cross-window updates
                root.context_refreshed.emit(root.object_instance, root.context_obj)
                # CRITICAL: Also notify external listeners directly (e.g., PipelineEditor)
                logger.info(f"🔍 reset_all_parameters: About to call root._notify_external_listeners_refreshed()")
                root._notify_external_listeners_refreshed()



    def update_parameter(self, param_name: str, value: Any) -> None:
        """Update parameter value using shared service layer."""

        if param_name in self.parameters:
            # Convert value using service layer
            converted_value = self.service.convert_value_to_type(value, self.parameter_types.get(param_name, type(value)), param_name, self.dataclass_type)

            # Update parameter in data model
            self._store_parameter_value(param_name, converted_value)

            # CRITICAL FIX: Track that user explicitly set this field
            # This prevents placeholder updates from destroying user values
            self._user_set_fields.add(param_name)

            # Update corresponding widget if it exists
            if param_name in self.widgets:
                self.update_widget_value(self.widgets[param_name], converted_value, param_name=param_name)

            # Emit signal for PyQt6 compatibility
            # This will trigger both local placeholder refresh AND cross-window updates (via _emit_cross_window_change)
            self.parameter_changed.emit(param_name, converted_value)

    def _is_function_parameter(self, param_name: str) -> bool:
        """
        Detect if parameter is a function parameter vs dataclass field.

        Function parameters should not be reset against dataclass types.
        This prevents the critical bug where step editor tries to reset
        function parameters like 'group_by' against the global config type.
        """
        if not self.function_target or not self.dataclass_type:
            return False

        # Check if parameter exists in dataclass fields
        if dataclasses.is_dataclass(self.dataclass_type):
            field_names = {field.name for field in dataclasses.fields(self.dataclass_type)}
            is_function_param = param_name not in field_names
            return is_function_param

        return False

    def reset_parameter(self, param_name: str) -> None:
        """Reset parameter to signature default."""
        if param_name not in self.parameters:
            return

        # Set flag to prevent automatic refresh during reset
        # CRITICAL: Keep _in_reset=True until AFTER manual refresh to prevent
        # queued parameter_changed signals from triggering automatic refresh
        self._in_reset = True
        try:
            self._reset_parameter_impl(param_name)

            # CRITICAL: Increment global token after reset to invalidate caches
            # Reset changes values, so other windows need to know their cached context is stale
            type(self)._live_context_token_counter += 1

            # CRITICAL: Emit cross-window signal for reset
            # The _in_reset flag blocks normal parameter_changed handlers, so we must emit manually
            reset_value = self.parameters.get(param_name)
            if self._parent_manager is None:
                # Root manager: emit directly
                field_path = f"{self.field_id}.{param_name}"
                self.context_value_changed.emit(field_path, reset_value,
                                               self.object_instance, self.context_obj)
            else:
                # Nested manager: build full path and emit from root
                root = self._parent_manager
                while root._parent_manager is not None:
                    root = root._parent_manager

                # Build full field path by walking up the parent chain
                path_parts = [param_name]
                current = self
                while current._parent_manager is not None:
                    # Find this manager's parameter name in the parent's nested_managers dict
                    parent_param_name = None
                    for pname, manager in current._parent_manager.nested_managers.items():
                        if manager is current:
                            parent_param_name = pname
                            break
                    if parent_param_name:
                        path_parts.insert(0, parent_param_name)
                    current = current._parent_manager

                # Prepend root field_id
                path_parts.insert(0, root.field_id)
                field_path = '.'.join(path_parts)

                # Emit from root with root's object instance
                root.context_value_changed.emit(field_path, reset_value,
                                               root.object_instance, root.context_obj)

            # CRITICAL: Manually refresh placeholders BEFORE clearing _in_reset
            # This ensures queued parameter_changed signals don't trigger automatic refresh
            # This matches the behavior of reset_all_parameters() which also refreshes before clearing flag
            # CRITICAL: Use _refresh_with_live_context() to collect live values from other open windows
            # Reset should show inherited values from parent contexts, including unsaved changes
            # CRITICAL: Nested managers must trigger refresh on ROOT manager to collect live context
            if self._parent_manager is None:
                self._refresh_with_live_context()
                # CRITICAL: Also notify external listeners directly (e.g., PipelineEditor)
                self._notify_external_listeners_refreshed()
            else:
                # Nested manager: trigger refresh on root manager
                root = self._parent_manager
                while root._parent_manager is not None:
                    root = root._parent_manager
                root._refresh_with_live_context()
                # CRITICAL: Also notify external listeners directly (e.g., PipelineEditor)
                root._notify_external_listeners_refreshed()
        finally:
            self._in_reset = False

    def _reset_parameter_impl(self, param_name: str) -> None:
        """Internal reset implementation."""

        # Function parameters reset to static defaults from param_defaults
        if self._is_function_parameter(param_name):
            reset_value = self.param_defaults.get(param_name)
            self._store_parameter_value(param_name, reset_value)

            if param_name in self.widgets:
                widget = self.widgets[param_name]
                self.update_widget_value(widget, reset_value, param_name, skip_context_behavior=True)

            self.parameter_changed.emit(param_name, reset_value)
            return

        # Special handling for dataclass fields
        try:
            import dataclasses as _dc
            from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
            param_type = self.parameter_types.get(param_name)

            # If this is an Optional[Dataclass], sync container UI and reset nested manager
            if param_type and ParameterTypeUtils.is_optional_dataclass(param_type):
                reset_value = self._get_reset_value(param_name)
                self._store_parameter_value(param_name, reset_value)

                if param_name in self.widgets:
                    container = self.widgets[param_name]
                    # Toggle the optional checkbox to match reset_value (None -> unchecked, enabled=False -> unchecked)
                    from PyQt6.QtWidgets import QCheckBox
                    ids = self.service.generate_field_ids_direct(self.config.field_id, param_name)
                    checkbox = container.findChild(QCheckBox, ids['optional_checkbox_id'])
                    if checkbox:
                        checkbox.blockSignals(True)
                        checkbox.setChecked(reset_value is not None and reset_value.enabled)
                        checkbox.blockSignals(False)

                # Reset nested manager contents too
                nested_manager = self.nested_managers.get(param_name)
                if nested_manager and hasattr(nested_manager, 'reset_all_parameters'):
                    nested_manager.reset_all_parameters()

                # Enable/disable the nested group visually without relying on signals
                try:
                    from .clickable_help_components import GroupBoxWithHelp
                    group = container.findChild(GroupBoxWithHelp) if param_name in self.widgets else None
                    if group:
                        group.setEnabled(reset_value is not None)
                except Exception:
                    pass

                # Emit parameter change and return (handled)
                self.parameter_changed.emit(param_name, reset_value)
                return

            # If this is a direct dataclass field (non-optional), do NOT replace the instance.
            # Instead, keep the container value and recursively reset the nested manager.
            if param_type and _dc.is_dataclass(param_type):
                nested_manager = self.nested_managers.get(param_name)
                if nested_manager and hasattr(nested_manager, 'reset_all_parameters'):
                    nested_manager.reset_all_parameters()
                # Do not modify self.parameters[param_name] (keep current dataclass instance)
                # Refresh placeholder on the group container if it has a widget
                if param_name in self.widgets:
                    self._apply_context_behavior(self.widgets[param_name], None, param_name)
                # Emit parameter change with unchanged container value
                self.parameter_changed.emit(param_name, self.parameters.get(param_name))
                return
        except Exception:
            # Fall through to generic handling if type checks fail
            pass

        # Generic config field reset - use context-aware reset value
        reset_value = self._get_reset_value(param_name)
        self._store_parameter_value(param_name, reset_value)
        if param_name in self._user_set_fields:
            self._user_set_fields.discard(param_name)

        # Track reset fields only for lazy behavior (when reset_value is None)
        if reset_value is None:
            self.reset_fields.add(param_name)
            # SHARED RESET STATE: Also add to shared reset state for coordination with nested managers
            field_path = f"{self.field_id}.{param_name}"
            self.shared_reset_fields.add(field_path)
        else:
            # For concrete values, remove from reset tracking
            self.reset_fields.discard(param_name)
            field_path = f"{self.field_id}.{param_name}"
            self.shared_reset_fields.discard(field_path)

        # Update widget with reset value
        if param_name in self.widgets:
            widget = self.widgets[param_name]
            self.update_widget_value(widget, reset_value, param_name)

            # Apply placeholder only if reset value is None (lazy behavior)
            # OPTIMIZATION: Skip during batch reset - we'll refresh all placeholders once at the end
            if reset_value is None and not self._in_reset:
                # Build overlay from current form state
                overlay = self.get_current_values()

                # Collect live context from other open windows for cross-window placeholder resolution
                live_context = self._collect_live_context_from_other_windows() if self._parent_manager is None else None

                # Build context stack (handles static defaults for global config editing + live context)
                token, live_context_values = self._unwrap_live_context(live_context)
                with self._build_context_stack(overlay, live_context=live_context_values, live_context_token=token):
                    placeholder_text = self.service.get_placeholder_text(param_name, self.dataclass_type)
                    if placeholder_text:
                        from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer
                        PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)

        # Emit parameter change to notify other components
        self.parameter_changed.emit(param_name, reset_value)

        # For root managers (especially GlobalPipelineConfig), ensure cross-window context updates immediately
        if self._parent_manager is None:
            self._schedule_cross_window_refresh()

    def _get_reset_value(self, param_name: str) -> Any:
        """Get reset value based on editing context.

        For global config editing: Use static class defaults (not None)
        For lazy config editing: Use signature defaults (None for inheritance)
        For functions: Use signature defaults
        """
        # For global config editing, use static class defaults instead of None
        if self.config.is_global_config_editing and self.dataclass_type:
            # Get static default from class attribute
            try:
                static_default = object.__getattribute__(self.dataclass_type, param_name)
                return static_default
            except AttributeError:
                # Fallback to signature default if no class attribute
                pass

        # For everything else, use signature defaults
        return self.param_defaults.get(param_name)



    def get_current_values(self) -> Dict[str, Any]:
        """
        Get current parameter values preserving lazy dataclass structure.

        This fixes the lazy default materialization override saving issue by ensuring
        that lazy dataclasses maintain their structure when values are retrieved.
        """
        with timer(f"get_current_values ({self.field_id})", threshold_ms=2.0):
            # Start from cached parameter values instead of re-reading every widget
            current_values = dict(self._current_value_cache)

            # Checkbox validation is handled in widget creation

            # Collect values from nested managers, respecting optional dataclass checkbox states
            self._apply_to_nested_managers(
                lambda name, manager: self._process_nested_values_if_checkbox_enabled(
                    name, manager, current_values
                )
            )

            # Lazy dataclasses are now handled by LazyDataclassEditor, so no structure preservation needed
            return current_values

    def get_user_modified_values(self) -> Dict[str, Any]:
        """
        Get only values that were explicitly set by the user (non-None raw values).

        For lazy dataclasses, this preserves lazy resolution for unmodified fields
        by only returning fields where the raw value is not None.

        For nested dataclasses, only include them if they have user-modified fields inside.

        CRITICAL: Includes fields that were explicitly reset to None (tracked in reset_fields).
        This ensures cross-window updates see reset operations and can override saved concrete values.
        The None values will be used in dataclasses.replace() to override saved values.
        """
        if not hasattr(self.config, '_resolve_field_value'):
            return self.get_current_values()

        user_modified = {}
        current_values = self.get_current_values()

        # Include fields where the raw value is not None OR the field was explicitly reset
        for field_name, value in current_values.items():
            # CRITICAL: Include None values if they were explicitly reset
            # This allows other windows to see that the field was reset and should override saved values
            is_explicitly_reset = field_name in self.reset_fields

            if value is not None or is_explicitly_reset:
                # CRITICAL: For nested dataclasses, we need to extract only user-modified fields
                # by checking the raw values (using object.__getattribute__ to avoid resolution)
                from dataclasses import is_dataclass, fields as dataclass_fields
                if is_dataclass(value) and not isinstance(value, type):
                    # Extract raw field values from nested dataclass
                    nested_user_modified = {}
                    for field in dataclass_fields(value):
                        raw_value = object.__getattribute__(value, field.name)
                        if raw_value is not None:
                            nested_user_modified[field.name] = raw_value

                    # Only include if nested dataclass has user-modified fields
                    if nested_user_modified:
                        # CRITICAL: Pass as dict, not as reconstructed instance
                        # This allows the context merging to handle it properly
                        # We'll need to reconstruct it when applying to context
                        user_modified[field_name] = (type(value), nested_user_modified)
                else:
                    # Non-dataclass field, include if not None OR explicitly reset
                    user_modified[field_name] = value

        return user_modified

    def _reconstruct_nested_dataclasses(self, live_values: dict, base_instance=None) -> dict:
        """
        Reconstruct nested dataclasses from tuple format (type, dict) to instances.

        get_user_modified_values() returns nested dataclasses as (type, dict) tuples
        to preserve only user-modified fields. This function reconstructs them as instances
        by merging the user-modified fields into the base instance's nested dataclasses.

        Args:
            live_values: Dict with values, may contain (type, dict) tuples for nested dataclasses
            base_instance: Base dataclass instance to merge into (for nested dataclass fields)
        """
        import dataclasses
        from dataclasses import is_dataclass

        reconstructed = {}
        for field_name, value in live_values.items():
            if isinstance(value, tuple) and len(value) == 2:
                # Nested dataclass in tuple format: (type, dict)
                dataclass_type, field_dict = value

                # CRITICAL: If we have a base instance, merge into its nested dataclass
                # This prevents creating fresh instances with None defaults
                if base_instance and hasattr(base_instance, field_name):
                    base_nested = getattr(base_instance, field_name)
                    if base_nested is not None and is_dataclass(base_nested):
                        # Merge user-modified fields into base nested dataclass
                        reconstructed[field_name] = dataclasses.replace(base_nested, **field_dict)
                    else:
                        # No base nested dataclass, create fresh instance
                        reconstructed[field_name] = dataclass_type(**field_dict)
                else:
                    # No base instance, create fresh instance
                    reconstructed[field_name] = dataclass_type(**field_dict)
            else:
                # Regular value, pass through
                reconstructed[field_name] = value
        return reconstructed

    def _create_overlay_instance(self, overlay_type, values_dict):
        """
        Create an overlay instance from a type and values dict.

        Handles both dataclasses (instantiate normally) and non-dataclass types
        like functions (use SimpleNamespace as fallback).

        Args:
            overlay_type: Type to instantiate (dataclass, function, etc.)
            values_dict: Dict of parameter values to pass to constructor

        Returns:
            Instance of overlay_type or SimpleNamespace if type is not instantiable
        """
        try:
            return overlay_type(**values_dict)
        except TypeError:
            # Function or other non-instantiable type: use SimpleNamespace
            from types import SimpleNamespace
            return SimpleNamespace(**values_dict)

    def _build_context_stack(self, overlay, skip_parent_overlay: bool = False, live_context: dict = None, live_context_token: Optional[int] = None):
        """Build nested config_context() calls for placeholder resolution.

        Context stack order for PipelineConfig (lazy):
        1. Thread-local global config (automatic base - loaded instance)
        2. Parent context(s) from self.context_obj (if provided) - with live values if available
        3. Parent overlay (if nested form)
        4. Overlay from current form values (always applied last)

        Context stack order for GlobalPipelineConfig (non-lazy):
        1. Thread-local global config (automatic base - loaded instance)
        2. Static defaults (masks thread-local with fresh GlobalPipelineConfig())
        3. Overlay from current form values (always applied last)

        Args:
            overlay: Current form values (from get_current_values()) - dict or dataclass instance
            skip_parent_overlay: If True, skip applying parent's user-modified values.
                                Used during reset to prevent parent from re-introducing old values.
            live_context: Optional dict mapping object instances to their live values from other open windows

        Returns:
            ExitStack with nested contexts
        """
        from contextlib import ExitStack
        from openhcs.config_framework.context_manager import config_context

        stack = ExitStack()

        # CRITICAL: For GlobalPipelineConfig editing (root form only), apply static defaults as base context
        # This masks the thread-local loaded instance with class defaults
        # Only do this for the ROOT GlobalPipelineConfig form, not nested configs or step editor
        is_root_global_config = (self.config.is_global_config_editing and
                                 self.global_config_type is not None and
                                 self.context_obj is None)  # No parent context = root form

        if is_root_global_config:
            static_defaults = self.global_config_type()
            stack.enter_context(config_context(static_defaults, mask_with_none=True))
        else:
            # CRITICAL: Always add global context layer, either from live editor or thread-local
            # This ensures placeholders show correct values even when GlobalPipelineConfig editor is closed
            global_layer = self._get_cached_global_context(live_context_token, live_context)
            if global_layer is not None:
                # Use live values from open GlobalPipelineConfig editor
                stack.enter_context(config_context(global_layer))
            else:
                # No live editor - use thread-local global config (saved values)
                from openhcs.config_framework.context_manager import get_base_global_config
                thread_local_global = get_base_global_config()
                if thread_local_global is not None:
                    stack.enter_context(config_context(thread_local_global))
                else:
                    logger.warning(f"🔍 No global context available (neither live nor thread-local)")

        # CRITICAL FIX: For function panes with step_instance as context_obj, we need to add PipelineConfig
        # from live_context as a separate layer BEFORE the step_instance layer.
        # This ensures the hierarchy: Global -> Pipeline -> Step -> Function
        # Without this, function panes skip PipelineConfig and go straight from Global to Step.
        from openhcs.core.config import PipelineConfig
        if live_context and not isinstance(self.context_obj, PipelineConfig):
            # Check if we have PipelineConfig in live_context
            pipeline_config_live = self._find_live_values_for_type(PipelineConfig, live_context)
            if pipeline_config_live is not None:
                try:
                    # Create PipelineConfig instance from live values
                    import dataclasses
                    pipeline_config_instance = PipelineConfig(**pipeline_config_live)
                    stack.enter_context(config_context(pipeline_config_instance))
                    logger.debug(f"Added PipelineConfig layer from live context for {self.field_id}")
                except Exception as e:
                    logger.warning(f"Failed to add PipelineConfig layer from live context: {e}")

        # Apply parent context(s) if provided
        if self.context_obj is not None:
            if isinstance(self.context_obj, list):
                # Multiple parent contexts (future: deeply nested editors)
                for ctx in self.context_obj:
                    # Check if we have live values for this context TYPE (or its lazy/base equivalent)
                    ctx_type = type(ctx)
                    live_values = self._find_live_values_for_type(ctx_type, live_context)
                    if live_values is not None:
                        try:
                            live_instance = self._get_cached_parent_context(ctx, live_context_token, live_context)
                            stack.enter_context(config_context(live_instance))
                        except Exception as e:
                            logger.warning(f"Failed to apply live parent context for {type(ctx).__name__}: {e}")
                            stack.enter_context(config_context(ctx))
                    else:
                        stack.enter_context(config_context(ctx))
            else:
                # Single parent context (Step Editor: pipeline_config)
                # CRITICAL: If live_context has updated values for this context TYPE, merge them into the saved instance
                # This preserves inheritance: only concrete (non-None) live values override the saved instance
                ctx_type = type(self.context_obj)
                live_values = self._find_live_values_for_type(ctx_type, live_context)

                if live_values is not None:
                    try:
                        live_instance = self._get_cached_parent_context(self.context_obj, live_context_token, live_context)
                        stack.enter_context(config_context(live_instance))
                    except Exception as e:
                        logger.warning(f"Failed to apply live parent context: {e}")
                        stack.enter_context(config_context(self.context_obj))
                else:
                    # No live values from other windows - use context_obj directly
                    # This happens when the parent config window is closed after saving
                    stack.enter_context(config_context(self.context_obj))

        # CRITICAL: For nested forms, include parent's USER-MODIFIED values for sibling inheritance
        # This allows live placeholder updates when sibling fields change
        # ONLY enable this AFTER initial form load to avoid polluting placeholders with initial widget values
        # SKIP if skip_parent_overlay=True (used during reset to prevent re-introducing old values)
        parent_manager = getattr(self, '_parent_manager', None)
        if (not skip_parent_overlay and
            parent_manager and
            hasattr(parent_manager, 'get_user_modified_values') and
            hasattr(parent_manager, 'dataclass_type') and
            parent_manager._initial_load_complete):  # Check PARENT's initial load flag

            # Get only user-modified values from parent (not all values)
            # This prevents polluting context with stale/default values
            parent_user_values = parent_manager.get_user_modified_values()

            if parent_user_values and parent_manager.dataclass_type:
                # CRITICAL: Exclude the current nested config from parent overlay
                # This prevents the parent from re-introducing old values when resetting fields in nested form
                # Example: When resetting well_filter in StepMaterializationConfig, don't include
                # step_materialization_config from parent's user-modified values
                # CRITICAL FIX: Also exclude params from parent's exclude_params list (e.g., 'func' for FunctionStep)
                excluded_keys = {self.field_id}
                if hasattr(parent_manager, 'exclude_params') and parent_manager.exclude_params:
                    excluded_keys.update(parent_manager.exclude_params)

                filtered_parent_values = {k: v for k, v in parent_user_values.items() if k not in excluded_keys}

                if filtered_parent_values:
                    # Use lazy version of parent type to enable sibling inheritance
                    from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
                    parent_type = parent_manager.dataclass_type
                    lazy_parent_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(parent_type)
                    if lazy_parent_type:
                        parent_type = lazy_parent_type

                    # CRITICAL FIX: Add excluded params from parent's object_instance
                    # This allows instantiating parent_type even when some params are excluded from the form
                    parent_values_with_excluded = filtered_parent_values.copy()
                    if hasattr(parent_manager, 'exclude_params') and parent_manager.exclude_params:
                        for excluded_param in parent_manager.exclude_params:
                            if excluded_param not in parent_values_with_excluded and hasattr(parent_manager.object_instance, excluded_param):
                                parent_values_with_excluded[excluded_param] = getattr(parent_manager.object_instance, excluded_param)

                    # Create parent overlay with only user-modified values (excluding current nested config)
                    # For global config editing (root form only), use mask_with_none=True to preserve None overrides
                    parent_overlay_instance = self._create_overlay_instance(parent_type, parent_values_with_excluded)

                    if is_root_global_config:
                        stack.enter_context(config_context(parent_overlay_instance, mask_with_none=True))
                    else:
                        stack.enter_context(config_context(parent_overlay_instance))

        # Convert overlay dict to object instance for config_context()
        # config_context() expects an object with attributes, not a dict
        # CRITICAL FIX: If overlay is a dict but empty (no widgets yet), use object_instance directly
        if isinstance(overlay, dict):
            if not overlay and self.object_instance is not None:
                # Empty dict means widgets don't exist yet - use original instance for context
                import dataclasses
                if dataclasses.is_dataclass(self.object_instance):
                    overlay_instance = self.object_instance
                else:
                    # For non-dataclass objects, use as-is
                    overlay_instance = self.object_instance
            elif self.dataclass_type:
                # Normal case: convert dict to dataclass instance
                # CRITICAL FIX: For excluded params (e.g., 'func' for FunctionStep), use values from object_instance
                # This allows us to instantiate the dataclass type while excluding certain params from the overlay
                overlay_with_excluded = overlay.copy()
                for excluded_param in self.exclude_params:
                    if excluded_param not in overlay_with_excluded and hasattr(self.object_instance, excluded_param):
                        # Use the value from the original object instance for excluded params
                        overlay_with_excluded[excluded_param] = getattr(self.object_instance, excluded_param)

                # For functions and non-dataclass objects: use SimpleNamespace to hold parameters
                # For dataclasses: instantiate normally
                overlay_instance = self._create_overlay_instance(self.dataclass_type, overlay_with_excluded)
            else:
                # Dict but no dataclass_type - use SimpleNamespace
                from types import SimpleNamespace
                overlay_instance = SimpleNamespace(**overlay)
        else:
            # Already an instance - use as-is
            overlay_instance = overlay

        # Always apply overlay with current form values (the object being edited)
        # config_context() will filter None values and merge onto parent context
        stack.enter_context(config_context(overlay_instance))

        return stack

    def _get_cached_global_context(self, token: Optional[int], live_context: Optional[dict]):
        if not self.global_config_type or not live_context:
            self._cached_global_context_token = None
            self._cached_global_context_instance = None
            return None

        if token is None or self._cached_global_context_token != token:
            self._cached_global_context_instance = self._build_global_context_instance(live_context)
            self._cached_global_context_token = token
        return self._cached_global_context_instance

    def _build_global_context_instance(self, live_context: dict):
        from openhcs.config_framework.context_manager import get_base_global_config
        import dataclasses

        try:
            thread_local_global = get_base_global_config()
            if thread_local_global is None:
                return None

            global_live_values = self._find_live_values_for_type(self.global_config_type, live_context)
            if global_live_values is None:
                return None

            global_live_values = self._reconstruct_nested_dataclasses(global_live_values, thread_local_global)
            merged = dataclasses.replace(thread_local_global, **global_live_values)
            return merged
        except Exception as e:
            logger.warning(f"Failed to cache global context: {e}")
            return None

    def _get_cached_parent_context(self, ctx_obj, token: Optional[int], live_context: Optional[dict]):
        if ctx_obj is None:
            return None
        if token is None or not live_context:
            return self._build_parent_context_instance(ctx_obj, live_context)

        ctx_id = id(ctx_obj)
        cached = self._cached_parent_contexts.get(ctx_id)
        if cached and cached[0] == token:
            return cached[1]

        instance = self._build_parent_context_instance(ctx_obj, live_context)
        if instance is not None:
            self._cached_parent_contexts[ctx_id] = (token, instance)
        return instance

    def _build_parent_context_instance(self, ctx_obj, live_context: Optional[dict]):
        import dataclasses

        try:
            ctx_type = type(ctx_obj)
            live_values = self._find_live_values_for_type(ctx_type, live_context)
            if live_values is None:
                return ctx_obj

            live_values = self._reconstruct_nested_dataclasses(live_values, ctx_obj)

            # Try dataclasses.replace first (for dataclasses)
            # Fall back to creating overlay instance (handles both dataclasses and non-dataclass objects)
            if dataclasses.is_dataclass(ctx_obj):
                return dataclasses.replace(ctx_obj, **live_values)
            else:
                # For non-dataclass objects (like FunctionStep), use the same helper as overlay creation
                # This creates a SimpleNamespace with the live values
                return self._create_overlay_instance(ctx_type, live_values)
        except Exception as e:
            logger.warning(f"Failed to cache parent context for {ctx_obj}: {e}")
            return ctx_obj

    def _apply_initial_enabled_styling(self) -> None:
        """Apply initial enabled field styling based on resolved value from widget.

        This is called once after all widgets are created to ensure initial styling matches the enabled state.
        We get the resolved value from the checkbox widget, not from self.parameters, because the parameter
        might be None (lazy) but the checkbox shows the resolved placeholder value.

        CRITICAL: This should NOT be called for optional dataclass nested managers when instance is None.
        The None state dimming is handled by the optional dataclass checkbox handler.
        """

        # CRITICAL: Check if this is a nested manager inside an optional dataclass
        # If the parent's parameter for this nested manager is None, skip enabled styling
        # The optional dataclass checkbox handler already applied None-state dimming
        if self._parent_manager is not None:
            # Find which parameter in parent corresponds to this nested manager
            for param_name, nested_manager in self._parent_manager.nested_managers.items():
                if nested_manager is self:
                    # Check if this is an optional dataclass and if the instance is None
                    param_type = self._parent_manager.parameter_types.get(param_name)
                    if param_type:
                        from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
                        if ParameterTypeUtils.is_optional_dataclass(param_type):
                            # This is an optional dataclass - check if instance is None
                            instance = self._parent_manager.parameters.get(param_name)
                            if instance is None:
                                return
                    break

        # Get the enabled widget
        enabled_widget = self.widgets.get('enabled')
        if not enabled_widget:
            return

        # Get resolved value from widget
        if hasattr(enabled_widget, 'isChecked'):
            resolved_value = enabled_widget.isChecked()
        else:
            # Fallback to parameter value
            resolved_value = self.parameters.get('enabled')
            if resolved_value is None:
                resolved_value = True  # Default to enabled if we can't resolve

        # Call the enabled handler with the resolved value
        self._on_enabled_field_changed_universal('enabled', resolved_value)

    def _is_any_ancestor_disabled(self) -> bool:
        """
        Check if any ancestor form has enabled=False.

        This is used to determine if a nested config should remain dimmed
        even if its own enabled field is True.

        Returns:
            True if any ancestor has enabled=False, False otherwise
        """
        current = self._parent_manager
        while current is not None:
            if 'enabled' in current.parameters:
                enabled_widget = current.widgets.get('enabled')
                if enabled_widget and hasattr(enabled_widget, 'isChecked'):
                    if not enabled_widget.isChecked():
                        return True
            current = current._parent_manager
        return False

    def _refresh_enabled_styling(self) -> None:
        """
        Refresh enabled styling for this form and all nested forms.

        This should be called when context changes that might affect inherited enabled values.
        Similar to placeholder refresh, but for enabled field styling.

        CRITICAL: Skip optional dataclass nested managers when instance is None.
        """

        # CRITICAL: Track if this nested manager lives inside an optional dataclass that is currently None
        # Instead of skipping styling entirely, we propagate the state so we can keep the dimming applied
        is_optional_none = False
        if self._parent_manager is not None:
            for param_name, nested_manager in self._parent_manager.nested_managers.items():
                if nested_manager is self:
                    param_type = self._parent_manager.parameter_types.get(param_name)
                    if param_type:
                        from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
                        if ParameterTypeUtils.is_optional_dataclass(param_type):
                            instance = self._parent_manager.parameters.get(param_name)
                            if instance is None:
                                is_optional_none = True
                    break

        # Refresh this form's enabled styling if it has an enabled field
        if 'enabled' in self.parameters:
            # Get the enabled widget to read the CURRENT resolved value
            enabled_widget = self.widgets.get('enabled')
            if enabled_widget and hasattr(enabled_widget, 'isChecked'):
                # Use the checkbox's current state (which reflects resolved placeholder)
                resolved_value = enabled_widget.isChecked()
            else:
                # Fallback to parameter value
                resolved_value = self.parameters.get('enabled')
                if resolved_value is None:
                    resolved_value = True

            # Apply styling with the resolved value
            self._on_enabled_field_changed_universal('enabled', resolved_value)

        # Recursively refresh all nested forms' enabled styling
        for nested_manager in self.nested_managers.values():
            nested_manager._refresh_enabled_styling()

    def _on_enabled_field_changed_universal(self, param_name: str, value: Any) -> None:
        """
        UNIVERSAL ENABLED FIELD BEHAVIOR: Apply visual styling when 'enabled' parameter changes.

        This handler is connected for ANY form that has an 'enabled' parameter (function, dataclass, etc.).
        When enabled resolves to False (concrete or lazy), apply visual dimming WITHOUT blocking input.

        This creates consistent semantics across all ParameterFormManager instances:
        - enabled=True or lazy-resolved True: Normal styling
        - enabled=False or lazy-resolved False: Dimmed styling, inputs stay editable
        """
        if param_name != 'enabled':
            return

        # CRITICAL FIX: Ignore propagated 'enabled' signals from nested forms
        # When a nested form's enabled field changes, it handles its own styling,
        # then propagates the signal up. The parent should NOT apply styling changes
        # in response to this propagated signal - only to direct changes to its own enabled field.
        if getattr(self, '_propagating_nested_enabled', False):
            return

        # Also check: does this form actually HAVE an 'enabled' parameter?
        # This is a redundant safety check in case the flag mechanism fails
        if 'enabled' not in self.parameters:
            return

        # Import ParameterTypeUtils at the top of the method for use throughout
        from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils

        # DEBUG: Log when this handler is called

        # Resolve lazy value: None means inherit from parent context
        if value is None:
            # Lazy field - get the resolved placeholder value from the widget
            enabled_widget = self.widgets.get('enabled')
            if enabled_widget and hasattr(enabled_widget, 'isChecked'):
                resolved_value = enabled_widget.isChecked()
            else:
                # Fallback: assume True if we can't resolve
                resolved_value = True
        else:
            resolved_value = value


        # Apply styling to the entire form based on resolved enabled value
        # Inputs stay editable - only visual dimming changes
        # CRITICAL FIX: Only apply to widgets in THIS form, not nested ParameterFormManager forms
        # This prevents crosstalk when a step has 'enabled' field and nested configs also have 'enabled' fields
        def get_direct_widgets(parent_widget):
            """Get widgets that belong to this form, excluding nested ParameterFormManager widgets."""
            direct_widgets = []
            all_widgets = parent_widget.findChildren(ALL_INPUT_WIDGET_TYPES)

            for widget in all_widgets:
                widget_name = f"{widget.__class__.__name__}({widget.objectName() or 'no-name'})"
                object_name = widget.objectName()

                # Check if widget belongs to a nested manager by checking if its object name starts with nested manager's field_id
                belongs_to_nested = False
                for nested_name, nested_manager in self.nested_managers.items():
                    nested_field_id = nested_manager.field_id
                    if object_name and object_name.startswith(nested_field_id + '_'):
                        belongs_to_nested = True
                        break

                if not belongs_to_nested:
                    direct_widgets.append(widget)

            return direct_widgets

        direct_widgets = get_direct_widgets(self)
        widget_names = [f"{w.__class__.__name__}({w.objectName() or 'no-name'})" for w in direct_widgets[:5]]  # First 5

        # CRITICAL: Check if this is an Optional dataclass with None value
        # This needs to be checked BEFORE applying styling logic
        is_optional_none = False
        if self._parent_manager:
            # Find our parameter name in parent
            our_param_name = None
            for param_name, nested_manager in self._parent_manager.nested_managers.items():
                if nested_manager == self:
                    our_param_name = param_name
                    break

            if our_param_name:
                param_type = self._parent_manager.parameter_types.get(our_param_name)
                if param_type and ParameterTypeUtils.is_optional_dataclass(param_type):
                    instance = self._parent_manager.parameters.get(our_param_name)
                    if instance is None:
                        is_optional_none = True

        # CRITICAL: For nested configs (inside GroupBox), apply styling to the GroupBox container
        # For top-level forms (step, function), apply styling to direct widgets
        is_nested_config = self._parent_manager is not None and any(
            nested_manager == self for nested_manager in self._parent_manager.nested_managers.values()
        )

        if is_nested_config:
            # This is a nested config - find the GroupBox container and apply styling to it
            # The GroupBox is stored in parent's widgets dict
            group_box = None
            for param_name, nested_manager in self._parent_manager.nested_managers.items():
                if nested_manager == self:
                    group_box = self._parent_manager.widgets.get(param_name)
                    break

            if group_box:
                from PyQt6.QtWidgets import QGraphicsOpacityEffect

                # CRITICAL: Check if ANY ancestor has enabled=False
                # If any ancestor is disabled, child should remain dimmed regardless of its own enabled value
                ancestor_is_disabled = self._is_any_ancestor_disabled()

                # CRITICAL: Check if this nested manager lives inside an optional dataclass that is currently None
                is_optional_none = False
                if self._parent_manager is not None:
                    for param_name, nested_manager in self._parent_manager.nested_managers.items():
                        if nested_manager is self:
                            param_type = self._parent_manager.parameter_types.get(param_name)
                            if param_type:
                                if ParameterTypeUtils.is_optional_dataclass(param_type):
                                    instance = self._parent_manager.parameters.get(param_name)
                                    if instance is None:
                                        is_optional_none = True
                            break

                if resolved_value and not ancestor_is_disabled and not is_optional_none:
                    # Enabled=True AND no ancestor is disabled: Remove dimming from GroupBox
                    # Clear effects from all widgets in the GroupBox
                    for widget in group_box.findChildren(ALL_INPUT_WIDGET_TYPES):
                        widget.setGraphicsEffect(None)
                else:
                    # Ancestor disabled, optional None, or resolved False → apply dimming
                    for widget in group_box.findChildren(ALL_INPUT_WIDGET_TYPES):
                        effect = QGraphicsOpacityEffect()
                        effect.setOpacity(0.4)
                        widget.setGraphicsEffect(effect)
        else:
            # This is a top-level form (step, function) - apply styling to direct widgets + nested configs
            if resolved_value:
                # Enabled=True: Remove dimming from direct widgets
                for widget in direct_widgets:
                    widget.setGraphicsEffect(None)

                # CRITICAL: Restore nested configs, but respect their own state
                # Don't restore if:
                # 1. Nested form has enabled=False
                # 2. Nested form is Optional dataclass with None value
                for param_name, nested_manager in self.nested_managers.items():
                    # Check if this is an Optional dataclass with None value
                    param_type = self.parameter_types.get(param_name)
                    is_optional_none = False
                    if param_type and ParameterTypeUtils.is_optional_dataclass(param_type):
                        instance = self.parameters.get(param_name)
                        if instance is None:
                            is_optional_none = True
                            continue  # Don't restore - keep dimmed
                    
                    # Check if nested form has its own enabled=False
                    nested_has_enabled_false = False
                    if 'enabled' in nested_manager.parameters:
                        enabled_widget = nested_manager.widgets.get('enabled')
                        if enabled_widget and hasattr(enabled_widget, 'isChecked'):
                            nested_enabled = enabled_widget.isChecked()
                        else:
                            nested_enabled = nested_manager.parameters.get('enabled', True)
                        
                        if not nested_enabled:
                            nested_has_enabled_false = True
                            continue  # Don't restore - keep dimmed
                    
                    # Safe to restore this nested config
                    group_box = self.widgets.get(param_name)
                    if not group_box:
                        # Try using the nested manager's field_id instead
                        group_box = self.widgets.get(nested_manager.field_id)
                        if not group_box:
                            continue
                    
                    # Remove dimming from ALL widgets in the GroupBox
                    widgets_to_restore = group_box.findChildren(ALL_INPUT_WIDGET_TYPES)
                    for widget in widgets_to_restore:
                        widget.setGraphicsEffect(None)
                    
                    # Recursively handle nested managers within this nested manager
                    # This ensures deeply nested forms are also restored correctly
                    nested_manager._refresh_enabled_styling()
            else:
                # Enabled=False: Apply dimming to direct widgets + ALL nested configs
                from PyQt6.QtWidgets import QGraphicsOpacityEffect
                for widget in direct_widgets:
                    # Skip QLabel widgets when dimming (only dim inputs)
                    if isinstance(widget, QLabel):
                        continue
                    effect = QGraphicsOpacityEffect()
                    effect.setOpacity(0.4)
                    widget.setGraphicsEffect(effect)

                # Also dim all nested configs (entire step is disabled)
                for param_name, nested_manager in self.nested_managers.items():
                    group_box = self.widgets.get(param_name)
                    if not group_box:
                        # Try using the nested manager's field_id instead
                        group_box = self.widgets.get(nested_manager.field_id)
                        if not group_box:
                            continue
                    widgets_to_dim = group_box.findChildren(ALL_INPUT_WIDGET_TYPES)
                    for widget in widgets_to_dim:
                        effect = QGraphicsOpacityEffect()
                        effect.setOpacity(0.4)
                        widget.setGraphicsEffect(effect)

    def _on_nested_parameter_changed(self, param_name: str, value: Any) -> None:
        """
        Handle parameter changes from nested forms.

        When a nested form's field changes:
        1. Refresh parent form's placeholders (in case they inherit from nested values)
        2. Refresh all sibling nested forms' placeholders
        3. Refresh enabled styling (in case siblings inherit enabled values)
        4. Propagate the change signal up to root for cross-window updates
        """
        # OPTIMIZATION: Skip expensive placeholder refreshes during batch reset
        # The reset operation will do a single refresh at the end
        # BUT: Still propagate the signal so dual editor window can sync function editor
        in_reset = getattr(self, '_in_reset', False)
        block_cross_window = getattr(self, '_block_cross_window_updates', False)

        # Find which nested manager emitted this change (needed for both refresh and signal propagation)
        emitting_manager_name = None
        for nested_name, nested_manager in self.nested_managers.items():
            if param_name in nested_manager.parameters:
                emitting_manager_name = nested_name
                break

        # CRITICAL OPTIMIZATION: Also check if ANY nested manager is in reset mode
        # When a nested dataclass's "Reset All" button is clicked, the nested manager
        # sets _in_reset=True, but the parent doesn't know about it. We need to skip
        # expensive updates while the child is resetting.
        nested_in_reset = False
        for nested_manager in self.nested_managers.values():
            if getattr(nested_manager, '_in_reset', False):
                nested_in_reset = True
                break
            if getattr(nested_manager, '_block_cross_window_updates', False):
                nested_in_reset = True
                break

        # Skip expensive operations during reset, but still propagate signal
        if not (in_reset or block_cross_window or nested_in_reset):
            # Collect live context from other windows (only for root managers)
            if self._parent_manager is None:
                live_context = self._collect_live_context_from_other_windows()
            else:
                live_context = None

            # Refresh parent form's placeholders with live context
            self._refresh_all_placeholders(live_context=live_context)

            # Refresh all nested managers' placeholders (including siblings) with live context
            # emitting_manager_name was already found above
            self._apply_to_nested_managers(
                lambda name, manager: (
                    manager._refresh_all_placeholders(live_context=live_context)
                    if name != emitting_manager_name else None
                )
            )

            # CRITICAL: Only refresh enabled styling for siblings if the changed param is 'enabled'
            # AND only if this is necessary for lazy inheritance scenarios
            # FIX: Do NOT refresh when a nested form's own 'enabled' field changes -
            # this was causing styling pollution where toggling a nested enabled field
            # would incorrectly trigger styling updates on parents and siblings
            # The nested form handles its own styling via _on_enabled_field_changed_universal
            if param_name == 'enabled' and emitting_manager_name:
                # Only refresh siblings that might inherit from this nested form's enabled value
                # Skip the emitting manager itself (it already handled its own styling)
                self._apply_to_nested_managers(
                    lambda name, manager: (
                        manager._refresh_enabled_styling()
                        if name != emitting_manager_name else None
                    )
                )

        # CRITICAL: ALWAYS propagate parameter change signal up the hierarchy, even during reset
        # This ensures the dual editor window can sync the function editor when reset changes group_by
        # The root manager will emit context_value_changed via _emit_cross_window_change
        # IMPORTANT: We DO propagate 'enabled' field changes for cross-window styling updates
        #
        # CRITICAL FIX: When propagating 'enabled' changes from nested forms, set a flag
        # to prevent the parent's _on_enabled_field_changed_universal from incorrectly
        # applying styling changes (the nested form already handled its own styling)

        # CRITICAL FIX: When a nested dataclass field changes, emit the PARENT parameter name
        # with the reconstructed dataclass value, not the nested field name
        # This ensures function kwargs have dtype_config (dataclass), not default_dtype_conversion (field)
        if emitting_manager_name:
            # Get the reconstructed dataclass value from get_current_values
            nested_values = self.nested_managers[emitting_manager_name].get_current_values()
            param_type = self.parameter_types.get(emitting_manager_name)

            # Reconstruct dataclass instance
            from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
            if param_type and ParameterTypeUtils.is_optional_dataclass(param_type):
                inner_type = ParameterTypeUtils.get_optional_inner_type(param_type)
                reconstructed_value = inner_type(**nested_values) if nested_values else None
            elif param_type and hasattr(param_type, '__dataclass_fields__'):
                reconstructed_value = param_type(**nested_values) if nested_values else None
            else:
                reconstructed_value = nested_values

            # Emit parent parameter name with reconstructed dataclass
            if param_name == 'enabled':
                self._propagating_nested_enabled = True

            self.parameter_changed.emit(emitting_manager_name, reconstructed_value)

            if param_name == 'enabled':
                self._propagating_nested_enabled = False
        else:
            # Not from a nested manager, emit as-is
            if param_name == 'enabled':
                self._propagating_nested_enabled = True

            self.parameter_changed.emit(param_name, value)

            if param_name == 'enabled':
                self._propagating_nested_enabled = False

    def _refresh_with_live_context(self, live_context: Any = None, exclude_param: str = None) -> None:
        """Refresh placeholders using live context from other open windows."""

        if live_context is None and self._parent_manager is None:
            live_context = self._collect_live_context_from_other_windows()

        if self._should_use_async_placeholder_refresh():
            self._schedule_async_placeholder_refresh(live_context, exclude_param)
        else:
            self._perform_placeholder_refresh_sync(live_context, exclude_param)

    def _refresh_all_placeholders(self, live_context: dict = None, exclude_param: str = None) -> None:
        """Refresh placeholder text for all widgets in this form.

        Args:
            live_context: Optional dict mapping object instances to their live values from other open windows
            exclude_param: Optional parameter name to exclude from refresh (e.g., the param that just changed)
        """
        # Extract token and live context values
        token, live_context_values = self._unwrap_live_context(live_context)

        # CRITICAL: Use token-based cache key, not value-based
        # The token increments whenever ANY value changes, which is correct behavior
        # The individual placeholder text cache is value-based to prevent redundant resolution
        # But the refresh operation itself should run when the token changes
        from openhcs.config_framework import CacheKey
        cache_key = CacheKey.from_args(exclude_param, token)

        def perform_refresh():
            """Actually perform the placeholder refresh."""
            with timer(f"_refresh_all_placeholders ({self.field_id})", threshold_ms=5.0):
                # Allow placeholder refresh for nested forms even if they're not detected as lazy dataclasses
                # The placeholder service will determine if placeholders are available
                if not self.dataclass_type:
                    return

                # CRITICAL FIX: Use self.parameters instead of get_current_values() for overlay
                # get_current_values() reads widget values, but widgets don't have placeholder state set yet
                # during initial refresh, so it reads displayed values instead of None
                # self.parameters has the correct None values from initialization
                overlay = self.parameters

                # Build context stack: parent context + overlay (with live context from other windows)
                candidate_names = set(self._placeholder_candidates)
                if exclude_param:
                    candidate_names.discard(exclude_param)
                if not candidate_names:
                    return

                token_inner, live_context_values = self._unwrap_live_context(live_context)
                with self._build_context_stack(overlay, live_context=live_context_values, live_context_token=token_inner):
                    monitor = get_monitor("Placeholder resolution per field")

                    for param_name in candidate_names:
                        widget = self.widgets.get(param_name)
                        if not widget:
                            continue

                        widget_in_placeholder_state = widget.property("is_placeholder_state")
                        current_value = self.parameters.get(param_name)
                        if current_value is not None and not widget_in_placeholder_state:
                            continue

                        with monitor.measure():
                            # CRITICAL: Resolve placeholder text and let widget signature check skip redundant updates
                            # The widget already checks if placeholder text changed - no need for complex caching
                            placeholder_text = self.service.get_placeholder_text(param_name, self.dataclass_type)
                            if placeholder_text:
                                from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer
                                # Widget signature check will skip update if placeholder text hasn't changed
                                PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)

            return True  # Return sentinel value to indicate refresh was performed

        # Use cache - if same token and exclude_param, skip the entire refresh
        self._placeholder_refresh_cache.get_or_compute(cache_key, perform_refresh)

    def _perform_placeholder_refresh_sync(self, live_context: Any, exclude_param: Optional[str]) -> None:
        """Run placeholder refresh synchronously on the UI thread."""
        self._refresh_all_placeholders(live_context=live_context, exclude_param=exclude_param)
        self._after_placeholder_text_applied(live_context)

    def _refresh_specific_placeholder(self, field_name: str = None, live_context: dict = None) -> None:
        """Refresh placeholder for a specific field, or all fields if field_name is None.

        For nested config changes, refreshes all fields that inherit from the changed config type.

        Args:
            field_name: Name of the specific field to refresh. If None, refresh all placeholders.
            live_context: Optional dict mapping object instances to their live values from other open windows
        """
        if field_name is None:
            # No specific field - refresh all placeholders
            self._refresh_all_placeholders(live_context=live_context)
            return

        # Check if this exact field exists
        if field_name in self._placeholder_candidates:
            self._refresh_single_field_placeholder(field_name, live_context)
            return

        # Field doesn't exist with exact name - find fields that inherit from the same base type
        # Example: PipelineConfig.well_filter_config changes → refresh Step.step_well_filter_config
        # Both inherit from WellFilterConfig, so changes in one affect the other
        fields_to_refresh = self._find_fields_inheriting_from_changed_field(field_name, live_context)

        if not fields_to_refresh:
            # No matching fields - nothing to refresh
            return

        # Refresh only the matching fields
        for matching_field in fields_to_refresh:
            self._refresh_single_field_placeholder(matching_field, live_context)

    def _refresh_specific_placeholder_from_path(self, parent_field_name: str = None, remaining_path: str = None, live_context: dict = None) -> None:
        """Refresh placeholder for nested manager based on parent field name and remaining path.

        This is called on nested managers during cross-window updates to extract the relevant field name.

        Example:
            Parent manager has field "well_filter_config" (nested dataclass)
            Remaining path is "well_filter" (field inside the nested dataclass)
            → This nested manager should refresh its "well_filter" field

        Args:
            parent_field_name: Name of the field in the parent manager that contains this nested manager
            remaining_path: Remaining path after the parent field (e.g., "well_filter" or "sub_config.field")
            live_context: Optional dict mapping object instances to their live values from other open windows
        """
        # If this nested manager corresponds to the parent field, use the remaining path
        # Otherwise, skip (this nested manager is not affected)
        if remaining_path:
            # Extract the first component of the remaining path
            # Example: "well_filter" → "well_filter"
            # Example: "sub_config.field" → "sub_config"
            field_name = remaining_path.split('.')[0] if remaining_path else None
            self._refresh_specific_placeholder(field_name, live_context)
        else:
            # No remaining path - the parent field itself changed (e.g., entire config replaced)
            # Refresh all placeholders in this nested manager
            self._refresh_all_placeholders(live_context=live_context)

    def _find_fields_inheriting_from_changed_field(self, changed_field_name: str, live_context: dict = None) -> list:
        """Find fields in this form that inherit from the same base type as the changed field.

        Example: PipelineConfig.well_filter_config (WellFilterConfig) changes
                 → Find Step.step_well_filter_config (StepWellFilterConfig inherits from WellFilterConfig)

        Args:
            changed_field_name: Name of the field that changed in another window
            live_context: Live context to find the changed field's type

        Returns:
            List of field names in this form that should be refreshed
        """
        from dataclasses import fields as dataclass_fields, is_dataclass

        if not self.dataclass_type or not is_dataclass(self.dataclass_type):
            return []

        # Get the type of the changed field from live context
        # We need to check what type the changed field is in the other window
        changed_field_type = None

        # Try to get the changed field type from live context values
        token, live_context_values = self._unwrap_live_context(live_context)
        if live_context_values:
            for ctx_type, ctx_values in live_context_values.items():
                if changed_field_name in ctx_values:
                    # Found the changed field - get its type from the context type's fields
                    if is_dataclass(ctx_type):
                        for field in dataclass_fields(ctx_type):
                            if field.name == changed_field_name:
                                changed_field_type = field.type
                                break
                    break

        if not changed_field_type:
            # Couldn't determine the changed field type - skip
            return []

        # Find fields in this form that have the same type or inherit from the same base
        matching_fields = []
        for field in dataclass_fields(self.dataclass_type):
            if field.name not in self._placeholder_candidates:
                continue

            # Check if this field's type matches or inherits from the changed field's type
            field_type = field.type

            # Handle Optional types and get the actual type
            from typing import get_origin, get_args
            if get_origin(field_type) is type(None) or str(field_type).startswith('Optional'):
                args = get_args(field_type)
                if args:
                    field_type = args[0]

            # Check if types match or share a common base
            try:
                # Same type
                if field_type == changed_field_type:
                    matching_fields.append(field.name)
                    continue

                # Check if both are classes and share inheritance
                if isinstance(field_type, type) and isinstance(changed_field_type, type):
                    # Check if field_type inherits from changed_field_type
                    if issubclass(field_type, changed_field_type):
                        matching_fields.append(field.name)
                        continue
                    # Check if changed_field_type inherits from field_type
                    if issubclass(changed_field_type, field_type):
                        matching_fields.append(field.name)
                        continue
            except TypeError:
                # issubclass failed - types aren't compatible
                continue

        return matching_fields

    def _refresh_single_field_placeholder(self, field_name: str, live_context: dict = None) -> None:
        """Refresh placeholder for a single specific field.

        Args:
            field_name: Name of the field to refresh
            live_context: Optional dict mapping object instances to their live values
        """
        widget = self.widgets.get(field_name)
        if not widget:
            return

        widget_in_placeholder_state = widget.property("is_placeholder_state")
        current_value = self.parameters.get(field_name)
        if current_value is not None and not widget_in_placeholder_state:
            return

        # Build context stack and resolve placeholder
        token, live_context_values = self._unwrap_live_context(live_context)
        overlay = self.parameters
        with self._build_context_stack(overlay, live_context=live_context_values, live_context_token=token):
            placeholder_text = self.service.get_placeholder_text(field_name, self.dataclass_type)
            if placeholder_text:
                from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer
                PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)

    def _after_placeholder_text_applied(self, live_context: Any) -> None:
        """Apply nested refreshes and styling once placeholders have been updated."""
        self._apply_to_nested_managers(
            lambda name, manager: manager._refresh_all_placeholders(live_context=live_context)
        )
        self._refresh_enabled_styling()
        self._apply_to_nested_managers(lambda name, manager: manager._refresh_enabled_styling())
        self._has_completed_initial_placeholder_refresh = True

    def _should_use_async_placeholder_refresh(self) -> bool:
        """Determine if the current refresh can be performed off the UI thread."""
        if not self.ASYNC_PLACEHOLDER_REFRESH:
            return False
        if self._parent_manager is not None:
            return False
        if getattr(self, '_in_reset', False):
            return False
        if getattr(self, '_block_cross_window_updates', False):
            return False
        if not self._has_completed_initial_placeholder_refresh:
            return False
        if not self.dataclass_type:
            return False
        return True

    def _schedule_async_placeholder_refresh(self, live_context: dict, exclude_param: Optional[str]) -> None:
        """Offload placeholder resolution to a worker thread."""
        if not self.dataclass_type:
            self._after_placeholder_text_applied(live_context)
            return

        placeholder_plan = self._capture_placeholder_plan(exclude_param)
        if not placeholder_plan:
            self._after_placeholder_text_applied(live_context)
            return

        parameters_snapshot = dict(self.parameters)
        self._placeholder_refresh_generation += 1
        generation = self._placeholder_refresh_generation
        self._pending_placeholder_metadata = {
            "live_context": live_context,
            "exclude_param": exclude_param,
        }

        task = _PlaceholderRefreshTask(
            self,
            generation=generation,
            parameters_snapshot=parameters_snapshot,
            placeholder_plan=placeholder_plan,
            live_context_snapshot=live_context,
        )
        self._active_placeholder_task = task
        task.signals.completed.connect(self._on_placeholder_task_completed)
        task.signals.failed.connect(self._on_placeholder_task_failed)
        self._placeholder_thread_pool.start(task)

    def _capture_placeholder_plan(self, exclude_param: Optional[str]) -> Dict[str, bool]:
        """Capture UI state needed by the background placeholder resolver."""
        plan = {}
        for param_name, widget in self.widgets.items():
            if exclude_param and param_name == exclude_param:
                continue
            if not widget:
                continue
            plan[param_name] = bool(widget.property("is_placeholder_state"))
        return plan

    def _unwrap_live_context(self, live_context: Optional[Any]) -> Tuple[Optional[int], Optional[dict]]:
        """Return (token, values) for a live context snapshot or raw dict."""
        if isinstance(live_context, LiveContextSnapshot):
            return live_context.token, live_context.values
        return None, live_context

    def _compute_placeholder_map_async(
        self,
        parameters_snapshot: Dict[str, Any],
        placeholder_plan: Dict[str, bool],
        live_context_snapshot: Optional[LiveContextSnapshot],
    ) -> Dict[str, str]:
        """Compute placeholder text map in a worker thread."""
        if not self.dataclass_type or not placeholder_plan:
            return {}

        placeholder_map: Dict[str, str] = {}
        token, live_context_values = self._unwrap_live_context(live_context_snapshot)
        with self._build_context_stack(parameters_snapshot, live_context=live_context_values, live_context_token=token):
            for param_name, was_placeholder in placeholder_plan.items():
                current_value = parameters_snapshot.get(param_name)
                should_apply_placeholder = current_value is None or was_placeholder
                if not should_apply_placeholder:
                    continue
                placeholder_text = self.service.get_placeholder_text(param_name, self.dataclass_type)
                if placeholder_text:
                    placeholder_map[param_name] = placeholder_text
        return placeholder_map

    def _apply_placeholder_map_results(self, placeholder_map: Dict[str, str]) -> None:
        """Apply resolved placeholder text to widgets on the UI thread."""
        if not placeholder_map:
            return
        from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer

        for param_name, placeholder_text in placeholder_map.items():
            widget = self.widgets.get(param_name)
            if widget and placeholder_text:
                PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)

    def _on_placeholder_task_completed(self, generation: int, placeholder_map: Dict[str, str]) -> None:
        """Handle completion of async placeholder refresh."""
        if generation != self._placeholder_refresh_generation:
            return

        self._active_placeholder_task = None
        self._apply_placeholder_map_results(placeholder_map)
        live_context = self._pending_placeholder_metadata.get("live_context")
        self._after_placeholder_text_applied(live_context)
        self._pending_placeholder_metadata = {}

    def _on_placeholder_task_failed(self, generation: int, error_message: str) -> None:
        """Fallback to synchronous refresh if async worker fails."""
        if generation != self._placeholder_refresh_generation:
            return

        logger.warning("Async placeholder refresh failed (gen %s): %s", generation, error_message)
        metadata = self._pending_placeholder_metadata or {}
        live_context = metadata.get("live_context")
        exclude_param = metadata.get("exclude_param")
        self._active_placeholder_task = None
        self._pending_placeholder_metadata = {}
        self._perform_placeholder_refresh_sync(live_context, exclude_param)

    def _apply_to_nested_managers(self, operation_func: callable) -> None:
        """Apply operation to all nested managers."""
        for param_name, nested_manager in self.nested_managers.items():
            operation_func(param_name, nested_manager)

    def _apply_all_styling_callbacks(self) -> None:
        """Recursively apply all styling callbacks for this manager and all nested managers.

        This must be called AFTER all async widget creation is complete, otherwise
        findChildren() calls in styling callbacks will return empty lists.
        """
        # Apply this manager's callbacks
        for callback in self._on_build_complete_callbacks:
            callback()
        self._on_build_complete_callbacks.clear()

        # Recursively apply nested managers' callbacks
        for nested_manager in self.nested_managers.values():
            nested_manager._apply_all_styling_callbacks()

    def _apply_all_post_placeholder_callbacks(self) -> None:
        """Recursively apply all post-placeholder callbacks for this manager and all nested managers.

        This must be called AFTER placeholders are refreshed, so enabled styling can use resolved values.
        """
        # Apply this manager's callbacks
        for callback in self._on_placeholder_refresh_complete_callbacks:
            callback()
        self._on_placeholder_refresh_complete_callbacks.clear()

        # Recursively apply nested managers' callbacks
        for nested_manager in self.nested_managers.values():
            nested_manager._apply_all_post_placeholder_callbacks()

    def _on_parameter_changed_root(self, param_name: str, value: Any) -> None:
        """Debounce placeholder refreshes originating from this root manager."""
        if (getattr(self, '_in_reset', False) or
                getattr(self, '_block_cross_window_updates', False) or
                param_name == 'enabled'):
            return
        if self._pending_debounced_exclude_param is None:
            self._pending_debounced_exclude_param = param_name
        else:
            # Preserve the most recent field to exclude
            self._pending_debounced_exclude_param = param_name
        if self._parameter_change_timer is None:
            self._run_debounced_placeholder_refresh()
        else:
            self._parameter_change_timer.start(self.PARAMETER_CHANGE_DEBOUNCE_MS)

    def _on_parameter_changed_nested(self, param_name: str, value: Any) -> None:
        """Bubble refresh requests from nested managers up to the root with debounce.

        CRITICAL: ALL changes must emit cross-window signals so other windows can react in real time.
        'enabled' changes skip placeholder refreshes to avoid infinite loops.
        """
        if (getattr(self, '_in_reset', False) or
                getattr(self, '_block_cross_window_updates', False)):
            return

        # Find root manager
        root = self
        while root._parent_manager is not None:
            root = root._parent_manager

        # Build full field path by walking up the parent chain
        # Use the parent's nested_managers dict to find the actual parameter name
        path_parts = [param_name]
        current = self
        while current._parent_manager is not None:
            # Find this manager's parameter name in the parent's nested_managers dict
            parent_param_name = None
            for pname, manager in current._parent_manager.nested_managers.items():
                if manager is current:
                    parent_param_name = pname
                    break

            if parent_param_name:
                path_parts.insert(0, parent_param_name)

            current = current._parent_manager

        # Prepend root field_id
        path_parts.insert(0, root.field_id)
        field_path = '.'.join(path_parts)

        # ALWAYS emit cross-window signal for real-time updates
        # CRITICAL: Use root.object_instance (e.g., PipelineConfig), not self.object_instance (e.g., LazyStepWellFilterConfig)
        # This ensures type-based filtering works correctly - other windows check if they inherit from PipelineConfig
        root.context_value_changed.emit(field_path, value,
                                       root.object_instance, root.context_obj)

        # For 'enabled' changes: skip placeholder refresh to avoid infinite loops
        if param_name == 'enabled':
            return

        # For other changes: also trigger placeholder refresh
        root._on_parameter_changed_root(param_name, value)

    def _run_debounced_placeholder_refresh(self) -> None:
        """Execute the pending debounced refresh request."""
        exclude_param = self._pending_debounced_exclude_param
        self._pending_debounced_exclude_param = None
        self._refresh_with_live_context(exclude_param=exclude_param)

    def _on_nested_manager_complete(self, nested_manager) -> None:
        """Called by nested managers when they complete async widget creation."""
        if hasattr(self, '_pending_nested_managers'):
            # Find and remove this manager from pending dict
            key_to_remove = None
            for key, manager in self._pending_nested_managers.items():
                if manager is nested_manager:
                    key_to_remove = key
                    break

            if key_to_remove:
                del self._pending_nested_managers[key_to_remove]

            # If all nested managers are done, apply styling and refresh placeholders
            if len(self._pending_nested_managers) == 0:
                # STEP 1: Apply all styling callbacks now that ALL widgets exist
                with timer(f"  Apply styling callbacks", threshold_ms=5.0):
                    self._apply_all_styling_callbacks()

                # STEP 2: Refresh placeholders with live context
                # CRITICAL: Use _refresh_with_live_context() to collect live values from other open windows
                # This ensures new windows show unsaved changes from already-open windows
                with timer(f"  Complete placeholder refresh with live context (all nested ready)", threshold_ms=10.0):
                    self._refresh_with_live_context()

                # STEP 2.5: Apply post-placeholder callbacks (enabled styling that needs resolved values)
                with timer(f"  Apply post-placeholder callbacks (async)", threshold_ms=5.0):
                    self._apply_all_post_placeholder_callbacks()

                # STEP 3: Refresh enabled styling (after placeholders are resolved)
                # This ensures that nested configs with inherited enabled values get correct styling
                with timer(f"  Enabled styling refresh (all nested ready)", threshold_ms=5.0):
                    self._apply_to_nested_managers(lambda name, manager: manager._refresh_enabled_styling())

    def _process_nested_values_if_checkbox_enabled(self, name: str, manager: Any, current_values: Dict[str, Any]) -> None:
        """Process nested values if checkbox is enabled - convert dict back to dataclass."""
        if not hasattr(manager, 'get_current_values'):
            return

        # Check if this is an Optional dataclass with a checkbox
        param_type = self.parameter_types.get(name)

        if param_type and ParameterTypeUtils.is_optional_dataclass(param_type):
            # For Optional dataclasses, check if checkbox is enabled
            checkbox_widget = self.widgets.get(name)
            if checkbox_widget and hasattr(checkbox_widget, 'findChild'):
                from PyQt6.QtWidgets import QCheckBox
                checkbox = checkbox_widget.findChild(QCheckBox)
                if checkbox and not checkbox.isChecked():
                    # Checkbox is unchecked, set to None
                    current_values[name] = None
                    return
            # Also check if the value itself has enabled=False
            elif current_values.get(name) and not current_values[name].enabled:
                # Config exists but is disabled, set to None for serialization
                current_values[name] = None
                return

        # Get nested values from the nested form
        nested_values = manager.get_current_values()
        if nested_values:
            # Convert dictionary back to dataclass instance
            if param_type and hasattr(param_type, '__dataclass_fields__'):
                # Direct dataclass type
                current_values[name] = param_type(**nested_values)
            elif param_type and ParameterTypeUtils.is_optional_dataclass(param_type):
                # Optional dataclass type
                inner_type = ParameterTypeUtils.get_optional_inner_type(param_type)
                current_values[name] = inner_type(**nested_values)
            else:
                # Fallback to dictionary if type conversion fails
                current_values[name] = nested_values
        else:
            # No nested values, but checkbox might be checked - create empty instance
            if param_type and ParameterTypeUtils.is_optional_dataclass(param_type):
                inner_type = ParameterTypeUtils.get_optional_inner_type(param_type)
                current_values[name] = inner_type()  # Create with defaults

    def _make_widget_readonly(self, widget: QWidget):
        """
        Make a widget read-only without greying it out.

        Args:
            widget: Widget to make read-only
        """
        from PyQt6.QtWidgets import QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox, QTextEdit, QAbstractSpinBox

        if isinstance(widget, (QLineEdit, QTextEdit)):
            widget.setReadOnly(True)
            # Keep normal text color
            widget.setStyleSheet(f"color: {self.config.color_scheme.to_hex(self.config.color_scheme.text_primary)};")
        elif isinstance(widget, (QSpinBox, QDoubleSpinBox)):
            widget.setReadOnly(True)
            widget.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.NoButtons)
            # Keep normal text color
            widget.setStyleSheet(f"color: {self.config.color_scheme.to_hex(self.config.color_scheme.text_primary)};")
        elif isinstance(widget, QComboBox):
            # Disable but keep normal appearance
            widget.setEnabled(False)
            widget.setStyleSheet(f"""
                QComboBox:disabled {{
                    color: {self.config.color_scheme.to_hex(self.config.color_scheme.text_primary)};
                    background-color: {self.config.color_scheme.to_hex(self.config.color_scheme.input_bg)};
                }}
            """)
        elif isinstance(widget, QCheckBox):
            # Make non-interactive but keep normal appearance
            widget.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
            widget.setFocusPolicy(Qt.FocusPolicy.NoFocus)

    # ==================== CROSS-WINDOW CONTEXT UPDATE METHODS ====================

    def _emit_cross_window_change(self, param_name: str, value: object):
        """Emit cross-window context change signal.

        This is connected to parameter_changed signal for root managers.

        Args:
            param_name: Name of the parameter that changed
            value: New value
        """
        # OPTIMIZATION: Skip cross-window updates during batch operations (e.g., reset_all)
        if getattr(self, '_block_cross_window_updates', False):
            return

        if param_name in self._last_emitted_values:
            last_value = self._last_emitted_values[param_name]
            try:
                if last_value == value:
                    return
            except Exception:
                # If equality check fails, fall back to emitting
                pass

        self._last_emitted_values[param_name] = value

        # Invalidate live context cache by incrementing token
        type(self)._live_context_token_counter += 1

        field_path = f"{self.field_id}.{param_name}"
        self.context_value_changed.emit(field_path, value,
                                       self.object_instance, self.context_obj)

    def unregister_from_cross_window_updates(self):
        """Manually unregister this form manager from cross-window updates.

        This should be called when the window is closing (before destruction) to ensure
        other windows refresh their placeholders without this window's live values.
        """

        try:
            if self in self._active_form_managers:
                # CRITICAL FIX: Disconnect all signal connections BEFORE removing from registry
                # This prevents the closed window from continuing to receive signals and execute
                # _refresh_with_live_context() which causes runaway get_current_values() calls
                for manager in self._active_form_managers:
                    if manager is not self:
                        try:
                            # Disconnect this manager's signals from other manager
                            self.context_value_changed.disconnect(manager._on_cross_window_context_changed)
                            self.context_refreshed.disconnect(manager._on_cross_window_context_refreshed)
                            # Disconnect other manager's signals from this manager
                            manager.context_value_changed.disconnect(self._on_cross_window_context_changed)
                            manager.context_refreshed.disconnect(self._on_cross_window_context_refreshed)
                        except (TypeError, RuntimeError):
                            pass  # Signal already disconnected or object destroyed

                # Remove from registry
                self._active_form_managers.remove(self)

                # Invalidate live context caches so external listeners drop stale data
                type(self)._live_context_token_counter += 1

                # CRITICAL: Trigger refresh in all remaining windows
                # They were using this window's live values, now they need to revert to saved values
                for manager in self._active_form_managers:
                    # Refresh immediately (not deferred) since we're in a controlled close event
                    manager._refresh_with_live_context()

                # CRITICAL: Also notify external listeners (like pipeline editor)
                # They need to refresh their previews to drop this window's live values
                # Use special field_path to indicate window closed (triggers full refresh)
                logger.info(f"🔍 Notifying external listeners of window close: {self.field_id}")
                for listener, value_changed_handler, refresh_handler in self._external_listeners:
                    if value_changed_handler:
                        try:
                            logger.info(f"🔍   Calling value_changed_handler for {listener.__class__.__name__}")
                            value_changed_handler(
                                f"{self.field_id}.__WINDOW_CLOSED__",  # Special marker
                                None,
                                self.object_instance,
                                self.context_obj
                            )
                        except Exception as e:
                            logger.warning(f"Failed to notify external listener {listener.__class__.__name__}: {e}")
        except (ValueError, AttributeError):
            pass  # Already removed or list doesn't exist

    def _on_destroyed(self):
        """Cleanup when widget is destroyed - unregister from active managers."""
        # Call the manual unregister method
        # This is a fallback in case the window didn't call it explicitly
        self.unregister_from_cross_window_updates()

    def _on_cross_window_context_changed(self, field_path: str, new_value: object,
                                         editing_object: object, context_object: object):
        """Handle context changes from other open windows.

        Args:
            field_path: Full path to the changed field (e.g., "pipeline.well_filter")
            new_value: New value that was set
            editing_object: The object being edited in the other window
            context_object: The context object used by the other window
        """
        # Don't refresh if this is the window that made the change
        if editing_object is self.object_instance:
            logger.info(f"[{self.field_id}] Skipping cross-window update - same instance")
            return

        # Check if the change affects this form based on context hierarchy
        if not self._is_affected_by_context_change(editing_object, context_object):
            logger.info(f"[{self.field_id}] Skipping cross-window update - not affected by {type(editing_object).__name__}")
            return

        logger.info(f"[{self.field_id}] ✅ Cross-window update: {field_path} = {new_value} (from {type(editing_object).__name__})")

        # Pass the full field_path so nested managers can extract their relevant part
        # Example: "PipelineConfig.well_filter_config.well_filter"
        #   → Root manager extracts "well_filter_config"
        #   → Nested manager extracts "well_filter"
        self._schedule_cross_window_refresh(changed_field_path=field_path)

    def _on_cross_window_context_refreshed(self, editing_object: object, context_object: object):
        """Handle cascading placeholder refreshes from upstream windows.

        This is triggered when an upstream window's placeholders are refreshed due to
        changes in its parent context. This allows the refresh to cascade downstream.

        Example: GlobalPipelineConfig changes → PipelineConfig placeholders refresh →
                 PipelineConfig emits context_refreshed → Step editor refreshes

        Args:
            editing_object: The object whose placeholders were refreshed
            context_object: The context object used by that window
        """
        # Don't refresh if this is the window that was refreshed
        if editing_object is self.object_instance:
            return

        # Check if the refresh affects this form based on context hierarchy
        if not self._is_affected_by_context_change(editing_object, context_object):
            return

        # CRITICAL: Don't emit signal when refreshing due to another window's refresh
        # This prevents infinite ping-pong loops between windows
        # Example: GlobalPipelineConfig refresh → PipelineConfig refresh (no signal) → stops
        self._schedule_cross_window_refresh(emit_signal=False)

    def _is_affected_by_context_change(self, editing_object: object, context_object: object) -> bool:
        """Determine if a context change from another window affects this form.

        Hierarchical rules:
        - GlobalPipelineConfig changes affect: PipelineConfig, Steps, Functions
        - PipelineConfig changes affect: Steps in that pipeline, Functions in those steps
        - Step changes affect: Functions in that step

        MRO inheritance rules:
        - Config changes only affect configs that inherit from the changed type
        - Example: StepWellFilterConfig changes affect StreamingDefaults (inherits from it)
        - Example: StepWellFilterConfig changes DON'T affect ZarrConfig (unrelated)

        Args:
            editing_object: The object being edited in the other window
            context_object: The context object used by the other window

        Returns:
            True if this form should refresh placeholders due to the change
        """
        from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
        from openhcs.core.steps.abstract import AbstractStep

        # If other window is editing GlobalPipelineConfig, check if we use GlobalPipelineConfig as context
        if isinstance(editing_object, GlobalPipelineConfig):
            # We're affected if our context_obj is GlobalPipelineConfig OR if we're editing GlobalPipelineConfig
            # OR if we have no context (we use global context from thread-local)
            is_affected = (
                isinstance(self.context_obj, GlobalPipelineConfig) or
                isinstance(self.object_instance, GlobalPipelineConfig) or
                self.context_obj is None  # No context means we use global context
            )
            logger.info(f"[{self.field_id}] GlobalPipelineConfig change: context_obj={type(self.context_obj).__name__ if self.context_obj else 'None'}, affected={is_affected}")
            return is_affected

        # If other window is editing PipelineConfig, check if we're a step in that pipeline
        if PipelineConfig and isinstance(editing_object, PipelineConfig):
            # We're affected if our context_obj is a PipelineConfig (same type, scope matching handled elsewhere)
            # Don't use instance identity check - the editing window has a different instance than our saved context
            is_affected = isinstance(self.context_obj, PipelineConfig)
            logger.info(f"[{self.field_id}] PipelineConfig change: context_obj={type(self.context_obj).__name__ if self.context_obj else 'None'}, affected={is_affected}")
            return is_affected

        # If other window is editing a Step, check if we're a function in that step
        if isinstance(editing_object, AbstractStep):
            # We're affected if our context_obj is the same Step instance
            is_affected = self.context_obj is editing_object
            logger.info(f"[{self.field_id}] Step change: affected={is_affected}")
            return is_affected

        # CRITICAL: Check MRO inheritance for nested config changes
        # If the editing_object is a config instance, only refresh if this config inherits from it
        if self.dataclass_type:
            editing_type = type(editing_object)
            # Check if this config type inherits from the changed config type
            # Use try/except because issubclass requires both args to be classes
            try:
                if issubclass(self.dataclass_type, editing_type):
                    logger.info(f"[{self.field_id}] Affected by MRO inheritance: {self.dataclass_type.__name__} inherits from {editing_type.__name__}")
                    return True
            except TypeError:
                pass

        logger.info(f"[{self.field_id}] NOT affected by {type(editing_object).__name__} change")
        # Other changes don't affect this window
        return False

    def _schedule_cross_window_refresh(self, emit_signal: bool = True, changed_field_path: str = None):
        """Schedule a debounced placeholder refresh for cross-window updates.

        Args:
            emit_signal: Whether to emit context_refreshed signal after refresh.
                        Set to False when refresh is triggered by another window's
                        context_refreshed to prevent infinite ping-pong loops.
            changed_field_path: Optional full path of the field that changed (e.g., "PipelineConfig.well_filter_config.well_filter").
                               Used to extract the relevant field name for this manager and nested managers.
        """
        from PyQt6.QtCore import QTimer

        # Cancel existing timer if any
        if self._cross_window_refresh_timer is not None:
            self._cross_window_refresh_timer.stop()

        # Schedule new refresh after configured delay (debounce)
        self._cross_window_refresh_timer = QTimer()
        self._cross_window_refresh_timer.setSingleShot(True)
        self._cross_window_refresh_timer.timeout.connect(
            lambda: self._do_cross_window_refresh(emit_signal=emit_signal, changed_field_path=changed_field_path)
        )
        delay = max(0, self.CROSS_WINDOW_REFRESH_DELAY_MS)
        self._cross_window_refresh_timer.start(delay)

    def _find_live_values_for_type(self, ctx_type: type, live_context: dict) -> dict:
        """Find live values for a context type, checking both exact type and lazy/base equivalents.

        Args:
            ctx_type: The type to find live values for
            live_context: Dict mapping types to their live values

        Returns:
            Live values dict if found, None otherwise
        """
        if not live_context:
            return None

        # Check exact type match first
        if ctx_type in live_context:
            return live_context[ctx_type]

        # Check lazy/base equivalents
        from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
        from openhcs.config_framework.lazy_factory import get_base_type_for_lazy

        # If ctx_type is lazy, check its base type
        base_type = get_base_type_for_lazy(ctx_type)
        if base_type and base_type in live_context:
            return live_context[base_type]

        # If ctx_type is base, check its lazy type
        lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(ctx_type)
        if lazy_type and lazy_type in live_context:
            return live_context[lazy_type]

        return None

    def _is_scope_visible(self, other_scope_id: Optional[str], my_scope_id: Optional[str]) -> bool:
        """Check if other_scope_id is visible from my_scope_id using hierarchical matching.

        Rules:
        - None (global scope) is visible to everyone
        - Parent scopes are visible to child scopes (e.g., "plate1" visible to "plate1::step1")
        - Sibling scopes are NOT visible to each other (e.g., "plate1::step1" NOT visible to "plate1::step2")
        - Exact matches are visible

        Args:
            other_scope_id: The scope_id of the other manager
            my_scope_id: The scope_id of this manager

        Returns:
            True if other_scope_id is visible from my_scope_id
        """
        # Global scope (None) is visible to everyone
        if other_scope_id is None:
            return True

        # If I'm global scope (None), I can only see other global scopes
        if my_scope_id is None:
            return other_scope_id is None

        # Exact match
        if other_scope_id == my_scope_id:
            return True

        # Check if other_scope_id is a parent scope (prefix match with :: separator)
        # e.g., "plate1" is parent of "plate1::step1"
        if my_scope_id.startswith(other_scope_id + "::"):
            return True

        # Not visible (sibling or unrelated scope)
        return False

    def _collect_live_context_from_other_windows(self) -> LiveContextSnapshot:
        """Collect live values from other open form managers for context resolution.

        Returns a dict mapping object types to their current live values.
        This allows matching by type rather than instance identity.
        Maps both the actual type AND its lazy/non-lazy equivalent for flexible matching.

        CRITICAL: Only collects context from PARENT types in the hierarchy, not from the same type.
        E.g., PipelineConfig editor collects GlobalPipelineConfig but not other PipelineConfig instances.
        This prevents a window from using its own live values for placeholder resolution.

        CRITICAL: Uses get_user_modified_values() to only collect concrete (non-None) values.
        This ensures proper inheritance: if PipelineConfig has None for a field, it won't
        override GlobalPipelineConfig's concrete value in the Step editor's context.

        CRITICAL: Only collects from managers with the SAME scope_id (same orchestrator/plate).
        This prevents cross-contamination between different orchestrators.
        GlobalPipelineConfig (scope_id=None) is shared across all scopes.
        """
        from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
        from openhcs.config_framework.lazy_factory import get_base_type_for_lazy

        live_context = {}
        alias_context = {}
        my_type = type(self.object_instance)


        for manager in self._active_form_managers:
            if manager is self:
                continue

            # CRITICAL: Only collect from managers in the same scope hierarchy OR from global scope (None)
            # Hierarchical scope matching:
            # - None (global) is visible to everyone
            # - "plate1" is visible to "plate1::step1" (parent scope)
            # - "plate1::step1" is NOT visible to "plate1::step2" (sibling scope)
            if not self._is_scope_visible(manager.scope_id, self.scope_id):
                continue  # Different scope - skip

            # CRITICAL: Get only user-modified (concrete, non-None) values
            live_values = manager.get_user_modified_values()
            obj_type = type(manager.object_instance)

            # CRITICAL: Only skip if this is EXACTLY the same type as us
            if obj_type == my_type:
                continue

            # Map by the actual type
            live_context[obj_type] = live_values

            # Also map by the base/lazy equivalent type for flexible matching
            base_type = get_base_type_for_lazy(obj_type)
            if base_type and base_type != obj_type:
                alias_context.setdefault(base_type, live_values)

            lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(obj_type)
            if lazy_type and lazy_type != obj_type:
                alias_context.setdefault(lazy_type, live_values)

        # Apply alias mappings only where no direct mapping exists
        for alias_type, values in alias_context.items():
            if alias_type not in live_context:
                live_context[alias_type] = values

        type(self)._live_context_token_counter += 1
        token = type(self)._live_context_token_counter
        return LiveContextSnapshot(token=token, values=live_context)

    def _do_cross_window_refresh(self, emit_signal: bool = True, changed_field_path: str = None):
        """Actually perform the cross-window placeholder refresh using live values from other windows.

        Args:
            emit_signal: Whether to emit context_refreshed signal after refresh.
                        Set to False when refresh is triggered by another window's
                        context_refreshed to prevent infinite ping-pong loops.
            changed_field_path: Optional full path of the field that changed (e.g., "PipelineConfig.well_filter_config.well_filter").
                               Used to extract the relevant field name for this manager and nested managers.
        """
        # Collect live context values from other open windows
        live_context = self._collect_live_context_from_other_windows()

        # Extract the relevant field name for this manager level
        # Example: "PipelineConfig.well_filter_config.well_filter" → extract "well_filter_config" for root, "well_filter" for nested
        changed_field_name = None
        if changed_field_path:
            # Split path and get the first component after the type name
            # Format: "TypeName.field1.field2.field3" → ["TypeName", "field1", "field2", "field3"]
            path_parts = changed_field_path.split('.')
            if len(path_parts) > 1:
                # For root manager: use the first field name (e.g., "well_filter_config")
                changed_field_name = path_parts[1]

        # Refresh placeholders for this form using live context
        # CRITICAL: Only refresh the specific field that changed (if provided)
        # This dramatically reduces refresh time by skipping unaffected fields
        self._refresh_specific_placeholder(changed_field_name, live_context=live_context)

        # Refresh nested managers with the remaining path
        # Example: "PipelineConfig.well_filter_config.well_filter" → nested manager gets "well_filter_config.well_filter"
        nested_field_path = None
        if changed_field_path and changed_field_name:
            # Remove the type name and first field from path
            # "PipelineConfig.well_filter_config.well_filter" → "well_filter_config.well_filter"
            path_parts = changed_field_path.split('.')
            if len(path_parts) > 2:
                nested_field_path = '.'.join(path_parts[2:])

        self._apply_to_nested_managers(
            lambda name, manager: manager._refresh_specific_placeholder_from_path(
                parent_field_name=changed_field_name,
                remaining_path=nested_field_path,
                live_context=live_context
            )
        )

        # CRITICAL: Also refresh enabled styling for all nested managers
        # This ensures that when 'enabled' field changes in another window, styling updates here
        # Example: User changes napari_streaming_config.enabled in one window, other windows update styling
        self._refresh_enabled_styling()

        # CRITICAL: Only emit context_refreshed signal if requested
        # When emit_signal=False, this refresh was triggered by another window's context_refreshed,
        # so we don't emit to prevent infinite ping-pong loops between windows
        # Example: GlobalPipelineConfig value change → emits signal → PipelineConfig refreshes (no emit) → stops
        if emit_signal:
            # This allows Step editors to know that PipelineConfig's effective context changed
            # even though no actual field values were modified (only placeholders updated)
            # Example: GlobalPipelineConfig change → PipelineConfig placeholders update → Step editor needs to refresh
            self.context_refreshed.emit(self.object_instance, self.context_obj)
