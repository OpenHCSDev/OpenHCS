"""
Dramatically simplified PyQt parameter form manager.

This demonstrates how the widget implementation can be drastically simplified
by leveraging the comprehensive shared infrastructure we've built.
"""

import dataclasses
import logging
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Type, Optional, Tuple, Union, List, Set
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
    scopes: Dict[str, Optional[str]] = field(default_factory=dict)  # Maps config type name to scope ID


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

    # Class-level registry mapping scope_id to parent window (QDialog)
    # Used to focus existing windows instead of opening duplicates
    # Format: {scope_id: QDialog} where scope_id is str or None (global)
    _scope_to_window: Dict[Optional[str], 'QWidget'] = {}

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
    CROSS_WINDOW_REFRESH_DELAY_MS = 100  # INSTANT: No debounce for cross-window updates (batching handles it)

    _live_context_token_counter = 0

    # Class-level mapping from object instances to their form managers
    # Used to retrieve window_open_snapshot when window closes
    _object_to_manager: Dict[int, 'ParameterFormManager'] = {}

    # Class-level token cache for live context collection
    _live_context_cache: Optional['TokenCache'] = None  # Initialized on first use

    # PERFORMANCE: Class-level cache for global context (shared across all instances)
    # This prevents every nested form from rebuilding the global context independently
    _cached_global_context_token: Optional[int] = None
    _cached_global_context_instance: Optional[Any] = None

    # PERFORMANCE: Type-based cache for unsaved changes detection (Phase 1-ALT)
    # Map: (config_type, scope_id) → set of changed field names
    # Example: (LazyWellFilterConfig, "plate::step_6") → {'well_filter', 'well_filter_mode'}
    # CRITICAL: This cache is SCOPED to prevent cross-step contamination
    # When step 6's editor has unsaved changes, it should NOT affect step 0's unsaved changes check
    # CRITICAL: This cache is invalidated when the live context token changes
    # The token changes when: form values change, windows open/close, resets happen
    # When the token changes, the cache is stale and must be cleared
    _configs_with_unsaved_changes: Dict[Tuple[Type, Optional[str]], Set[str]] = {}
    _configs_with_unsaved_changes_token: int = -1  # Token when cache was last populated
    MAX_CONFIG_TYPE_CACHE_ENTRIES = 50  # Monitor cache size (log warning if exceeded)

    # PERFORMANCE: Phase 3 - Batch cross-window updates
    # Store manager reference to avoid fragile string matching
    # Format: List[(manager, param_name, value, obj_instance, context_obj)]
    _pending_cross_window_changes: List[Tuple['ParameterFormManager', str, Any, Any, Any]] = []
    _cross_window_batch_timer: Optional['QTimer'] = None

    # PERFORMANCE: Universal reactive update coordinator - synchronizes EVERYTHING
    # Batches ALL reactive updates in single pass: listeners, placeholders, flashes
    _pending_listener_updates: Set[Any] = set()  # External listeners (PlateManager, etc.)
    _pending_placeholder_refreshes: Set['ParameterFormManager'] = set()  # Form managers needing refresh
    _pending_flash_widgets: Set[Tuple[Any, Any]] = set()  # (widget/item, color) tuples
    _pending_flash_restorations: List[Any] = []  # Flash animators awaiting restoration (batched to prevent event loop blocking)
    _flash_restoration_timer: Optional['QTimer'] = None  # Single timer for ALL flash restorations
    _current_batch_changed_fields: Set[str] = set()  # Field identifiers that changed in current batch
    _coordinator_timer: Optional['QTimer'] = None

    # PERFORMANCE: MRO inheritance cache - maps (parent_type, field_name) → set of child types
    # This enables O(1) lookup of which config types can inherit a field from a parent type
    # Example: (PathPlanningConfig, 'output_dir_suffix') → {StepMaterializationConfig, ...}
    # Built once at startup via _build_mro_inheritance_cache()
    _mro_inheritance_cache: Dict[Tuple[Type, str], Set[Type]] = {}

    # PERFORMANCE: MRO inheritance cache - maps (parent_type, field_name) → set of child types
    # This enables O(1) lookup of which config types can inherit a field from a parent type
    # Example: (PathPlanningConfig, 'output_dir_suffix') → {StepMaterializationConfig, ...}
    _mro_inheritance_cache: Dict[Tuple[Type, str], Set[Type]] = {}

    @classmethod
    def _build_mro_inheritance_cache(cls):
        """Build cache of which config types can inherit from which other types via MRO.

        This is called once at startup and enables O(1) lookup of affected types when
        marking unsaved changes. Uses introspection to discover all config types generically.

        Example cache entry:
            (PathPlanningConfig, 'output_dir_suffix') → {StepMaterializationConfig, LazyStepMaterializationConfig}

        This means when PathPlanningConfig.output_dir_suffix changes, we also mark
        StepMaterializationConfig as having unsaved changes (because it inherits via MRO).
        """
        from openhcs.config_framework.cache_warming import _extract_all_dataclass_types
        from openhcs.core.config import GlobalPipelineConfig
        import dataclasses

        logger.info("🔧 Building MRO inheritance cache for unsaved changes detection...")

        # Introspect all config types in the hierarchy (generic, no hardcoding)
        all_config_types = _extract_all_dataclass_types(GlobalPipelineConfig)
        logger.info(f"🔧 Found {len(all_config_types)} config types to analyze")

        # PERFORMANCE: Cache fields() results to avoid repeated introspection
        fields_cache = {}
        for config_type in all_config_types:
            if dataclasses.is_dataclass(config_type):
                try:
                    fields_cache[config_type] = {f.name for f in dataclasses.fields(config_type)}
                except TypeError:
                    fields_cache[config_type] = set()

        # For each config type, build reverse mapping: (parent_type, field_name) → child_types
        for child_type in all_config_types:
            if child_type not in fields_cache:
                continue

            # Get all fields on this child type
            child_field_names = fields_cache[child_type]

            # Filter MRO to only dataclasses once
            dataclass_mro = [c for c in child_type.__mro__
                           if c != child_type and c in fields_cache]

            # Check which types in the MRO have this field
            # If a parent type has this field, the child can inherit from it
            for field_name in child_field_names:
                for mro_class in dataclass_mro:
                    # Check if mro_class has this field (O(1) set lookup)
                    if field_name in fields_cache[mro_class]:
                        cache_key = (mro_class, field_name)
                        if cache_key not in cls._mro_inheritance_cache:
                            cls._mro_inheritance_cache[cache_key] = set()
                        cls._mro_inheritance_cache[cache_key].add(child_type)

        logger.info(f"🔧 Built MRO inheritance cache with {len(cls._mro_inheritance_cache)} entries")

        # Log all WellFilterConfig-related entries for debugging
        if cls._mro_inheritance_cache:
            for cache_key, child_types in cls._mro_inheritance_cache.items():
                parent_type, field_name = cache_key
                if 'WellFilter' in parent_type.__name__:
                    child_names = [t.__name__ for t in child_types]
                    logger.info(f"🔧   WellFilter cache: ({parent_type.__name__}, '{field_name}') → {child_names}")

    @classmethod
    def _clear_unsaved_changes_cache(cls, reason: str):
        """Clear the entire unsaved changes cache.

        This should be called when the comparison basis changes globally:
        - Save happens (saved values change)
        - Reset happens (live values revert to saved)

        NOTE: For window close, use _clear_unsaved_changes_cache_for_scope() instead
        to avoid clearing entries for other open windows (like step editors).
        """
        cls._configs_with_unsaved_changes.clear()
        logger.debug(f"🔍 Cleared unsaved changes cache: {reason}")

    @classmethod
    def _clear_unsaved_changes_cache_for_scope(cls, scope_id: Optional[str], reason: str):
        """Clear unsaved changes cache entries for a specific scope only.

        This should be called when a window closes to avoid clearing entries
        for other windows that are still open. For example, when a PipelineConfig
        editor closes, we should NOT clear entries for step editors (which have
        scope_ids like "plate::step_token").

        The cache is keyed by (config_type, scope_id) tuples, so we filter by
        matching the scope_id component.

        Args:
            scope_id: The scope to clear. If None, clears entries with None scope.
            reason: Debug reason string for logging.
        """
        keys_to_remove = [key for key in cls._configs_with_unsaved_changes if key[1] == scope_id]
        for key in keys_to_remove:
            del cls._configs_with_unsaved_changes[key]
        logger.debug(f"🔍 Cleared unsaved changes cache for scope '{scope_id}': {reason} ({len(keys_to_remove)} entries removed)")

    @classmethod
    def _invalidate_config_in_cache(cls, config_type: Type):
        """Invalidate a specific config type in the unsaved changes cache.

        This should be called when a value changes - we need to re-check if there
        are still unsaved changes (user might have typed the value back to saved state).
        """
        if config_type in cls._configs_with_unsaved_changes:
            del cls._configs_with_unsaved_changes[config_type]
            logger.debug(f"🔍 Invalidated cache for {config_type.__name__}")

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
    def collect_live_context(cls, scope_filter: Optional[Union[str, 'Path']] = None) -> LiveContextSnapshot:
        """
        Collect live context from all active form managers in scope.

        This is a class method that can be called from anywhere (e.g., PipelineEditor)
        to get the current live context for resolution.

        PERFORMANCE: Caches the snapshot and only invalidates when token changes.
        The token is incremented whenever any form value changes.

        Args:
            scope_filter: Optional scope filter:
                         - None: No filtering - collect ALL managers (global + all scopes)
                         - plate_path: Filter to specific scope (global + that plate)

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

            # CRITICAL: Include thread-local global config even if no GlobalPipelineConfig window is open
            # This ensures placeholders resolve correctly when PipelineConfig opens before GlobalPipelineConfig
            from openhcs.config_framework.context_manager import get_base_global_config
            from openhcs.core.config import GlobalPipelineConfig
            thread_local_global = get_base_global_config()
            if thread_local_global is not None:
                # Extract non-None values from thread-local global config
                global_values = {}
                from dataclasses import fields as dataclass_fields
                for field in dataclass_fields(thread_local_global):
                    value = getattr(thread_local_global, field.name)
                    if value is not None:
                        global_values[field.name] = value
                if global_values:
                    live_context[GlobalPipelineConfig] = global_values
                    logger.info(f"🔍 collect_live_context: Added thread-local GlobalPipelineConfig with {len(global_values)} values: {list(global_values.keys())[:5]}")

                    # DEBUG: Log display and streaming configs
                    for key in ['napari_display_config', 'fiji_display_config', 'streaming_defaults', 'napari_streaming_config', 'fiji_streaming_config']:
                        if key in global_values:
                            logger.info(f"🔍 collect_live_context (thread-local): {key} = {global_values[key]}")
                        else:
                            logger.info(f"🔍 collect_live_context (thread-local): {key} NOT IN global_values")

            # Polymorphic scope filtering via enum factory method
            from openhcs.config_framework.dual_axis_resolver import ScopeFilterMode
            value_filter_mode = ScopeFilterMode.for_value_collection(scope_filter)

            for manager in cls._active_form_managers:
                # Enum handles str normalization internally
                if not value_filter_mode.should_include(manager.scope_id, scope_filter):
                    logger.info(
                        f"🔍 collect_live_context: Skipping manager {manager.field_id} "
                        f"(scope_id={manager.scope_id}) - filtered by {value_filter_mode.name}"
                    )
                    continue

                # Collect values
                live_values = manager.get_user_modified_values()
                obj_type = type(manager.object_instance)

                # Debug logging for num_workers
                if 'num_workers' in live_values:
                    logger.info(f"🔍 collect_live_context: {manager.field_id} has num_workers={live_values['num_workers']}")

                # DEBUG: Log streaming config values for GlobalPipelineConfig
                if manager.field_id == 'GlobalPipelineConfig':
                    for key in ['streaming_defaults', 'napari_streaming_config', 'fiji_streaming_config', 'napari_display_config', 'fiji_display_config']:
                        if key in live_values:
                            logger.info(f"🔍 collect_live_context: GlobalPipelineConfig.{key} = {live_values[key]}")
                        else:
                            logger.info(f"🔍 collect_live_context: GlobalPipelineConfig.{key} NOT IN live_values")

                # Add ALL managers (global + scoped) to live_context so resolution sees scoped edits.
                from openhcs.config_framework.lazy_factory import is_global_config_type
                from dataclasses import is_dataclass
                if manager.scope_id is None and is_global_config_type(obj_type):
                    # For GlobalPipelineConfig, filter out nested dataclass instances to avoid masking thread-local
                    scalar_values = {k: v for k, v in live_values.items() if not is_dataclass(v)}
                    if obj_type in live_context:
                        live_context[obj_type].update(scalar_values)
                    else:
                        live_context[obj_type] = scalar_values
                    logger.info(f"🔍 collect_live_context: Added GLOBAL manager {manager.field_id} to live_context with {len(scalar_values)} scalar keys: {list(scalar_values.keys())[:5]}")
                else:
                    live_context[obj_type] = live_values
                    logger.info(f"🔍 collect_live_context: Added manager {manager.field_id} (scope_id={manager.scope_id}) to live_context with {len(live_values)} keys: {list(live_values.keys())[:5]}")
                    # Bump live context token when any scoped/global manager contributes live values
                    cls._live_context_token_counter += 1

                # Track scope-specific mappings (for step-level overlays)
                if manager.scope_id:
                    scoped_live_context.setdefault(manager.scope_id, {})[obj_type] = live_values
                    logger.info(f"🔍 collect_live_context: Added to scoped_live_context[{manager.scope_id}][{obj_type.__name__}] with {len(live_values)} keys: {list(live_values.keys())[:5]}")

                # Alias mappings for all managers
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

            # Build scopes dict - uses STRICT_HIERARCHY to prevent scope contamination
            scopes_dict: Dict[str, Optional[str]] = {}
            scopes_filter_mode = ScopeFilterMode.for_scopes_dict()
            logger.info(f"🔍 BUILD SCOPES: Starting with {len(cls._active_form_managers)} active managers")

            def add_manager_to_scopes(manager, is_nested=False):
                """Helper to add a manager and its nested managers to scopes_dict."""
                # Enum handles str normalization internally
                if not scopes_filter_mode.should_include(manager.scope_id, scope_filter):
                    logger.info(f"🔍 BUILD SCOPES: Skipping manager {manager.field_id} (scope_id={manager.scope_id}) - filtered by {scopes_filter_mode.name}")
                    return

                obj_type = type(manager.object_instance)
                type_name = obj_type.__name__

                # Get base and lazy type names for this config
                base_type = get_base_type_for_lazy(obj_type)
                base_name = base_type.__name__ if base_type and base_type != obj_type else None

                lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(obj_type)
                lazy_name = lazy_type.__name__ if lazy_type and lazy_type != obj_type else None

                # Determine the canonical scope for this config family (base + lazy)
                # CRITICAL: If lazy type already has a more specific scope, use that for base type too
                # Example: LazyStreamingDefaults (plate_path) should set StreamingDefaults to plate_path
                # even if GlobalPipelineConfig tries to set StreamingDefaults to None later
                # EXCEPTION: Global configs must ALWAYS have scope=None, never inherit from lazy versions
                canonical_scope = manager.scope_id

                # GENERIC SCOPE RULE: Global configs must always have scope=None
                from openhcs.config_framework.lazy_factory import is_global_config_type
                if is_global_config_type(manager.dataclass_type):
                    canonical_scope = None
                    logger.info(f"🔍 BUILD SCOPES: Forcing {type_name} scope to None (global config must always be global)")
                else:
                    # Check if lazy equivalent already has a more specific scope
                    if lazy_name and lazy_name in scopes_dict:
                        existing_lazy_scope = scopes_dict[lazy_name]
                        if existing_lazy_scope is not None and canonical_scope is None:
                            canonical_scope = existing_lazy_scope
                            logger.info(f"🔍 BUILD SCOPES: Using lazy scope {existing_lazy_scope} for {type_name} (lazy {lazy_name} already mapped)")

                    # Check if base equivalent already has a more specific scope
                    if base_name and base_name in scopes_dict:
                        existing_base_scope = scopes_dict[base_name]
                        if existing_base_scope is not None and canonical_scope is None:
                            canonical_scope = existing_base_scope
                            logger.info(f"🔍 BUILD SCOPES: Using base scope {existing_base_scope} for {type_name} (base {base_name} already mapped)")

                # Map the actual type
                if type_name not in scopes_dict:
                    scopes_dict[type_name] = canonical_scope
                    logger.info(f"🔍 BUILD SCOPES: {type_name} -> {canonical_scope} (from {manager.field_id}, nested={is_nested})")
                else:
                    # Already exists - only overwrite if new scope is MORE SPECIFIC (not None)
                    existing_scope = scopes_dict[type_name]
                    if existing_scope is None and canonical_scope is not None:
                        scopes_dict[type_name] = canonical_scope
                        logger.info(f"🔍 BUILD SCOPES: {type_name} -> {canonical_scope} (OVERWRITE: was None, now {canonical_scope})")
                    else:
                        logger.info(f"🔍 BUILD SCOPES: {type_name} already mapped to {existing_scope}, skipping {canonical_scope}")

                # Also map base/lazy equivalents with the same canonical scope
                # CRITICAL: NEVER map global configs to a non-None scope
                # Global configs should ALWAYS have scope=None (global scope)
                if base_name:
                    # GENERIC SCOPE RULE: Global configs must always have scope=None
                    # Use base_type from get_base_type_for_lazy (line 583), not MRO parent
                    from openhcs.config_framework.lazy_factory import is_global_config_type
                    if base_type and is_global_config_type(base_type) and canonical_scope is not None:
                        logger.info(f"🔍 BUILD SCOPES: Skipping {base_name} -> {canonical_scope} (global config must always have scope=None)")
                    elif base_name not in scopes_dict:
                        scopes_dict[base_name] = canonical_scope
                        logger.info(f"🔍 BUILD SCOPES: {base_name} -> {canonical_scope} (base of {type_name})")
                    elif scopes_dict[base_name] is None and canonical_scope is not None:
                        scopes_dict[base_name] = canonical_scope
                        logger.info(f"🔍 BUILD SCOPES: {base_name} -> {canonical_scope} (OVERWRITE base: was None, now {canonical_scope})")

                if lazy_name:
                    if lazy_name not in scopes_dict:
                        scopes_dict[lazy_name] = canonical_scope
                        logger.info(f"🔍 BUILD SCOPES: {lazy_name} -> {canonical_scope} (lazy of {type_name})")
                    elif scopes_dict[lazy_name] is None and canonical_scope is not None:
                        scopes_dict[lazy_name] = canonical_scope
                        logger.info(f"🔍 BUILD SCOPES: {lazy_name} -> {canonical_scope} (OVERWRITE lazy: was None, now {canonical_scope})")

                # Recursively add nested managers
                for _, nested_manager in manager.nested_managers.items():
                    add_manager_to_scopes(nested_manager, is_nested=True)

            for manager in cls._active_form_managers:
                logger.info(f"🔍 BUILD SCOPES: Processing manager {manager.field_id} with {len(manager.nested_managers)} nested managers")
                if 'streaming' in str(manager.nested_managers.keys()).lower():
                    logger.info(f"🔍 BUILD SCOPES: Manager {manager.field_id} has streaming-related nested managers: {list(manager.nested_managers.keys())}")
                add_manager_to_scopes(manager, is_nested=False)

            logger.info(f"🔍 BUILD SCOPES: Final scopes_dict has {len(scopes_dict)} entries")

            # Create snapshot with current token (don't increment - that happens on value change)
            token = cls._live_context_token_counter
            return LiveContextSnapshot(token=token, values=live_context, scoped_values=scoped_live_context, scopes=scopes_dict)

        # Use token cache to get or compute
        snapshot = cls._live_context_cache.get_or_compute(cache_key, compute_live_context)

        import logging
        logger = logging.getLogger(__name__)
        if snapshot.token == cls._live_context_token_counter:
            logger.debug(f"✅ collect_live_context: CACHE HIT (token={cls._live_context_token_counter}, scope={scope_filter})")

        return snapshot

    def _create_snapshot_for_this_manager(self) -> LiveContextSnapshot:
        """Create a snapshot containing ONLY this form manager's values.

        This is used when a window closes to create a "before" snapshot that only
        contains the values from the closing window, not all active form managers.

        Returns:
            LiveContextSnapshot with only this manager's values
        """
        from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
        from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService

        logger.debug(f"🔍 _create_snapshot_for_this_manager: Creating snapshot for {self.field_id} (scope={self.scope_id})")

        live_context = {}
        scoped_live_context: Dict[str, Dict[type, Dict[str, Any]]] = {}
        alias_context = {}

        # Collect values from THIS manager only
        live_values = self.get_user_modified_values()
        obj_type = type(self.object_instance)

        # Map by the actual type
        live_context[obj_type] = live_values

        # Track scope-specific mappings (for step-level overlays)
        if self.scope_id:
            scoped_live_context.setdefault(self.scope_id, {})[obj_type] = live_values

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

        # Create snapshot with current token
        token = type(self)._live_context_token_counter
        logger.debug(f"🔍 _create_snapshot_for_this_manager: Created snapshot with scoped_values keys: {list(scoped_live_context.keys())}")
        return LiveContextSnapshot(token=token, values=live_context, scoped_values=scoped_live_context)

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
    def focus_existing_window(cls, scope_id: Optional[str]) -> bool:
        """Focus an existing window with the given scope_id if one exists.

        This enables "focus-instead-of-duplicate" behavior where opening a window
        with the same scope_id will focus the existing window instead of creating
        a new one.

        Args:
            scope_id: The scope identifier to look up. Can be None for global scope.

        Returns:
            True if an existing window was found and focused, False otherwise.
        """
        if scope_id in cls._scope_to_window:
            window = cls._scope_to_window[scope_id]
            try:
                # Verify the window still exists and is valid
                if window and not window.isHidden():
                    window.show()
                    window.raise_()
                    window.activateWindow()
                    logger.debug(f"Focused existing window for scope_id={scope_id}")
                    return True
                else:
                    # Window was closed/hidden, remove stale entry
                    del cls._scope_to_window[scope_id]
                    logger.debug(f"Removed stale window entry for scope_id={scope_id}")
            except RuntimeError:
                # Window was deleted, remove stale entry
                del cls._scope_to_window[scope_id]
                logger.debug(f"Removed deleted window entry for scope_id={scope_id}")
        return False

    @classmethod
    def register_window_for_scope(cls, scope_id: Optional[str], window: 'QWidget'):
        """Register a window for a scope_id to enable focus-instead-of-duplicate behavior.

        Args:
            scope_id: The scope identifier. Can be None for global scope.
            window: The window (QDialog) to register.
        """
        cls._scope_to_window[scope_id] = window
        logger.debug(f"Registered window for scope_id={scope_id}: {window.__class__.__name__}")

    @classmethod
    def unregister_window_for_scope(cls, scope_id: Optional[str]):
        """Unregister a window for a scope_id.

        Should be called when a window closes.

        Args:
            scope_id: The scope identifier to unregister.
        """
        if scope_id in cls._scope_to_window:
            del cls._scope_to_window[scope_id]
            logger.debug(f"Unregistered window for scope_id={scope_id}")

    @classmethod
    def trigger_global_cross_window_refresh(cls, source_scope_id: Optional[str] = None):
        """Trigger cross-window refresh for all active form managers.

        This is called when global config changes (e.g., from plate manager code editor)
        to ensure all open windows refresh their placeholders with the new values.

        CRITICAL SCOPE RULE: Only refresh managers with EQUAL OR MORE SPECIFIC scopes than source.
        This prevents parent scopes from being refreshed when child scopes change.
        Example: PipelineConfig (plate scope) changes should NOT refresh GlobalPipelineConfig (global scope).

        Args:
            source_scope_id: Optional scope ID of the manager that triggered the change.
                           If None, refresh all managers (global change).
                           If specified, only refresh managers with equal or more specific scopes.

        CRITICAL: Also emits context_refreshed signal for each manager so that
        downstream components (like function pattern editor) can refresh their state.

        CRITICAL: Also notifies external listeners (like PipelineEditor) directly,
        especially important when all managers are unregistered (e.g., after cancel).
        """
        from openhcs.config_framework.dual_axis_resolver import get_scope_specificity
        source_specificity = get_scope_specificity(source_scope_id)

        logger.debug(f"Triggering global cross-window refresh for {len(cls._active_form_managers)} active managers (source_scope={source_scope_id}, source_specificity={source_specificity})")

        for manager in cls._active_form_managers:
            # PERFORMANCE: Skip managers with less specific scopes than source
            # They won't see any changes from the source scope anyway
            if source_scope_id is not None:
                manager_specificity = get_scope_specificity(manager.scope_id)
                if manager_specificity < source_specificity:
                    logger.debug(f"Skipping refresh for {manager.field_id} (specificity={manager_specificity} < source_specificity={source_specificity})")
                    continue

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
        logger.debug(f"🔍 _notify_external_listeners_refreshed called from {self.field_id}, notifying {len(self._external_listeners)} listeners")
        for listener, value_changed_handler, refresh_handler in self._external_listeners:
            if refresh_handler:  # Skip if None
                try:
                    logger.debug(f"🔍   Calling refresh_handler for {listener.__class__.__name__}")
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

            # Register this manager in the object-to-manager mapping
            type(self)._object_to_manager[id(self.object_instance)] = self

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
            # NOTE: Global context cache is now class-level (see _cached_global_context_token below)
            self._cached_parent_contexts: Dict[int, Tuple[int, Any]] = {}

            # Placeholder text cache (value-based, not token-based)
            # Key: (param_name, hash of live context values) -> placeholder text
            # This prevents unnecessary re-resolution when unrelated configs change
            # No size limit needed - cache naturally stays small (< 20 params × few context states)
            self._placeholder_text_cache: Dict[Tuple, str] = {}

            # Last applied placeholder text per parameter (for flash detection)
            # Key: param_name -> last placeholder text
            # Used to detect when placeholder values change and trigger flash animations
            self._last_placeholder_text: Dict[str, str] = {}

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
                # DEBUG: Log placeholder candidates for AnalysisConsolidationConfig, PlateMetadataConfig, and StreamingDefaults
                if 'AnalysisConsolidation' in str(self.dataclass_type) or 'PlateMetadata' in str(self.dataclass_type) or 'Streaming' in str(self.dataclass_type) or 'PathPlanning' in str(self.dataclass_type) or 'StepWellFilter' in str(self.dataclass_type) or 'StepMaterialization' in str(self.dataclass_type):
                    logger.info(f"🔍 PLACEHOLDER CANDIDATES: {self.dataclass_type.__name__} - parameters={self.parameters}")
                    logger.info(f"🔍 PLACEHOLDER CANDIDATES: {self.dataclass_type.__name__} - _placeholder_candidates={self._placeholder_candidates}")

                # DEBUG: Log cache for GlobalPipelineConfig
                if self.dataclass_type and self.dataclass_type.__name__ == 'GlobalPipelineConfig':
                    for key in ['napari_streaming_config', 'fiji_streaming_config', 'napari_display_config', 'fiji_display_config']:
                        if key in self._current_value_cache:
                            logger.info(f"🔍 CACHE INIT (GlobalPipelineConfig): {key} = {self._current_value_cache[key]}")
                        else:
                            logger.info(f"🔍 CACHE INIT (GlobalPipelineConfig): {key} NOT IN CACHE")
                    logger.info(f"🔍 PLACEHOLDER CANDIDATES: {self.dataclass_type.__name__} - _placeholder_candidates={self._placeholder_candidates}")

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
                # This triggers _emit_cross_window_change which emits context_value_changed
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

            # CRITICAL FIX: Skip placeholder refresh in __init__ for SYNC widget creation
            # In sync mode, widgets are created but NOT visible yet when __init__ completes
            # Placeholders will be applied by the deferred callback in build_form() after widgets are visible
            # In async mode, this refresh is also skipped because placeholders are applied after async completion
            # ONLY refresh here for nested managers in async mode (they need initial state before parent refreshes)
            #
            # TL;DR: Placeholder refresh moved to build_form() deferred callbacks for both sync and async paths
            logger.info(f"🔍 INIT PLACEHOLDER SKIP: {self.field_id} - Skipping placeholder refresh in __init__, will be handled by build_form() deferred callbacks")

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

    def _get_resolution_type_for_field(self, param_name: str) -> Type:
        """Get the type to use for placeholder resolution.

        For dataclass types, returns the dataclass type itself.
        For non-dataclass types (like FunctionStep), returns the field's type.
        This allows step editor to resolve lazy dataclass fields through context.
        """
        import dataclasses

        # If dataclass_type is a dataclass, use it directly
        if dataclasses.is_dataclass(self.dataclass_type):
            return self.dataclass_type

        # Otherwise, get the field's type from parameter_types
        field_type = self.parameter_types.get(param_name)
        if field_type:
            from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
            if ParameterTypeUtils.is_optional(field_type):
                field_type = ParameterTypeUtils.get_optional_inner_type(field_type)
            return field_type

        # Fallback to dataclass_type
        return self.dataclass_type

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
                    logger.info(f"🔍 WIDGET CREATION: {self.field_id} creating {len(sync_params)} sync widgets")
                    with timer(f"        Create {len(sync_params)} initial widgets (sync)", threshold_ms=5.0):
                        for param_info in sync_params:
                            widget = self._create_widget_for_param(param_info)
                            content_layout.addWidget(widget)
                    logger.info(f"🔍 WIDGET CREATION: {self.field_id} sync widgets created")

                    # CRITICAL FIX: Skip early placeholder refresh entirely
                    # The issue is that nested managers created in async batches will have their placeholders
                    # applied before their widgets are added to the layout, causing them not to render.
                    # Instead, wait until ALL widgets (sync + async) are created, then apply placeholders once.
                    # This is handled by the on_async_complete callback at line 1328.

                def on_async_complete():
                    """Called when all async widgets are created for THIS manager."""
                    logger.info(f"🔍 ASYNC COMPLETE CALLBACK: {self.field_id} - callback triggered")
                    # CRITICAL FIX: Don't trigger styling callbacks yet!
                    # They need to wait until ALL nested managers complete their async widget creation
                    # Otherwise findChildren() will return empty lists for nested forms still being built

                    # CRITICAL FIX: Only root manager refreshes placeholders, and only after ALL nested managers are done
                    is_nested = self._parent_manager is not None
                    logger.info(f"🔍 ASYNC COMPLETE: {self.field_id} - is_nested={is_nested}")
                    if is_nested:
                        # Nested manager - just notify root that we're done
                        # Don't refresh own placeholders - let root do it once at the end
                        logger.info(f"🔍 ASYNC COMPLETE: {self.field_id} - notifying root, NOT applying placeholders")
                        root_manager = self._parent_manager
                        while root_manager._parent_manager is not None:
                            root_manager = root_manager._parent_manager
                        if hasattr(root_manager, '_on_nested_manager_complete'):
                            # CRITICAL FIX: Defer notification to next event loop tick
                            # This ensures Qt has fully processed the layout updates for this manager's widgets
                            # before the root manager tries to apply placeholders
                            QTimer.singleShot(0, lambda: root_manager._on_nested_manager_complete(self))
                    else:
                        # Root manager - mark that root's own widgets are done, but don't apply placeholders yet
                        # Wait for all nested managers to complete first
                        logger.info(f"🔍 ASYNC COMPLETE: {self.field_id} - ROOT manager, pending_nested={len(self._pending_nested_managers)}")
                        self._root_widgets_complete = True
                        if len(self._pending_nested_managers) == 0:
                            logger.info(f"🔍 ASYNC COMPLETE: {self.field_id} - ALL nested managers done, applying placeholders")
                            # CRITICAL FIX: Defer placeholder application to next event loop tick
                            # This gives Qt time to fully process layout updates for async-created widgets
                            # Without this, placeholders are set but not rendered because widgets don't have valid geometry yet
                            def apply_final_styling_and_placeholders():
                                logger.info(f"🔍 ASYNC COMPLETE: {self.field_id} - Applying final styling and placeholders NOW")
                                # STEP 1: Apply all styling callbacks now that ALL widgets exist
                                with timer(f"  Apply styling callbacks", threshold_ms=5.0):
                                    self._apply_all_styling_callbacks()

                                # STEP 2: Refresh placeholders for ALL widgets (including initial sync widgets)
                                # CRITICAL: Use _refresh_with_live_context() to collect live values from other open windows
                                # This ensures new windows immediately show unsaved changes from already-open windows
                                with timer(f"  Complete placeholder refresh with live context (all widgets ready)", threshold_ms=10.0):
                                    self._refresh_with_live_context()
                                logger.info(f"🔍 ASYNC COMPLETE: {self.field_id} - Placeholders applied!")

                            # Schedule on next event loop tick to ensure widgets are fully laid out
                            QTimer.singleShot(0, apply_final_styling_and_placeholders)
                        else:
                            logger.info(f"🔍 ASYNC COMPLETE: {self.field_id} - Still waiting for {len(self._pending_nested_managers)} nested managers")

                # Create remaining widgets asynchronously
                if async_params:
                    logger.info(f"🔍 WIDGET CREATION: {self.field_id} starting async creation of {len(async_params)} widgets")
                    self._create_widgets_async(content_layout, async_params, on_complete=on_async_complete)
                else:
                    # All widgets were created synchronously, call completion immediately
                    logger.info(f"🔍 WIDGET CREATION: {self.field_id} no async widgets, calling completion immediately")
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
            logger.info(f"🔍 BUILD_FORM: {self.field_id} - is_nested={is_nested}, _parent_manager={self._parent_manager}")
            if not is_nested:
                # CRITICAL FIX: Use TWO levels of deferral to match async path behavior
                # First deferral: ensure widgets are added to layout
                # Second deferral: ensure widgets are painted and visible
                def schedule_placeholder_application():
                    logger.info(f"🔍 SYNC DEFER 1: {self.field_id} - First event loop tick, scheduling second deferral")

                    def apply_callbacks_after_layout():
                        logger.info(f"🔍 SYNC DEFER 2: {self.field_id} - Second event loop tick, applying placeholders NOW")
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

                    # Second deferral to next event loop tick
                    QTimer.singleShot(0, apply_callbacks_after_layout)

                # First deferral to next event loop tick
                QTimer.singleShot(0, schedule_placeholder_application)
            else:
                # Nested managers: just apply callbacks
                # Don't refresh placeholders - let parent do it once at the end after all widgets are created
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
        logger.info(f"🔍 ASYNC WIDGET CREATION: {self.field_id} starting async creation of {len(param_infos)} widgets")
        # Create widgets in batches using QTimer to yield to event loop
        batch_size = 3  # Create 3 widgets at a time
        index = 0

        def create_next_batch():
            nonlocal index
            batch_end = min(index + batch_size, len(param_infos))
            logger.info(f"🔍 ASYNC BATCH: {self.field_id} creating widgets {index} to {batch_end-1}")

            for i in range(index, batch_end):
                param_info = param_infos[i]
                widget = self._create_widget_for_param(param_info)
                layout.addWidget(widget)

            index = batch_end

            # Schedule next batch if there are more widgets
            if index < len(param_infos):
                logger.info(f"🔍 ASYNC BATCH: {self.field_id} scheduling next batch, {len(param_infos) - index} widgets remaining")
                QTimer.singleShot(0, create_next_batch)
            elif on_complete:
                # All widgets created - defer completion callback to next event loop tick
                # This ensures Qt has processed all layout updates and widgets are findable
                logger.info(f"🔍 ASYNC BATCH: {self.field_id} all widgets created, scheduling completion callback")
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
        # DEBUG: Log nested form creation for StreamingDefaults
        if 'Streaming' in str(param_type):
            logger.info(f"🔍 NESTED FORM: Creating nested form for {param_name} (type={param_type.__name__})")
            logger.info(f"🔍 NESTED FORM: current_value type = {type(current_value).__name__}")
            if hasattr(current_value, '__dict__'):
                logger.info(f"🔍 NESTED FORM: current_value.__dict__ = {current_value.__dict__}")

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

        # CRITICAL: Pre-register with root manager BEFORE creating nested manager
        # This prevents race condition where nested manager completes before registration
        import dataclasses
        from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
        actual_type = ParameterTypeUtils.get_optional_inner_type(param_type) if ParameterTypeUtils.is_optional(param_type) else param_type

        pre_registered = False
        if dataclasses.is_dataclass(actual_type):
            param_count = len(dataclasses.fields(actual_type))

            # Find root manager
            root_manager = self
            while root_manager._parent_manager is not None:
                root_manager = root_manager._parent_manager

            # Pre-register with root if it's tracking and this will use async
            if self.should_use_async(param_count) and hasattr(root_manager, '_pending_nested_managers'):
                # Use a unique key that includes the full path to avoid duplicates
                unique_key = f"{self.field_id}.{param_name}"
                logger.info(f"🔍 PRE-REGISTER: {unique_key} with root {root_manager.field_id}, pending count before: {len(root_manager._pending_nested_managers)}")
                # Register with a placeholder - we'll replace with actual manager after creation
                root_manager._pending_nested_managers[unique_key] = None
                logger.info(f"🔍 PRE-REGISTER: {unique_key} with root {root_manager.field_id}, pending count after: {len(root_manager._pending_nested_managers)}")
                pre_registered = True

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

        # Update pre-registration with actual manager instance
        if pre_registered:
            unique_key = f"{self.field_id}.{param_name}"
            logger.info(f"🔍 UPDATE REGISTRATION: {unique_key} with actual manager instance")
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
                resolution_type = self._get_resolution_type_for_field(param_name)
                placeholder_text = self.service.get_placeholder_text(param_name, resolution_type)
                if placeholder_text:
                    self._apply_placeholder_text_with_flash_detection(param_name, widget, placeholder_text)
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

        logger.debug(f"🔍 reset_all_parameters CALLED for {self.field_id}, parent={self._parent_manager.field_id if self._parent_manager else 'None'}")
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

            # CRITICAL: Clear unsaved changes cache after reset
            # Reset changes the comparison basis (live values revert to saved)
            type(self)._clear_unsaved_changes_cache("reset_all")

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
                logger.debug(f"🔍 reset_all_parameters: ROOT manager {self.field_id}, refreshing and notifying external listeners")
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
                # CRITICAL: Clear unsaved changes cache after reset
                # When all fields are reset to defaults, there are no unsaved changes
                # This ensures the plate item shows "no unsaved changes" after reset
                type(self)._configs_with_unsaved_changes.clear()
            else:
                # Nested manager: trigger refresh on root manager
                logger.debug(f"🔍 reset_all_parameters: NESTED manager {self.field_id}, finding root and notifying external listeners")
                root = self._parent_manager
                while root._parent_manager is not None:
                    root = root._parent_manager
                logger.debug(f"🔍 reset_all_parameters: Found root manager {root.field_id}")
                root._refresh_with_live_context()
                # CRITICAL: Also refresh enabled styling for root's nested managers
                root._apply_to_nested_managers(lambda name, manager: manager._refresh_enabled_styling())
                # CRITICAL: Emit from root manager to trigger cross-window updates
                root.context_refreshed.emit(root.object_instance, root.context_obj)
                # CRITICAL: Also notify external listeners directly (e.g., PipelineEditor)
                logger.debug(f"🔍 reset_all_parameters: About to call root._notify_external_listeners_refreshed()")
                root._notify_external_listeners_refreshed()
                # CRITICAL: Clear unsaved changes cache after reset (from root manager)
                type(root)._configs_with_unsaved_changes.clear()



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

        # OPTIMIZATION: Block cross-window updates during reset
        # This prevents multiple context_value_changed emissions from _reset_parameter_impl
        # and from nested managers during placeholder refresh
        # We'll emit a single cross-window signal manually after reset completes
        self._block_cross_window_updates = True
        # CRITICAL: Also block on ALL nested managers to prevent cascading emissions
        self._apply_to_nested_managers(lambda name, manager: setattr(manager, '_block_cross_window_updates', True))

        try:
            self._reset_parameter_impl(param_name)

            # CRITICAL: Increment global token after reset to invalidate caches
            # Reset changes values, so other windows need to know their cached context is stale
            type(self)._live_context_token_counter += 1

            # CRITICAL: Clear unsaved changes cache after reset
            # Reset changes the comparison basis (live values revert to saved)
            type(self)._clear_unsaved_changes_cache(f"reset_parameter: {param_name}")

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
                # NOTE: No need to call _notify_external_listeners_refreshed() here
                # We already emitted context_value_changed signal above, which triggers
                # PlateManager/PipelineEditor updates via handle_cross_window_preview_change
            else:
                # Nested manager: trigger refresh on root manager
                root = self._parent_manager
                while root._parent_manager is not None:
                    root = root._parent_manager
                root._refresh_with_live_context()
                # NOTE: No need to call _notify_external_listeners_refreshed() here
                # We already emitted context_value_changed signal above
        finally:
            self._in_reset = False
            self._block_cross_window_updates = False
            # CRITICAL: Also unblock on ALL nested managers
            self._apply_to_nested_managers(lambda name, manager: setattr(manager, '_block_cross_window_updates', False))

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

        # CRITICAL: Clear unsaved changes cache after individual field reset
        # This ensures the plate item updates immediately when fields are reset
        # The cache will rebuild on next check if there are still unsaved changes
        type(self)._configs_with_unsaved_changes.clear()

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
                with self._build_context_stack(overlay, live_context=live_context, live_context_scopes=live_context.scopes if live_context else None):
                    resolution_type = self._get_resolution_type_for_field(param_name)
                    placeholder_text = self.service.get_placeholder_text(param_name, resolution_type)
                    if placeholder_text:
                        self._apply_placeholder_text_with_flash_detection(param_name, widget, placeholder_text)

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

        Uses the cached parameter values updated on every edit. This avoids losing
        concrete values when widgets are in placeholder state.
        """
        with timer(f"get_current_values ({self.field_id})", threshold_ms=2.0):
            # Start from cached parameter values instead of re-reading widgets
            current_values = dict(self._current_value_cache)

            if self.field_id == 'step':
                logger.info(f"🔍 get_current_values (step): _current_value_cache keys = {list(self._current_value_cache.keys())}")
                for key in ['step_well_filter_config', 'step_materialization_config', 'streaming_defaults']:
                    if key in self._current_value_cache:
                        val = self._current_value_cache[key]
                        logger.info(f"🔍 get_current_values (step): _current_value_cache[{key}] = {type(val).__name__}")

            # Collect values from nested managers, respecting optional dataclass checkbox states
            self._apply_to_nested_managers(
                lambda name, manager: self._process_nested_values_if_checkbox_enabled(
                    name, manager, current_values
                )
            )

            if self.field_id == 'step':
                logger.info(f"🔍 get_current_values (step): AFTER _apply_to_nested_managers")
                for key in ['step_well_filter_config', 'step_materialization_config', 'streaming_defaults']:
                    if key in current_values:
                        val = current_values[key]
                        logger.info(f"🔍 get_current_values (step): current_values[{key}] = {type(val).__name__}")

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

        CRITICAL: Works for ALL objects (lazy dataclasses, scoped objects like FunctionStep, etc.)
        by extracting raw values from nested dataclasses regardless of parent type.
        """
        user_modified = {}
        current_values = self.get_current_values()

        if self.field_id == 'step':
            logger.info(f"🔍 get_user_modified_values (step): current_values keys = {list(current_values.keys())}")
            for key in ['step_well_filter_config', 'step_materialization_config', 'streaming_defaults']:
                if key in current_values:
                    val = current_values[key]
                    logger.info(f"🔍 get_user_modified_values (step): {key} = {type(val).__name__}, value={val}")

        # For non-lazy-dataclass objects (like FunctionStep), we still need to extract raw values
        # from nested dataclasses for sibling inheritance to work
        is_lazy_dataclass = hasattr(self.config, '_resolve_field_value')

        # Include fields where the raw value is not None OR the field was explicitly reset
        for field_name, value in current_values.items():
            # CRITICAL: Include None values if they were explicitly reset
            # This allows other windows to see that the field was reset and should override saved values
            is_explicitly_reset = field_name in self.reset_fields

            if value is not None or is_explicitly_reset:
                # CRITICAL: For nested dataclasses, we need to extract only user-modified fields
                # by checking the raw values (using object.__getattribute__ to avoid resolution)
                from dataclasses import is_dataclass, fields as dataclass_fields
                if field_name in ['step_well_filter_config', 'step_materialization_config', 'streaming_defaults', 'well_filter_config']:
                    logger.info(f"🔍 get_user_modified_values CHECK: {field_name} - value type={type(value).__name__}, is_dataclass={is_dataclass(value)}, isinstance(value, type)={isinstance(value, type)}")
                if is_dataclass(value) and not isinstance(value, type):
                    if field_name in ['step_well_filter_config', 'step_materialization_config', 'streaming_defaults', 'well_filter_config']:
                        logger.info(f"🔍 get_user_modified_values: {field_name} IS A DATACLASS, extracting raw values")
                    # Extract raw field values from nested dataclass
                    nested_user_modified = {}
                    for field in dataclass_fields(value):
                        raw_value = object.__getattribute__(value, field.name)
                        if field_name in ['step_well_filter_config', 'step_materialization_config', 'streaming_defaults', 'well_filter_config']:
                            logger.info(f"🔍 get_user_modified_values:   {field_name}.{field.name} = {raw_value}")
                        if raw_value is not None:
                            nested_user_modified[field.name] = raw_value

                    # Only include if nested dataclass has user-modified fields
                    if nested_user_modified:
                        # CRITICAL: Pass as dict, not as reconstructed instance
                        # This allows the context merging to handle it properly
                        # We'll need to reconstruct it when applying to context
                        if field_name in ['step_well_filter_config', 'step_materialization_config', 'streaming_defaults', 'well_filter_config']:
                            logger.info(f"🔍 get_user_modified_values: {field_name} → tuple({type(value).__name__}, {nested_user_modified})")
                        user_modified[field_name] = (type(value), nested_user_modified)
                    else:
                        # No user-modified fields in nested dataclass - skip it
                        if field_name in ['step_well_filter_config', 'step_materialization_config', 'streaming_defaults', 'well_filter_config']:
                            logger.info(f"🔍 get_user_modified_values: {field_name} → SKIPPED (no user-modified fields)")
                else:
                    # Non-dataclass field, include if not None OR explicitly reset
                    if field_name in ['step_well_filter_config', 'step_materialization_config', 'streaming_defaults', 'well_filter_config']:
                        logger.info(f"🔍 get_user_modified_values: {field_name} → NOT A DATACLASS (is_dataclass={is_dataclass(value)}, isinstance(value, type)={isinstance(value, type)}), returning instance {type(value).__name__}")
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

        For GlobalPipelineConfig, merges values_dict into thread-local global config
        to preserve ui_hidden fields. For other types, creates fresh instance.

        CRITICAL: Handles tuple format (type, dict) from get_user_modified_values()
        by reconstructing nested dataclasses before passing to constructor.

        Args:
            overlay_type: Type to instantiate (dataclass, function, etc.)
            values_dict: Dict of parameter values to pass to constructor.
                        Values can be scalars, dataclass instances, or tuples (type, dict)
                        for nested dataclasses with user-modified fields.

        Returns:
            Instance of overlay_type or SimpleNamespace if type is not instantiable
        """
        try:
            # CRITICAL: Reconstruct nested dataclasses from tuple format (type, dict)
            # get_user_modified_values() returns nested dataclasses as tuples to preserve only user-modified fields
            # We need to instantiate them before passing to the constructor
            import dataclasses
            reconstructed_values = {}
            for key, value in values_dict.items():
                if isinstance(value, tuple) and len(value) == 2:
                    # Nested dataclass in tuple format: (type, dict)
                    dataclass_type, field_dict = value
                    # Only reconstruct if it's actually a dataclass (not a function)
                    if dataclasses.is_dataclass(dataclass_type):
                        logger.info(f"🔍 OVERLAY INSTANCE: Reconstructing {key} from tuple: {dataclass_type.__name__}({field_dict})")
                        reconstructed_values[key] = dataclass_type(**field_dict)
                    else:
                        # Not a dataclass (e.g., function), skip it
                        logger.warning(f"⚠️ OVERLAY INSTANCE: Skipping non-dataclass tuple for {key}: {dataclass_type}")
                        # Don't include it in reconstructed_values
                else:
                    reconstructed_values[key] = value

            # CRITICAL: For GlobalPipelineConfig, merge form values into thread-local global config
            # This preserves ui_hidden fields (napari_display_config, fiji_display_config)
            # that don't have widgets but are needed for sibling inheritance
            from openhcs.config_framework.lazy_factory import is_global_config_type
            if is_global_config_type(overlay_type):
                from openhcs.config_framework.context_manager import get_base_global_config
                thread_local_global = get_base_global_config()
                if thread_local_global is not None and type(thread_local_global) == overlay_type:
                    # CRITICAL: Only pass scalar values (not nested dataclass instances) to dataclasses.replace()
                    # Nested config instances from the form have None fields that would mask thread-local values
                    # So we skip them and let them come from thread-local instead
                    scalar_values = {
                        k: v for k, v in reconstructed_values.items()
                        if v is not None and not dataclasses.is_dataclass(v)
                    }
                    return dataclasses.replace(thread_local_global, **scalar_values)

            # For non-global configs, create fresh instance
            return overlay_type(**reconstructed_values)
        except TypeError:
            # Function or other non-instantiable type: use SimpleNamespace
            from types import SimpleNamespace
            return SimpleNamespace(**reconstructed_values)

    def _build_context_stack(self, overlay, skip_parent_overlay: bool = False, live_context = None, live_context_token: Optional[int] = None, live_context_scopes: Optional[Dict[str, Optional[str]]] = None):
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
            live_context: Either a LiveContextSnapshot or a dict mapping object instances to their live values from other open windows
            live_context_token: Optional cache invalidation token (extracted from LiveContextSnapshot if not provided)
            live_context_scopes: Optional dict mapping config type names to their scope IDs (extracted from LiveContextSnapshot if not provided)

        Returns:
            ExitStack with nested contexts
        """
        from contextlib import ExitStack
        from openhcs.config_framework.context_manager import config_context

        stack = ExitStack()

        # Extract token and scopes from LiveContextSnapshot if not provided
        if isinstance(live_context, LiveContextSnapshot):
            if live_context_token is None:
                live_context_token = live_context.token
            if live_context_scopes is None:
                live_context_scopes = live_context.scopes

        # CRITICAL: For GlobalPipelineConfig editing (root form only), apply static defaults as base context
        # This masks the thread-local loaded instance with class defaults
        # Only do this for the ROOT GlobalPipelineConfig form, not nested configs or step editor
        is_root_global_config = (self.config.is_global_config_editing and
                                 self.global_config_type is not None and
                                 self.context_obj is None)  # No parent context = root form
        logger.info(f"🔍 ROOT CHECK: {self.field_id} - is_global_config_editing={self.config.is_global_config_editing}, global_config_type={self.global_config_type}, context_obj={self.context_obj}, is_root_global_config={is_root_global_config}")

        # CRITICAL: Initialize current_config_scopes with live_context_scopes BEFORE entering any contexts
        # BUT: Do NOT do this for GlobalPipelineConfig OR nested forms inside GlobalPipelineConfig
        # GlobalPipelineConfig is global scope and should not inherit plate-scoped values
        from openhcs.config_framework.context_manager import current_config_scopes

        # Check if this is a nested form inside GlobalPipelineConfig
        is_nested_in_global_config = False
        if self._parent_manager is not None:
            logger.info(f"🔍 NESTED CHECK: {self.field_id} has parent manager")
            # Walk up the parent chain to see if any parent is editing GlobalPipelineConfig
            # CRITICAL: Check global_config_type, not is_global_config_editing
            # is_global_config_editing can be False when PipelineConfig window triggers a refresh
            # but global_config_type will still be a global config type
            from openhcs.config_framework.lazy_factory import is_global_config_type
            current_parent = self._parent_manager
            while current_parent is not None:
                logger.info(f"🔍 NESTED CHECK: Checking parent - is_global_config_editing={current_parent.config.is_global_config_editing}, global_config_type={current_parent.global_config_type}, context_obj={current_parent.context_obj}")
                # GENERIC SCOPE RULE: Check if parent is editing a global config
                if (is_global_config_type(current_parent.global_config_type) and
                    current_parent.context_obj is None):
                    is_nested_in_global_config = True
                    logger.info(f"🔍 NESTED CHECK: {self.field_id} is nested in global config!")
                    break
                current_parent = getattr(current_parent, '_parent_manager', None)
        else:
            logger.info(f"🔍 NESTED CHECK: {self.field_id} has NO parent manager")

        if is_root_global_config or is_nested_in_global_config:
            # CRITICAL: Reset the ContextVar to empty dict for GlobalPipelineConfig and its nested forms
            # This ensures that GlobalPipelineConfig doesn't inherit plate-scoped values
            # from previous PipelineConfig refreshes that may have set the ContextVar
            if is_root_global_config:
                logger.info(f"🔍 INIT SCOPES: Resetting ContextVar to empty for GlobalPipelineConfig (must be global scope)")
            else:
                logger.info(f"🔍 INIT SCOPES: Resetting ContextVar to empty for nested form in GlobalPipelineConfig (must be global scope)")
            token = current_config_scopes.set({})
            stack.callback(current_config_scopes.reset, token)
        elif live_context_scopes:
            logger.info(f"🔍 INIT SCOPES: Setting initial scopes with {len(live_context_scopes)} entries")
            if 'StreamingDefaults' in live_context_scopes:
                logger.info(f"🔍 INIT SCOPES: live_context_scopes['StreamingDefaults'] = {live_context_scopes.get('StreamingDefaults')}")
            # Set the initial scopes - this will be the parent scope for the first context entry
            token = current_config_scopes.set(dict(live_context_scopes))
            # Reset on exit
            stack.callback(current_config_scopes.reset, token)
        else:
            logger.info(f"🔍 INIT SCOPES: live_context_scopes is empty or None")

        if is_root_global_config:
            static_defaults = self.global_config_type()

            # CRITICAL: Merge ui_hidden fields from thread-local global config into static defaults
            # This ensures nested forms can inherit from ui_hidden fields (like napari_display_config)
            # while still showing class defaults for visible fields
            from openhcs.config_framework.context_manager import get_base_global_config
            import dataclasses
            thread_local_global = get_base_global_config()
            if thread_local_global is not None and type(thread_local_global) == type(static_defaults):
                # Get all ui_hidden fields from the dataclass by checking field metadata
                ui_hidden_fields = [
                    f.name for f in dataclasses.fields(type(static_defaults))
                    if f.metadata.get('ui_hidden', False)
                ]

                # Extract ui_hidden field values from thread-local
                ui_hidden_values = {
                    field_name: getattr(thread_local_global, field_name)
                    for field_name in ui_hidden_fields
                    if hasattr(thread_local_global, field_name)
                }

                # Merge into static defaults
                if ui_hidden_values:
                    logger.info(f"🔍 GLOBAL DEFAULTS: Merging {len(ui_hidden_values)} ui_hidden fields from thread-local: {list(ui_hidden_values.keys())}")
                    static_defaults = dataclasses.replace(static_defaults, **ui_hidden_values)

            # CRITICAL: DON'T pass config_scopes to config_context() for GlobalPipelineConfig
            # The scopes were already set in the ContextVar at lines 2712-2720
            # If we pass config_scopes here, it will REPLACE the ContextVar instead of merging
            # This causes plate-scoped configs to be overwritten with None
            logger.info(f"🔍 GLOBAL SCOPES: Entering GlobalPipelineConfig context WITHOUT config_scopes parameter")
            logger.info(f"🔍 GLOBAL SCOPES: ContextVar was already set with live_context_scopes at lines 2712-2720")
            # Global config - no context_provider needed (scope_id will be None)
            stack.enter_context(config_context(static_defaults, mask_with_none=True))
        else:
            # CRITICAL: Always add global context layer, either from live editor or thread-local
            # This ensures placeholders show correct values even when global config editor is closed
            global_layer = self._get_cached_global_context(live_context_token, live_context)
            if global_layer is not None:
                # Use live values from open global config editor
                # Add global config scope (None) to the scopes dict
                global_scopes = dict(live_context_scopes) if live_context_scopes else {}
                # GENERIC: Use type name instead of hardcoded string
                global_scopes[type(global_layer).__name__] = None
                stack.enter_context(config_context(global_layer, config_scopes=global_scopes))
            else:
                # No live editor - use thread-local global config (saved values)
                from openhcs.config_framework.context_manager import get_base_global_config
                thread_local_global = get_base_global_config()
                if thread_local_global is not None:
                    # DEBUG: Check what num_workers value is in thread-local global
                    logger.info(f"🔍 _build_context_stack: thread_local_global.num_workers = {getattr(thread_local_global, 'num_workers', 'NOT FOUND')}")
                    # Add global config scope (None) to the scopes dict
                    global_scopes = dict(live_context_scopes) if live_context_scopes else {}
                    # GENERIC: Use type name instead of hardcoded string
                    global_scopes[type(thread_local_global).__name__] = None
                    stack.enter_context(config_context(thread_local_global, config_scopes=global_scopes))
                else:
                    logger.warning(f"🔍 No global context available (neither live nor thread-local)")

        # CRITICAL FIX: For function panes with step_instance as context_obj, we need to add intermediate configs
        # from live_context as separate layers BEFORE the step_instance layer.
        # This ensures the hierarchy: Global -> Pipeline -> Step -> Function
        # Without this, function panes skip intermediate configs and go straight from Global to Step.
        #
        # GENERIC SCOPE RULE: Only add live context configs if they have LESS specific scopes than current scope.
        # This prevents parent scopes from seeing child scope values.
        # Example: GlobalPipelineConfig (scope=None) should NOT see PipelineConfig (scope=plate_path) values
        from openhcs.core.config import PipelineConfig
        from openhcs.config_framework.dual_axis_resolver import get_scope_specificity

        # Determine if we should add intermediate config layers from live_context
        should_add_intermediate_configs = (
            live_context and
            not is_root_global_config and
            not is_nested_in_global_config
        )

        # GENERIC SCOPE CHECK: Only add configs with less specific scopes than current scope
        if should_add_intermediate_configs:
            current_specificity = get_scope_specificity(self.scope_id)

            # Check if we have PipelineConfig in live_context
            pipeline_config_live = self._find_live_values_for_type(PipelineConfig, live_context)
            if pipeline_config_live is not None:
                # Get PipelineConfig scope from live_context_scopes
                pipeline_scopes = dict(live_context_scopes) if live_context_scopes else {}
                pipeline_scope_id = pipeline_scopes.get('PipelineConfig')
                pipeline_specificity = get_scope_specificity(pipeline_scope_id)

                # GENERIC SCOPE RULE: Only add if pipeline scope is less specific than current scope
                # This prevents GlobalPipelineConfig (specificity=0) from seeing PipelineConfig (specificity=1)
                if pipeline_specificity < current_specificity:
                    try:
                        # Create PipelineConfig instance from live values
                        import dataclasses
                        pipeline_config_instance = PipelineConfig(**pipeline_config_live)
                        # Create context_provider from scope_id if needed
                        from openhcs.config_framework.context_manager import ScopeProvider
                        context_provider = ScopeProvider(pipeline_scope_id) if pipeline_scope_id else None
                        stack.enter_context(config_context(pipeline_config_instance, context_provider=context_provider, config_scopes=pipeline_scopes))
                        logger.debug(f"Added PipelineConfig layer (scope={pipeline_scope_id}, specificity={pipeline_specificity}) from live context for {self.field_id} (current_specificity={current_specificity})")
                    except Exception as e:
                        logger.warning(f"Failed to add PipelineConfig layer from live context: {e}")
                else:
                    logger.debug(f"Skipped PipelineConfig layer (specificity={pipeline_specificity} >= current_specificity={current_specificity}) for {self.field_id}")

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

                # CRITICAL: For nested managers, also add the parent's nested config value to context
                # This allows nested fields to inherit from the parent's nested config
                # Example: step_materialization_config.sub_dir inherits from pipeline_config.step_materialization_config.sub_dir
                if self._parent_manager is not None and hasattr(self.context_obj, self.field_id):
                    parent_nested_value = getattr(self.context_obj, self.field_id)
                    if parent_nested_value is not None:
                        logger.debug(f"🔍 Adding parent's nested config to context: {type(parent_nested_value).__name__}")
                        stack.enter_context(config_context(parent_nested_value))

        # CRITICAL: For nested forms, include parent's USER-MODIFIED values for sibling inheritance
        # This allows live placeholder updates when sibling fields change
        # ONLY enable this AFTER initial form load to avoid polluting placeholders with initial widget values
        # SKIP if skip_parent_overlay=True (used during reset to prevent re-introducing old values)
        # CRITICAL SCOPE RULE: Only add parent overlay if parent scope is compatible with current scope
        # A form can only inherit from parents with EQUAL OR LESS specific scopes
        # Example: GlobalPipelineConfig (scope=None, specificity=0) should NOT inherit from PipelineConfig (scope=plate_path, specificity=1)
        parent_manager = getattr(self, '_parent_manager', None)
        parent_scope_compatible = True
        if parent_manager and hasattr(parent_manager, 'scope_id'):
            from openhcs.config_framework.dual_axis_resolver import get_scope_specificity
            parent_specificity = get_scope_specificity(parent_manager.scope_id)
            current_specificity = get_scope_specificity(self.scope_id)
            parent_scope_compatible = parent_specificity <= current_specificity
            logger.info(f"🔍 PARENT OVERLAY SCOPE CHECK: {self.field_id} - parent_scope={parent_manager.scope_id}, parent_specificity={parent_specificity}, current_scope={self.scope_id}, current_specificity={current_specificity}, compatible={parent_scope_compatible}")

        # DEBUG: Log why parent overlay might not be added
        if parent_manager:
            logger.info(f"🔍 PARENT OVERLAY CHECK: {self.field_id} - skip_parent_overlay={skip_parent_overlay}, parent_scope_compatible={parent_scope_compatible}, has_get_user_modified_values={hasattr(parent_manager, 'get_user_modified_values')}, has_dataclass_type={hasattr(parent_manager, 'dataclass_type')}, _initial_load_complete={parent_manager._initial_load_complete}")

        if (not skip_parent_overlay and
            parent_scope_compatible and
            parent_manager and
            hasattr(parent_manager, 'get_user_modified_values') and
            hasattr(parent_manager, 'dataclass_type') and
            parent_manager._initial_load_complete):  # Check PARENT's initial load flag

            # Get only user-modified values from parent (not all values)
            # This prevents polluting context with stale/default values
            parent_user_values = parent_manager.get_user_modified_values()
            logger.info(f"🔍 SIBLING INHERITANCE: {self.field_id} getting parent values: {list(parent_user_values.keys())}")
            # Log nested dataclass values for debugging
            for key, val in parent_user_values.items():
                if isinstance(val, tuple) and len(val) == 2:
                    dataclass_type, field_dict = val
                    logger.info(f"🔍 SIBLING INHERITANCE:   {key} = {dataclass_type.__name__}({field_dict})")
                elif key in ['step_well_filter_config', 'step_materialization_config', 'streaming_defaults', 'well_filter_config']:
                    logger.info(f"🔍 SIBLING INHERITANCE:   {key} = {type(val).__name__} (NOT A TUPLE!)")

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
                    # _create_overlay_instance() will handle reconstructing nested dataclasses from tuple format
                    parent_overlay_instance = self._create_overlay_instance(parent_type, parent_values_with_excluded)

                    # CRITICAL FIX: Pass parent's scope when adding parent overlay for sibling inheritance
                    # Without this, the parent overlay defaults to PipelineConfig scope (specificity=1)
                    # instead of FunctionStep scope (specificity=2), causing the resolver to skip siblings
                    parent_scopes = dict(live_context_scopes) if live_context_scopes else {}
                    if parent_manager.scope_id is not None:
                        # Add parent's scope to the scopes dict
                        parent_scopes[type(parent_overlay_instance).__name__] = parent_manager.scope_id
                        # Create context_provider from parent's scope_id
                        from openhcs.config_framework.context_manager import ScopeProvider
                        context_provider = ScopeProvider(parent_manager.scope_id)
                        logger.info(f"🔍 PARENT OVERLAY: Adding parent overlay with scope={parent_manager.scope_id} for {self.field_id}")
                    else:
                        context_provider = None
                        logger.info(f"🔍 PARENT OVERLAY: Adding parent overlay with NO scope for {self.field_id}")

                    if is_root_global_config:
                        stack.enter_context(config_context(parent_overlay_instance, context_provider=context_provider, config_scopes=parent_scopes, mask_with_none=True))
                    else:
                        stack.enter_context(config_context(parent_overlay_instance, context_provider=context_provider, config_scopes=parent_scopes))

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
        # CRITICAL: Pass scope_id for the current form to enable scope-aware priority
        current_scope_id = getattr(self, 'scope_id', None)
        logger.info(f"🔍 FINAL OVERLAY: current_scope_id={current_scope_id}, dataclass_type={self.dataclass_type.__name__ if self.dataclass_type else None}, live_context_scopes={live_context_scopes}")
        logger.info(f"🔍 FINAL OVERLAY: overlay_instance type = {type(overlay_instance).__name__}")
        logger.info(f"🔍 FINAL OVERLAY: self.scope_id = {self.scope_id}, hasattr(self, 'scope_id') = {hasattr(self, 'scope_id')}")

        # Log nested configs in overlay
        import dataclasses
        if dataclasses.is_dataclass(overlay_instance):
            for field in dataclasses.fields(overlay_instance):
                if field.name.endswith('_config'):
                    field_value = getattr(overlay_instance, field.name, None)
                    logger.info(f"🔍 FINAL OVERLAY: {field.name} = {field_value} (type={type(field_value).__name__ if field_value else 'None'})")
        if current_scope_id is not None or live_context_scopes:
            # Build scopes dict for current overlay
            overlay_scopes = dict(live_context_scopes) if live_context_scopes else {}
            if current_scope_id is not None and self.dataclass_type:
                overlay_scopes[self.dataclass_type.__name__] = current_scope_id
            logger.debug(f"🔍 FINAL OVERLAY: overlay_scopes={overlay_scopes}")
            # Create context_provider from scope_id if needed
            from openhcs.config_framework.context_manager import ScopeProvider
            context_provider = ScopeProvider(current_scope_id) if current_scope_id else None
            stack.enter_context(config_context(overlay_instance, context_provider=context_provider, config_scopes=overlay_scopes))
        else:
            stack.enter_context(config_context(overlay_instance))

        return stack

    def _get_cached_global_context(self, token: Optional[int], live_context):
        """Get cached GlobalPipelineConfig instance with live values merged.

        PERFORMANCE: Uses class-level cache shared across all instances to avoid
        rebuilding the global context for every nested form.

        Args:
            token: Cache invalidation token
            live_context: Either a LiveContextSnapshot or a dict mapping types to their live values
        """
        if not self.global_config_type or not live_context:
            type(self)._cached_global_context_token = None
            type(self)._cached_global_context_instance = None
            return None

        if token is None or type(self)._cached_global_context_token != token:
            type(self)._cached_global_context_instance = self._build_global_context_instance(live_context)
            type(self)._cached_global_context_token = token
            logger.debug(f"🔍 GLOBAL CONTEXT CACHE MISS: Rebuilt at token={token}")
        else:
            logger.debug(f"🔍 GLOBAL CONTEXT CACHE HIT: Reusing cached instance at token={token}")
        return type(self)._cached_global_context_instance

    def _build_global_context_instance(self, live_context):
        """Build GlobalPipelineConfig instance with live values merged.

        Args:
            live_context: Either a LiveContextSnapshot or a dict mapping types to their live values
        """
        from openhcs.config_framework.context_manager import get_base_global_config
        import dataclasses

        try:
            thread_local_global = get_base_global_config()
            if thread_local_global is None:
                return None

            global_live_values = self._find_live_values_for_type(self.global_config_type, live_context)
            if global_live_values is None:
                logger.info(f"🔍 _build_global_context_instance: No live values found for {self.global_config_type.__name__}")
                return None

            # DEBUG: Log what live values we found
            if 'num_workers' in global_live_values:
                logger.info(f"🔍 _build_global_context_instance: Found live num_workers={global_live_values['num_workers']}")

            global_live_values = self._reconstruct_nested_dataclasses(global_live_values, thread_local_global)
            merged = dataclasses.replace(thread_local_global, **global_live_values)

            # DEBUG: Log the merged result
            if hasattr(merged, 'num_workers'):
                logger.info(f"🔍 _build_global_context_instance: Merged instance has num_workers={merged.num_workers}")

            return merged
        except Exception as e:
            logger.warning(f"Failed to cache global context: {e}")
            return None

    def _get_cached_parent_context(self, ctx_obj, token: Optional[int], live_context):
        """Get cached parent context instance with live values merged.

        Args:
            ctx_obj: The parent context object
            token: Cache invalidation token
            live_context: Either a LiveContextSnapshot or a dict mapping types to their live values
        """
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

    def _build_parent_context_instance(self, ctx_obj, live_context):
        """Build parent context instance with live values merged.

        Args:
            ctx_obj: The parent context object
            live_context: Either a LiveContextSnapshot or a dict mapping types to their live values
        """
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
        logger.info(f"🔔 _on_nested_parameter_changed CALLED: param_name={param_name}, value={value}, field_id={self.field_id}")
        # OPTIMIZATION: Skip expensive placeholder refreshes during batch reset
        # The reset operation will do a single refresh at the end
        # BUT: Still propagate the signal so dual editor window can sync function editor
        in_reset = getattr(self, '_in_reset', False)
        block_cross_window = getattr(self, '_block_cross_window_updates', False)

        # Find which nested manager emitted this change (needed for both refresh and signal propagation)
        # CRITICAL: Use sender() to identify the actual emitting manager, not just param_name lookup
        # Multiple nested managers can have the same parameter name (e.g., well_filter in both
        # well_filter_config and step_well_filter_config), so we need to check which one sent the signal
        emitting_manager_name = None
        sender_obj = self.sender()
        logger.info(f"🔍 _on_nested_parameter_changed: param_name={param_name}, sender={sender_obj}, searching in {len(self.nested_managers)} nested managers")
        for nested_name, nested_manager in self.nested_managers.items():
            if nested_manager is sender_obj:
                logger.info(f"🔍 _on_nested_parameter_changed: FOUND sender in {nested_name}")
                emitting_manager_name = nested_name
                break
        if not emitting_manager_name:
            logger.warning(f"⚠️ _on_nested_parameter_changed: Could not find nested manager for sender={sender_obj}, param_name={param_name}")

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
            # CRITICAL: Increment token BEFORE refreshing placeholders
            # This ensures siblings resolve with the new token and don't cache stale values
            type(self)._live_context_token_counter += 1
            logger.info(f"🔍 NESTED CHANGE TOKEN INCREMENT: {emitting_manager_name}.{param_name} → token={type(self)._live_context_token_counter}")

            # Collect live context from other windows (only for root managers)
            if self._parent_manager is None:
                live_context = self._collect_live_context_from_other_windows()
            else:
                live_context = None

            # PERFORMANCE: Only refresh placeholders for fields with the same name
            # A field can ONLY inherit from another field with the same name
            # So when 'well_filter' changes, only refresh 'well_filter' placeholders, not ALL placeholders
            changed_fields = {param_name} if param_name else None

            # Refresh parent form's placeholders with live context
            self._refresh_all_placeholders(live_context=live_context, changed_fields=changed_fields)

            # Refresh only sibling nested managers that could be affected by this change
            # A sibling is affected if its object instance inherits from the emitting manager's type
            # Example: NapariStreamingConfig inherits from WellFilterConfig, so it's affected
            #          VFSConfig doesn't inherit from WellFilterConfig, so it's not affected
            emitting_manager = self.nested_managers.get(emitting_manager_name) if emitting_manager_name else None
            emitting_type = emitting_manager.dataclass_type if emitting_manager else None

            def should_refresh_sibling(name: str, manager) -> bool:
                """Check if sibling manager should be refreshed based on inheritance."""
                if name == emitting_manager_name:
                    return False  # Don't refresh the emitting manager itself
                if not emitting_type:
                    return True  # Conservative: refresh if we can't determine
                # Check if the sibling's object instance inherits from the emitting type
                return isinstance(manager.object_instance, emitting_type)

            logger.info(f"🔍 NESTED CHANGE: {emitting_manager_name}.{param_name} = {value}, refreshing siblings (only field '{param_name}')")

            # PERFORMANCE: Only refresh the SPECIFIC field in siblings that have it
            # Use changed_fields to filter inside _refresh_all_placeholders
            # This preserves flash animation and other placeholder update logic
            refreshed_count = 0
            skipped_count = 0
            for name, manager in self.nested_managers.items():
                if not should_refresh_sibling(name, manager):
                    continue
                # Check if this sibling has the changed field
                if param_name not in manager.parameters:
                    skipped_count += 1
                    continue
                # Call _refresh_all_placeholders with changed_fields to filter to just this field
                # This preserves flash animation and other placeholder update logic
                manager._refresh_all_placeholders(live_context=live_context, changed_fields=changed_fields)
                refreshed_count += 1

            logger.info(f"🔍 NESTED CHANGE: Refreshed {refreshed_count} sibling configs, skipped {skipped_count} (no '{param_name}' field)")

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

            # CRITICAL FIX: Update parent's cache with reconstructed dataclass
            # This ensures get_user_modified_values() returns the latest nested values
            # Without this, the parent's cache has a stale instance from initialization
            self._store_parameter_value(emitting_manager_name, reconstructed_value)

            # DEBUG: Check what's actually stored
            if emitting_manager_name in ['step_well_filter_config', 'step_materialization_config', 'streaming_defaults']:
                logger.info(f"🔍 STORED IN CACHE: {emitting_manager_name} = {reconstructed_value}")
                logger.info(f"🔍 CACHE TYPE: {type(reconstructed_value).__name__}")
                if reconstructed_value:
                    from dataclasses import fields as dataclass_fields
                    for field in dataclass_fields(reconstructed_value):
                        raw_val = object.__getattribute__(reconstructed_value, field.name)
                        logger.info(f"🔍 RAW VALUE: {emitting_manager_name}.{field.name} = {raw_val}")

            # Emit parent parameter name with reconstructed dataclass
            logger.info(f"🔔 EMITTING PARENT CONFIG: {emitting_manager_name} = {reconstructed_value}")
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

        # CRITICAL: Always collect live context if not provided, even for nested forms
        # Nested forms need live context too for correct placeholder resolution
        if live_context is None:
            live_context = self._collect_live_context_from_other_windows()

        if self._should_use_async_placeholder_refresh():
            self._schedule_async_placeholder_refresh(live_context, exclude_param)
        else:
            self._perform_placeholder_refresh_sync(live_context, exclude_param)

    def _refresh_all_placeholders(self, live_context: dict = None, exclude_param: str = None, changed_fields: set = None) -> None:
        """Refresh placeholder text for widgets that could be affected by field changes.

        PERFORMANCE: Only refreshes placeholders that could inherit from changed fields.

        Args:
            live_context: Optional dict mapping object instances to their live values from other open windows
            exclude_param: Optional parameter name to exclude from refresh (e.g., the param that just changed)
            changed_fields: Optional set of field paths that changed (e.g., {'well_filter', 'well_filter_mode'})
        """
        # CRITICAL FIX: If live_context is not a LiveContextSnapshot, collect it now
        # This ensures we ALWAYS have scope information for _build_context_stack()
        # Without scopes, PipelineConfig gets assigned scope=None, breaking placeholder inheritance
        if not isinstance(live_context, LiveContextSnapshot):
            logger.info(f"🔍 _refresh_all_placeholders: live_context is not LiveContextSnapshot, collecting now (type={type(live_context).__name__})")
            live_context = type(self).collect_live_context(scope_filter=self.scope_id)

        # Extract token, live context values, and scopes
        token, live_context_values, live_context_scopes = self._unwrap_live_context(live_context)
        live_context_for_stack = live_context if isinstance(live_context, LiveContextSnapshot) else live_context_values

        # CRITICAL: Use token-based cache key, not value-based
        # The token increments whenever ANY value changes, which is correct behavior
        # The individual placeholder text cache is value-based to prevent redundant resolution
        # But the refresh operation itself should run when the token changes
        from openhcs.config_framework import CacheKey
        cache_key = CacheKey.from_args(exclude_param, token, frozenset(changed_fields) if changed_fields else None)

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

                # PERFORMANCE: Filter to only fields that could be affected by changes
                if changed_fields:
                    # Keep placeholders that match any changed field
                    # Match by field name or by nested path (e.g., 'well_filter' affects 'step_well_filter_config')
                    filtered_candidates = set()
                    for candidate in candidate_names:
                        for changed in changed_fields:
                            # Match if candidate contains the changed field name
                            # E.g., changed='well_filter' matches candidate='well_filter' or 'step_well_filter_config.well_filter'
                            if changed in candidate or candidate in changed:
                                filtered_candidates.add(candidate)
                                break
                    if filtered_candidates:
                        logger.debug(f"🔍 Filtered placeholders: {len(candidate_names)} → {len(filtered_candidates)} (changed_fields={changed_fields})")
                        candidate_names = filtered_candidates
                    else:
                        # No candidates match - skip entire refresh
                        logger.debug(f"🔍 No placeholders affected by changes={changed_fields}, skipping refresh")
                        return

                if not candidate_names:
                    return

                with self._build_context_stack(overlay, live_context=live_context_for_stack, live_context_scopes=live_context_scopes):
                    monitor = get_monitor("Placeholder resolution per field")

                    for param_name in candidate_names:
                        widget = self.widgets.get(param_name)
                        if not widget:
                            # DEBUG: Log missing widgets for StreamingDefaults
                            if 'Streaming' in str(self.dataclass_type):
                                logger.info(f"🔍 MISSING WIDGET: {self.field_id}.{param_name} not in self.widgets")
                            continue

                        widget_in_placeholder_state = widget.property("is_placeholder_state")
                        current_value = self.parameters.get(param_name)
                        if current_value is not None and not widget_in_placeholder_state:
                            continue

                        with monitor.measure():
                            # CRITICAL: Resolve placeholder text and detect changes for flash animation
                            resolution_type = self._get_resolution_type_for_field(param_name)
                            # DEBUG: Log placeholder resolution for StreamingDefaults
                            if 'Streaming' in str(self.dataclass_type):
                                logger.info(f"🔍 APPLYING PLACEHOLDER: {self.field_id}.{param_name} - resolving with type {resolution_type.__name__}")
                            placeholder_text = self.service.get_placeholder_text(param_name, resolution_type)
                            if 'Streaming' in str(self.dataclass_type):
                                logger.info(f"🔍 APPLYING PLACEHOLDER: {self.field_id}.{param_name} - got text: {placeholder_text}, type={type(placeholder_text)}, bool={bool(placeholder_text)}")
                            if placeholder_text:
                                self._apply_placeholder_text_with_flash_detection(param_name, widget, placeholder_text)
                            elif 'Streaming' in str(self.dataclass_type):
                                logger.info(f"🔍 SKIPPING PLACEHOLDER: {self.field_id}.{param_name} - placeholder_text is falsy")

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
        token, live_context_values, live_context_scopes = self._unwrap_live_context(live_context)
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
        overlay = self.parameters
        with self._build_context_stack(overlay, live_context=live_context, live_context_scopes=live_context.scopes if live_context else None):
            resolution_type = self._get_resolution_type_for_field(field_name)
            placeholder_text = self.service.get_placeholder_text(field_name, resolution_type)
            if placeholder_text:
                self._apply_placeholder_text_with_flash_detection(field_name, widget, placeholder_text)

    def _after_placeholder_text_applied(self, live_context: Any) -> None:
        """Apply nested refreshes and styling once placeholders have been updated."""
        # DEBUG: Log nested manager refresh
        if self.nested_managers:
            logger.info(f"🔍 NESTED REFRESH: {self.field_id} refreshing {len(self.nested_managers)} nested managers: {list(self.nested_managers.keys())}")

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
        """Capture UI state needed by the background placeholder resolver.

        PERFORMANCE: Only include fields that are actually in placeholder state.
        Skip fields with user-entered values - they don't need placeholder resolution.
        """
        plan = {}
        for param_name, widget in self.widgets.items():
            if exclude_param and param_name == exclude_param:
                continue
            if not widget:
                continue
            # PERFORMANCE: Only resolve if widget is in placeholder state
            # If user has entered a value, skip placeholder resolution entirely
            if widget.property("is_placeholder_state"):
                plan[param_name] = True
        return plan

    def _unwrap_live_context(self, live_context: Optional[Any]) -> Tuple[Optional[int], Optional[dict], Optional[Dict[str, Optional[str]]]]:
        """Return (token, values, scopes) for a live context snapshot or raw dict."""
        if isinstance(live_context, LiveContextSnapshot):
            return live_context.token, live_context.values, live_context.scopes
        return None, live_context, None

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
        with self._build_context_stack(parameters_snapshot, live_context=live_context_snapshot, live_context_scopes=live_context_snapshot.scopes if live_context_snapshot else None):
            for param_name, was_placeholder in placeholder_plan.items():
                current_value = parameters_snapshot.get(param_name)
                should_apply_placeholder = current_value is None or was_placeholder
                if not should_apply_placeholder:
                    continue
                resolution_type = self._get_resolution_type_for_field(param_name)
                placeholder_text = self.service.get_placeholder_text(param_name, resolution_type)
                if placeholder_text:
                    placeholder_map[param_name] = placeholder_text
        return placeholder_map

    def _apply_placeholder_text_with_flash_detection(self, param_name: str, widget: Any, placeholder_text: str) -> None:
        """Apply placeholder text and detect changes for flash animation.

        This is the SINGLE SOURCE OF TRUTH for applying placeholders with flash detection.
        All code paths that apply placeholders should use this method.

        Args:
            param_name: Name of the parameter
            widget: Widget to apply placeholder to
            placeholder_text: Placeholder text to apply
        """
        from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer

        # Check if placeholder text actually changed (compare with last applied value)
        last_text = self._last_placeholder_text.get(param_name)

        # Apply placeholder text
        logger.info(f"🔍 _apply_placeholder_text_with_flash_detection: {self.field_id}.{param_name} - calling PyQt6WidgetEnhancer.apply_placeholder_text with text='{placeholder_text}'")
        PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
        logger.info(f"🔍 _apply_placeholder_text_with_flash_detection: {self.field_id}.{param_name} - DONE calling PyQt6WidgetEnhancer.apply_placeholder_text")

        # If placeholder changed, trigger flash
        if last_text is not None and last_text != placeholder_text:
            logger.info(f"💥 FLASH TRIGGERED: {self.field_id}.{param_name}: '{last_text}' -> '{placeholder_text}'")
            # If this is a NESTED manager, notify parent to flash the GroupBox
            if self._parent_manager is not None:
                logger.info(f"🔥 Nested manager {self.field_id} had placeholder change, notifying parent")
                self._notify_parent_to_flash_groupbox()
        elif last_text is None:
            logger.debug(f"🔍 NO FLASH (first time): {self.field_id}.{param_name} = '{placeholder_text}'")
        else:
            logger.debug(f"🔍 NO FLASH (same text): {self.field_id}.{param_name} = '{placeholder_text}'")

        # Update last applied text
        self._last_placeholder_text[param_name] = placeholder_text

    def _apply_placeholder_map_results(self, placeholder_map: Dict[str, str]) -> None:
        """Apply resolved placeholder text to widgets on the UI thread.

        Uses _apply_placeholder_text_with_flash_detection for flash detection.
        """
        if not placeholder_map:
            return

        for param_name, placeholder_text in placeholder_map.items():
            widget = self.widgets.get(param_name)
            if not widget or not placeholder_text:
                continue

            self._apply_placeholder_text_with_flash_detection(param_name, widget, placeholder_text)

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

    def _collect_all_field_paths(self) -> Set[str]:
        """Collect all field paths from this manager and all nested managers recursively.

        Returns paths in the format that would be emitted during typing, e.g.:
        - "well_filter_config.well_filter" (not "GlobalPipelineConfig.well_filter_config")
        - "step_materialization_config.enabled" (not "PipelineConfig.step_materialization_config")

        This ensures window close emits the same format as typing for flash detection.
        """
        field_paths = set()

        # Add this manager's own field paths (field_id.param_name)
        for param_name in self.parameters.keys():
            # Skip nested dataclass params - their fields are handled by nested managers
            if param_name in self.nested_managers:
                continue
            field_path = f"{self.field_id}.{param_name}" if self.field_id else param_name
            field_paths.add(field_path)

        # Recursively collect from nested managers
        for param_name, nested_manager in self.nested_managers.items():
            nested_paths = nested_manager._collect_all_field_paths()
            field_paths.update(nested_paths)

        return field_paths

    def _notify_parent_to_flash_groupbox(self) -> None:
        """Notify parent manager to flash this nested config's GroupBox.

        Called by nested managers when their placeholders change.
        The parent manager finds the GroupBox widget and flashes it.
        Also notifies the root manager to flash the tree item if applicable.
        """
        if not self._parent_manager:
            return

        # Find which parameter name in the parent corresponds to this nested manager
        param_name = None
        for name, manager in self._parent_manager.nested_managers.items():
            if manager is self:
                param_name = name
                break

        if not param_name:
            logger.warning(f"Could not find param_name for nested manager {self.field_id}")
            return

        logger.debug(f"🔥 Flashing GroupBox for nested config: {param_name}")

        # Get the GroupBox widget from parent
        group_box = self._parent_manager.widgets.get(param_name)

        if not group_box:
            logger.warning(f"No GroupBox widget found for {param_name}")
            return

        # Flash the GroupBox using scope border color
        from openhcs.pyqt_gui.widgets.shared.widget_flash_animation import flash_widget
        from openhcs.pyqt_gui.widgets.shared.scope_color_utils import get_scope_color_scheme
        from PyQt6.QtGui import QColor

        # Get scope color scheme
        color_scheme = get_scope_color_scheme(self._parent_manager.scope_id)

        # Use orchestrator border color for flash (same as window border)
        border_rgb = color_scheme.orchestrator_item_border_rgb
        flash_color = QColor(*border_rgb, 180)  # Border color with high opacity

        # Use global registry to prevent overlapping flashes
        flash_widget(group_box, flash_color=flash_color)
        logger.debug(f"✅ Flashed GroupBox for {param_name}")

        # Notify root manager to flash tree item (if this is a top-level config in ConfigWindow)
        logger.debug(f"🌲 Checking if should flash tree: parent._parent_manager is None? {self._parent_manager._parent_manager is None}")
        if self._parent_manager._parent_manager is None:
            # Parent is root manager - notify it to flash tree
            logger.debug(f"🌲 Notifying root manager to flash tree for {param_name}")
            self._parent_manager._notify_tree_flash(param_name)
        else:
            logger.debug(f"🌲 NOT notifying tree flash - parent is not root (parent.field_id={self._parent_manager.field_id})")

    def _notify_tree_flash(self, config_name: str) -> None:
        """Notify parent window to flash tree item for a config.

        This is called on the ROOT manager when a nested config's placeholder changes.
        ConfigWindow can override this to implement tree flashing.

        Args:
            config_name: Name of the config that changed (e.g., 'well_filter_config')
        """
        # Default no-op - ConfigWindow will override this
        pass

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

        # PERFORMANCE: Use universal coordinator instead of individual timer
        type(self).schedule_placeholder_refresh(self)
        type(self)._start_coordinated_update_timer()

    def _on_parameter_changed_nested(self, param_name: str, value: Any) -> None:
        """Bubble refresh requests from nested managers up to the root with debounce.

        CRITICAL: ALL changes must emit cross-window signals so other windows can react in real time.
        'enabled' changes skip placeholder refreshes to avoid infinite loops.

        CRITICAL: Also trigger parent's _on_nested_parameter_changed to refresh sibling managers.
        This ensures sibling inheritance works at ALL levels, not just at the root level.
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

        # CRITICAL FIX: Trigger parent's _on_nested_parameter_changed to refresh sibling managers
        # This ensures sibling inheritance works at ALL levels (not just root level)
        # Example: In step editor, when streaming_defaults.host changes, napari_streaming_config.host should update
        # CRITICAL: This must happen BEFORE the enabled early return, otherwise sibling inheritance breaks for enabled fields
        if self._parent_manager is not None:
            # Manually call parent's _on_nested_parameter_changed with this manager as sender
            # This triggers sibling refresh logic in the parent
            self._parent_manager._on_nested_parameter_changed(param_name, value)

        # For 'enabled' changes: skip placeholder refresh to avoid infinite loops
        # CRITICAL: This early return must come AFTER parent notification, otherwise sibling inheritance breaks
        if param_name == 'enabled':
            return

        # For other changes: also trigger placeholder refresh at root level
        root._on_parameter_changed_root(param_name, value)

    def _run_debounced_placeholder_refresh(self) -> None:
        """Execute the pending debounced refresh request."""
        exclude_param = self._pending_debounced_exclude_param
        self._pending_debounced_exclude_param = None
        self._refresh_with_live_context(exclude_param=exclude_param)

    def _on_nested_manager_complete(self, nested_manager) -> None:
        """Called by nested managers when they complete async widget creation."""
        logger.info(f"🔍 _on_nested_manager_complete: {self.field_id} received completion from {nested_manager.field_id}")
        if hasattr(self, '_pending_nested_managers'):
            logger.info(f"🔍 _on_nested_manager_complete: {self.field_id} has {len(self._pending_nested_managers)} pending: {list(self._pending_nested_managers.keys())}")
            # Find and remove this manager from pending dict
            key_to_remove = None
            for key, manager in self._pending_nested_managers.items():
                if manager is nested_manager:
                    key_to_remove = key
                    break

            if key_to_remove:
                logger.info(f"🔍 _on_nested_manager_complete: {self.field_id} removing {key_to_remove}")
                del self._pending_nested_managers[key_to_remove]
            else:
                # Manager already removed or not tracked - this is a duplicate completion call
                # This happens because nested managers fire completion twice (once for themselves, once when their nested managers complete)
                logger.info(f"🔍 _on_nested_manager_complete: {self.field_id} ignoring duplicate completion from {nested_manager.field_id}")
                return

            # If all nested managers are done AND root's own widgets are done, apply styling and refresh placeholders
            logger.info(f"🔍 _on_nested_manager_complete: {self.field_id} now has {len(self._pending_nested_managers)} pending")
            root_widgets_done = getattr(self, '_root_widgets_complete', False)
            logger.info(f"🔍 _on_nested_manager_complete: {self.field_id} root_widgets_complete={root_widgets_done}")
            if len(self._pending_nested_managers) == 0 and root_widgets_done:
                logger.info(f"🔍 _on_nested_manager_complete: {self.field_id} ALL DONE! Applying placeholders")
                # STEP 1: Apply all styling callbacks now that ALL widgets exist
                with timer(f"  Apply styling callbacks", threshold_ms=5.0):
                    self._apply_all_styling_callbacks()

                # STEP 2: Force re-application of placeholders bypassing cache
                # CRITICAL: Placeholders were already set during async widget creation,
                # but Qt doesn't render them because widgets weren't fully laid out yet.
                # Now that ALL widgets are created and laid out, force re-application.
                logger.info(f"🔍 _on_nested_manager_complete: {self.field_id} forcing placeholder re-application")

                # Invalidate the placeholder refresh cache to force re-application
                self._placeholder_refresh_cache.invalidate()

                # Also invalidate cache for all nested managers
                self._apply_to_nested_managers(lambda name, manager: manager._placeholder_refresh_cache.invalidate())

                # Now refresh with live context - this will re-apply all placeholders
                with timer(f"  Complete placeholder refresh with live context (all nested ready)", threshold_ms=10.0):
                    self._refresh_with_live_context()
                logger.info(f"🔍 _on_nested_manager_complete: {self.field_id} placeholder re-application complete")

                # STEP 2.5: Apply post-placeholder callbacks (enabled styling that needs resolved values)
                with timer(f"  Apply post-placeholder callbacks (async)", threshold_ms=5.0):
                    self._apply_all_post_placeholder_callbacks()

                # STEP 3: Refresh enabled styling (after placeholders are resolved)
                # This ensures that nested configs with inherited enabled values get correct styling
                with timer(f"  Enabled styling refresh (all nested ready)", threshold_ms=5.0):
                    self._apply_to_nested_managers(lambda name, manager: manager._refresh_enabled_styling())

    def _process_nested_values_if_checkbox_enabled(self, name: str, manager: Any, current_values: Dict[str, Any]) -> None:
        """
        Process nested values if checkbox is enabled.

        NOTE: The parent's _current_value_cache is now updated in _on_nested_parameter_changed,
        so current_values[name] already has the latest dataclass instance. We just need to
        handle the Optional dataclass checkbox logic here.
        """
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

        # If current_values doesn't have this nested field yet (e.g., during initialization),
        # get it from the nested manager and reconstruct the dataclass
        if name not in current_values:
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

    def _get_original_saved_value(self, param_name: str) -> Any:
        """Get the original saved value for a parameter.

        This retrieves the value from the object_instance WITHOUT any live edits,
        which represents the saved state.

        Args:
            param_name: Parameter name (e.g., 'num_workers')

        Returns:
            The original saved value, or None if not found
        """
        if self.object_instance is None:
            return None

        try:
            # Get the value directly from the object instance
            # This is the saved value because the object_instance is the original config
            # loaded from disk, not a preview instance with live edits merged
            original_value = getattr(self.object_instance, param_name, None)
            logger.debug(f"🔍 _get_original_saved_value: {self.field_id}.{param_name} = {original_value}")

            # CRITICAL: For GlobalPipelineConfig, we need to check if this is a lazy field
            # that might resolve from thread-local storage instead of the instance value
            if original_value is None and hasattr(self.object_instance, '__dataclass_fields__'):
                # Check if this is a lazy dataclass field
                from dataclasses import fields
                field_obj = next((f for f in fields(self.object_instance.__class__) if f.name == param_name), None)
                if field_obj and hasattr(self.object_instance, '_resolve_field_value'):
                    # This is a lazy field - get the raw __dict__ value to avoid resolution
                    raw_value = object.__getattribute__(self.object_instance, param_name)
                    logger.debug(f"🔍 _get_original_saved_value: {self.field_id}.{param_name} raw __dict__ value = {raw_value}")
                    return raw_value

            return original_value
        except Exception as e:
            logger.warning(f"⚠️ _get_original_saved_value failed for {param_name}: {e}")
            return None

    def _emit_cross_window_change(self, param_name: str, value: object):
        """Batch cross-window context change signals for performance.

        This is connected to parameter_changed signal for root managers.

        Args:
            param_name: Name of the parameter that changed
            value: New value
        """
        logger.info(f"🔔 _emit_cross_window_change: {self.field_id}.{param_name} = {value} (scope_id={self.scope_id})")

        # OPTIMIZATION: Skip cross-window updates during batch operations (e.g., reset_all)
        if getattr(self, '_block_cross_window_updates', False):
            logger.info(f"🚫 _emit_cross_window_change BLOCKED for {self.field_id}.{param_name} (in reset/batch operation)")
            return

        # CRITICAL: Use full field path as key, not just param_name!
        # This ensures nested field changes (e.g., step_materialization_config.well_filter)
        # are properly tracked with their full path, not just the leaf field name.
        field_path = f"{self.field_id}.{param_name}"

        if field_path in self._last_emitted_values:
            last_value = self._last_emitted_values[field_path]
            try:
                if last_value == value:
                    return
            except Exception:
                # If equality check fails, fall back to emitting
                pass

        # CRITICAL: Check if the new value equals the ORIGINAL saved value
        # If so, REMOVE the entry from _last_emitted_values instead of adding it
        # This ensures that reverting a field back to its original value clears the unsaved marker
        original_value = self._get_original_saved_value(param_name)
        try:
            if value == original_value:
                # Value reverted to original - remove from _last_emitted_values
                if field_path in self._last_emitted_values:
                    del self._last_emitted_values[field_path]
                    logger.info(f"🔄 Reverted {field_path} to original value ({value}) - removed from _last_emitted_values")
                else:
                    # Value was never emitted, so nothing to do
                    logger.debug(f"🔄 {field_path} equals original value ({value}) and was never emitted - skipping")
                    return
            else:
                # Value is different from original - add/update in _last_emitted_values
                self._last_emitted_values[field_path] = value
                logger.debug(f"📝 {field_path} changed to {value} (original={original_value}) - added to _last_emitted_values")
        except Exception as e:
            # If comparison fails, fall back to adding the value
            logger.warning(f"⚠️ Failed to compare {field_path} with original value: {e} - adding to _last_emitted_values")
            self._last_emitted_values[field_path] = value

        # Invalidate live context cache by incrementing token
        type(self)._live_context_token_counter += 1

        # PERFORMANCE: Phase 3 - Batch changes for performance
        # Store manager reference to avoid fragile string matching later
        logger.debug(f"📦 Batching cross-window change: {field_path} = {value}")
        type(self)._pending_cross_window_changes.append(
            (self, param_name, value, self.object_instance, self.context_obj)
        )

        # Schedule batched emission
        if type(self)._cross_window_batch_timer is None:
            from PyQt6.QtCore import QTimer
            type(self)._cross_window_batch_timer = QTimer()
            type(self)._cross_window_batch_timer.setSingleShot(True)
            type(self)._cross_window_batch_timer.timeout.connect(
                lambda: type(self)._emit_batched_cross_window_changes()
            )

        # Restart timer (trailing debounce)
        type(self)._cross_window_batch_timer.start(self.CROSS_WINDOW_REFRESH_DELAY_MS)

    @classmethod
    def _emit_batched_cross_window_changes(cls):
        """Emit all pending changes and coordinate listener updates synchronously.

        Uses stored manager references instead of fragile string matching.
        Deduplicates rapid changes to same field (keeps only latest value).
        Coordinates all listener updates to happen simultaneously (no per-listener debounce).
        """
        if not cls._pending_cross_window_changes:
            return

        logger.debug(f"📦 Processing {len(cls._pending_cross_window_changes)} batched cross-window changes")

        # Deduplicate: Keep only the latest value for each (manager, param_name) pair
        # This handles rapid typing where same field changes multiple times
        latest_changes = {}  # (manager_id, param_name) → (manager, value, obj_instance, context_obj)
        for manager, param_name, value, obj_instance, context_obj in cls._pending_cross_window_changes:
            key = (id(manager), param_name)
            latest_changes[key] = (manager, param_name, value, obj_instance, context_obj)

        logger.debug(f"📦 After deduplication: {len(latest_changes)} unique changes")

        # PERFORMANCE: O(N) field parsing + O(M) listener updates = O(N+M) instead of O(N×M)
        # Parse field paths ONCE, then copy to all listeners

        # Extract and parse all field identifiers ONCE (O(N))
        all_identifiers = set()
        for manager, param_name, value, obj_instance, context_obj in latest_changes.values():
            field_path = f"{manager.field_id}.{param_name}"
            # Parse field path to extract identifiers (same logic as handle_cross_window_preview_change)
            if '.' in field_path:
                parts = field_path.split('.', 1)
                if len(parts) == 2:
                    root_token, attr_path = parts
                    all_identifiers.add(attr_path)
                    if '.' in attr_path:
                        final_part = attr_path.split('.')[-1]
                        if final_part:
                            all_identifiers.add(final_part)

        logger.debug(f"📦 Parsed {len(latest_changes)} changes into {len(all_identifiers)} identifiers (O(N))")

        # PERFORMANCE: Store changed fields for placeholder refresh filtering
        cls._current_batch_changed_fields = all_identifiers

        # Copy parsed identifiers to each listener (O(M))
        # Also store the changes so listeners can determine which scopes to update
        for listener, value_changed_handler, refresh_handler in cls._external_listeners:
            if hasattr(listener, '_pending_changed_fields'):
                listener._pending_changed_fields.update(all_identifiers)  # O(1) set union

            # CRITICAL: Store the actual changes so listeners can populate _pending_preview_keys
            # based on which objects/scopes were edited
            if hasattr(listener, '_pending_cross_window_changes_for_scope_resolution'):
                for manager, param_name, value, obj_instance, context_obj in latest_changes.values():
                    listener._pending_cross_window_changes_for_scope_resolution.append(
                        (manager, param_name, value, obj_instance, context_obj)
                    )

            cls._pending_listener_updates.add(listener)
            logger.debug(f"📝 Added {listener.__class__.__name__} to coordinator queue")

        # CRITICAL: Emit context_value_changed signal to other form managers
        # This was missing! The batched emission only updated external listeners,
        # but never emitted the signal to other ParameterFormManager instances.
        # This is why nested dataclass changes worked (they emit directly in _on_parameter_changed_nested)
        # but primitive field changes didn't work (they only batch here).
        for manager, param_name, value, obj_instance, context_obj in latest_changes.values():
            field_path = f"{manager.field_id}.{param_name}"
            logger.debug(f"📡 Emitting context_value_changed: {field_path} = {value}")
            manager.context_value_changed.emit(field_path, value, obj_instance, context_obj)

        # PERFORMANCE: Start coordinator - O(1) regardless of change count
        if cls._pending_listener_updates:
            logger.info(f"🚀 Starting coordinated update for {len(cls._pending_listener_updates)} listeners")
            cls._start_coordinated_update_timer()

        # Clear pending changes
        cls._pending_cross_window_changes.clear()

    @classmethod
    def schedule_coordinated_update(cls, listener: Any):
        """Schedule a listener for coordinated update.

        Instead of each listener starting its own debounce timer, they register
        here and get updated all at once by the coordinator.

        Args:
            listener: The listener object that needs updating
        """
        cls._pending_listener_updates.add(listener)
        logger.debug(f"📝 Scheduled coordinated update for {listener.__class__.__name__}")
        # CRITICAL: Start the coordinator timer to actually execute the updates
        cls._start_coordinated_update_timer()

    @classmethod
    def schedule_placeholder_refresh(cls, form_manager: 'ParameterFormManager'):
        """Schedule a form manager for placeholder refresh.

        Replaces individual per-manager timers with batched execution.

        Args:
            form_manager: The form manager that needs placeholder refresh
        """
        cls._pending_placeholder_refreshes.add(form_manager)
        logger.debug(f"📝 Scheduled placeholder refresh for {form_manager.field_id}")

    @classmethod
    def schedule_flash_animation(cls, target: Any, color: Any):
        """Schedule a flash animation.

        Replaces individual per-widget/item timers with batched execution.

        Args:
            target: The widget or tree item to flash
            color: The flash color
        """
        cls._pending_flash_widgets.add((target, color))
        logger.debug(f"📝 Scheduled flash for {type(target).__name__}")
        # Start coordinator immediately (flashes should be instant)
        cls._start_coordinated_update_timer()

    @classmethod
    def schedule_flash_restoration(cls, animator: Any, duration_ms: int):
        """Schedule flash restoration via coordinator to prevent event loop blocking.

        PERFORMANCE: Batches ALL flash restorations together instead of using individual
        QTimer callbacks that block the event loop sequentially.

        Args:
            animator: WidgetFlashAnimator instance awaiting restoration
            duration_ms: How long until restoration (typically 300ms)
        """
        # Add to pending restorations
        cls._pending_flash_restorations.append(animator)
        # Get animator type (WidgetFlashAnimator has 'widget', TreeItemFlashAnimator has 'tree_widget')
        animator_type = type(animator).__name__
        logger.debug(f"📝 Scheduled flash restoration for {animator_type}")

        # Start/restart single restoration timer for ALL flashes
        from PyQt6.QtCore import QTimer
        if cls._flash_restoration_timer is not None:
            # Don't restart - let existing timer handle all restorations
            pass
        else:
            # Create new timer for batch restoration
            cls._flash_restoration_timer = QTimer()
            cls._flash_restoration_timer.setSingleShot(True)
            cls._flash_restoration_timer.timeout.connect(cls._execute_flash_restorations)
            cls._flash_restoration_timer.start(duration_ms)
            logger.debug(f"⏱️  Started flash restoration timer ({duration_ms}ms) for {len(cls._pending_flash_restorations)} flashes")

    @classmethod
    def _execute_flash_restorations(cls):
        """Batch restore ALL pending flash animations to prevent event loop blocking."""
        if not cls._pending_flash_restorations:
            return

        logger.debug(f"🔄 Batch restoring {len(cls._pending_flash_restorations)} flashes")

        # Restore all flashes in single pass
        for animator in cls._pending_flash_restorations:
            try:
                animator._restore_original()
            except Exception as e:
                logger.warning(f"Failed to restore flash: {e}")

        # Clear pending restorations
        cls._pending_flash_restorations.clear()
        cls._flash_restoration_timer = None

        logger.debug(f"✅ Batch flash restoration complete")

    @classmethod
    def _start_coordinated_update_timer(cls):
        """Start single shared timer for coordinated listener updates."""
        from PyQt6.QtCore import QTimer

        # Cancel existing timer if any
        if cls._coordinator_timer is not None:
            cls._coordinator_timer.stop()

        # Create and start new timer
        cls._coordinator_timer = QTimer()
        cls._coordinator_timer.setSingleShot(True)
        cls._coordinator_timer.timeout.connect(cls._execute_coordinated_updates)

        # Use same delay as cross-window refresh for consistency
        cls._coordinator_timer.start(cls.CROSS_WINDOW_REFRESH_DELAY_MS)
        logger.debug(f"⏱️  Started coordinator timer ({cls.CROSS_WINDOW_REFRESH_DELAY_MS}ms)")

    @classmethod
    def _execute_coordinated_updates(cls):
        """Execute ALL pending reactive updates simultaneously in single pass.

        John Carmack style: batch everything, execute once, minimize overhead.
        """
        total_updates = (
            len(cls._pending_listener_updates) +
            len(cls._pending_placeholder_refreshes) +
            len(cls._pending_flash_widgets)
        )

        if total_updates == 0:
            return

        logger.info(f"🚀 BATCH EXECUTION: {len(cls._pending_listener_updates)} listeners, "
                   f"{len(cls._pending_placeholder_refreshes)} placeholders, "
                   f"{len(cls._pending_flash_widgets)} flashes")

        # 1. Update all external listeners (PlateManager, PipelineEditor)
        for listener in cls._pending_listener_updates:
            try:
                if hasattr(listener, '_process_pending_preview_updates'):
                    listener._process_pending_preview_updates()
            except Exception as e:
                logger.error(f"❌ Error updating {listener.__class__.__name__}: {e}")

        # 2. Refresh all placeholders (PERFORMANCE: filtered by changed fields)
        for form_manager in cls._pending_placeholder_refreshes:
            try:
                form_manager._refresh_all_placeholders(changed_fields=cls._current_batch_changed_fields)
            except Exception as e:
                logger.error(f"❌ Error refreshing placeholders for {form_manager.field_id}: {e}")

        # 3. Execute all flash animations
        for target, color in cls._pending_flash_widgets:
            try:
                # Apply flash styling immediately
                from PyQt6.QtWidgets import QTreeWidgetItem
                from PyQt6.QtGui import QBrush, QFont, QColor

                if isinstance(target, QTreeWidgetItem):
                    # Tree item flash
                    target.setBackground(0, QBrush(color))
                    font = target.font(0)
                    font.setBold(True)
                    target.setFont(0, font)
                else:
                    # Widget flash (use flash animation helper)
                    from openhcs.pyqt_gui.widgets.shared.widget_flash_animation import WidgetFlashAnimator
                    animator = WidgetFlashAnimator.get_or_create_animator(target, color)
                    animator.flash_update()
            except Exception as e:
                logger.error(f"❌ Error flashing {type(target).__name__}: {e}")

        # Clear all pending updates
        cls._pending_listener_updates.clear()
        cls._pending_placeholder_refreshes.clear()
        cls._pending_flash_widgets.clear()
        cls._current_batch_changed_fields.clear()

        logger.debug(f"✅ Batch execution complete: {total_updates} updates in single pass")

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

                # CRITICAL: Capture "before" snapshot BEFORE unregistering
                # This snapshot must include ALL active form managers (not just this one) so that
                # when creating preview instances for flash detection, they have all live values
                # (e.g., if PipelineConfig closes but a step window is open, the step preview
                # instance needs the step's override values to resolve correctly)
                # scope_filter=None means no filtering (include ALL scopes: global + all plates)
                before_snapshot = type(self).collect_live_context()

                # Remove from registry
                self._active_form_managers.remove(self)

                # Remove from object-to-manager mapping
                obj_id = id(self.object_instance)
                if obj_id in type(self)._object_to_manager:
                    del type(self)._object_to_manager[obj_id]

                # CRITICAL: Clear _last_emitted_values so fast-path checks don't find stale values
                # This ensures that after the window closes, other windows don't think there are
                # unsaved changes just because this window's field paths are still in the dict
                logger.debug(f"🔍 Clearing _last_emitted_values for {self.field_id} (had {len(self._last_emitted_values)} entries)")
                self._last_emitted_values.clear()
                logger.debug(f"🔍 After clear: _last_emitted_values has {len(self._last_emitted_values)} entries")

                # Invalidate live context caches so external listeners drop stale data
                type(self)._live_context_token_counter += 1

                # CRITICAL: Clear unsaved changes cache ONLY for this window's scope
                # BUG FIX: Previously cleared the entire cache, which caused step editors
                # to lose their unsaved changes state when their parent PipelineConfig
                # editor closed. Now we only clear entries matching this window's scope_id.
                # Step editors have scope_ids like "plate::step_token" which don't match
                # the PipelineConfig's scope_id (just "plate"), so they are preserved.
                type(self)._clear_unsaved_changes_cache_for_scope(
                    self.scope_id, f"window_close: {self.field_id}"
                )

                # CRITICAL: Notify external listeners AFTER removing from registry
                # Use QTimer to defer notification until after current call stack completes
                # This ensures the form manager is fully unregistered before listeners process the changes
                # Send ALL fields as changed so batch update covers any changes
                from PyQt6.QtCore import QTimer

                # Capture variables in closure
                # CRITICAL: Collect ALL field paths from this manager AND nested managers
                # This ensures window close emits the same format as typing (e.g., "well_filter_config.well_filter")
                # not the root format (e.g., "GlobalPipelineConfig.well_filter_config")
                all_field_paths = self._collect_all_field_paths()
                object_instance = self.object_instance
                context_obj = self.context_obj
                external_listeners = list(self._external_listeners)

                def notify_listeners():
                    logger.debug(f"🔍 Notifying external listeners of window close (AFTER unregister)")
                    # Collect "after" snapshot (without form manager)
                    # scope_filter=None means no filtering (include ALL scopes: global + all plates)
                    logger.debug(f"🔍 Active form managers count: {len(ParameterFormManager._active_form_managers)}")
                    after_snapshot = ParameterFormManager.collect_live_context()
                    logger.debug(f"🔍 Collected after_snapshot: token={after_snapshot.token}")
                    logger.debug(f"🔍 after_snapshot.values keys: {list(after_snapshot.values.keys())}")

                    for listener, value_changed_handler, refresh_handler in external_listeners:
                        try:
                            logger.debug(f"🔍   Notifying listener {listener.__class__.__name__}")

                            # Use pre-collected field paths (same format as typing)
                            changed_fields = all_field_paths
                            logger.debug(f"🔍     Changed fields ({len(changed_fields)}): {changed_fields}")

                            # CRITICAL: Call dedicated handle_window_close() method if available
                            # This passes snapshots as parameters instead of storing them as state
                            if hasattr(listener, 'handle_window_close'):
                                logger.debug(f"🔍     Calling handle_window_close with snapshots: before={before_snapshot.token}, after={after_snapshot.token}")
                                listener.handle_window_close(
                                    object_instance,
                                    context_obj,
                                    before_snapshot,
                                    after_snapshot,
                                    changed_fields
                                )
                            elif value_changed_handler:
                                # Fallback: use old incremental update method
                                logger.debug(f"🔍     Falling back to value_changed_handler (no handle_window_close)")
                                for field_path in changed_fields:
                                    value_changed_handler(
                                        field_path,
                                        None,  # new_value not used for window close
                                        object_instance,
                                        context_obj
                                    )
                        except Exception as e:
                            logger.error(f"Error notifying external listener {listener.__class__.__name__}: {e}", exc_info=True)

                QTimer.singleShot(0, notify_listeners)

                # CRITICAL: Trigger refresh in all remaining windows
                # They were using this window's live values, now they need to revert to saved values
                for manager in self._active_form_managers:
                    # Refresh immediately (not deferred) since we're in a controlled close event
                    manager._refresh_with_live_context()

                # CRITICAL: DO NOT clear _configs_with_unsaved_changes cache here!
                # Other windows may still have unsaved changes that need to be preserved.
                # Example: If GlobalPipelineConfig closes with unsaved changes in field X,
                # and a Step editor also has unsaved changes in field X (overriding global),
                # the step's unsaved changes marker should remain because the step's resolved
                # state didn't change (it was already using its own override, not the global value).
                # The cache will be naturally updated as windows continue to edit values.

                # PERFORMANCE: Clear pending batched changes on form close (Phase 3)
                type(self)._pending_cross_window_changes.clear()

                # PERFORMANCE: Clear coordinator pending updates (Phase 3 coordinator)
                type(self)._pending_listener_updates.clear()

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
        logger.info(f"🔔 [{self.field_id}] _on_cross_window_context_changed: {field_path} = {new_value} (from {type(editing_object).__name__})")

        # Don't refresh if this is the window that made the change
        if editing_object is self.object_instance:
            logger.info(f"[{self.field_id}] Skipping cross-window update - same instance")
            return

        # Check if the change affects this form based on context hierarchy
        if not self._is_affected_by_context_change(editing_object, context_object):
            logger.debug(f"[{self.field_id}] Skipping cross-window update - not affected by {type(editing_object).__name__}")
            return

        logger.debug(f"[{self.field_id}] ✅ Cross-window update: {field_path} = {new_value} (from {type(editing_object).__name__})")

        # Pass the full field_path so nested managers can extract their relevant part
        # Example: "PipelineConfig.well_filter_config.well_filter"
        #   → Root manager extracts "well_filter_config"
        #   → Nested manager extracts "well_filter"
        # CRITICAL: Don't emit context_refreshed when refreshing due to another window's value change
        # The other window already emitted context_value_changed, which triggers incremental updates
        # Emitting context_refreshed here would cause full refreshes in pipeline editor
        self._schedule_cross_window_refresh(changed_field_path=field_path, emit_signal=False)

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

        GENERIC SCOPE RULE: A window is affected if its scope specificity >= source scope specificity.
        This prevents parent scopes from being affected by child scope changes.

        Examples:
        - GlobalPipelineConfig (specificity=0) changes affect ALL windows (specificity >= 0)
        - PipelineConfig (specificity=1) changes affect PipelineConfig and Steps (specificity >= 1), NOT GlobalPipelineConfig
        - Step (specificity=2) changes affect only Steps and Functions (specificity >= 2)

        Args:
            editing_object: The object being edited in the other window
            context_object: The context object used by the other window

        Returns:
            True if this form should refresh placeholders due to the change
        """
        # CRITICAL: Find the source manager that's making the change
        # We need its scope_id to determine if we're affected
        source_manager = None
        for manager in type(self)._active_form_managers:
            if manager.object_instance is editing_object:
                source_manager = manager
                break

        if source_manager is None:
            # Can't determine source scope - assume affected for safety
            logger.warning(f"[{self.field_id}] Could not find source manager for {type(editing_object).__name__} - assuming affected")
            return True

        # GENERIC SCOPE RULE: Compare scope specificities
        from openhcs.config_framework.dual_axis_resolver import get_scope_specificity
        source_specificity = get_scope_specificity(source_manager.scope_id)
        self_specificity = get_scope_specificity(self.scope_id)

        # We're affected if our specificity >= source specificity
        # This means changes flow DOWN the hierarchy (global → plate → step), not UP
        is_affected = self_specificity >= source_specificity

        logger.info(
            f"[{self.field_id}] Scope check: source={source_manager.field_id} "
            f"(scope={source_manager.scope_id}, specificity={source_specificity}), "
            f"self=(scope={self.scope_id}, specificity={self_specificity}), "
            f"affected={is_affected}"
        )

        return is_affected

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

    def _find_live_values_for_type(self, ctx_type: type, live_context) -> dict:
        """Find live values for a context type, checking both exact type and lazy/base equivalents.

        Args:
            ctx_type: The type to find live values for
            live_context: Either a LiveContextSnapshot or a dict mapping types to their live values

        Returns:
            Live values dict if found, None otherwise
        """
        if not live_context:
            return None

        # Handle LiveContextSnapshot - search in both values and scoped_values
        if isinstance(live_context, LiveContextSnapshot):
            logger.debug(f"🔍 _find_live_values_for_type: Looking for {ctx_type.__name__} in LiveContextSnapshot (scope_id={self.scope_id})")
            logger.debug(f"🔍   values keys: {[t.__name__ for t in live_context.values.keys()]}")
            logger.debug(f"🔍   scoped_values keys: {list(live_context.scoped_values.keys())}")

            # CRITICAL FIX: Check if the value in live_context.values came from a compatible scope
            # live_context.values contains merged values from ALL scopes (latest value wins)
            # But we should ONLY use values from scopes that are compatible with current manager's scope
            # Scope hierarchy: Global (None) < Plate (plate_path) < Step (step_name)
            # A global manager (scope=None) should NOT see values from plate/step scopes
            # A plate manager (scope=plate_path) CAN see values from global scope, but not from other plates or steps
            if ctx_type in live_context.values:
                # Check which scope this config type belongs to
                config_scope = live_context.scopes.get(ctx_type.__name__) if live_context.scopes else None

                # GENERIC SCOPE RULE: Use get_scope_specificity() instead of hardcoded levels
                from openhcs.config_framework.dual_axis_resolver import get_scope_specificity
                current_specificity = get_scope_specificity(self.scope_id)
                config_specificity = get_scope_specificity(config_scope)

                # Only use this value if it's from the same scope or a less specific (more general) scope
                if config_specificity <= current_specificity:
                    logger.debug(f"🔍   Found {ctx_type.__name__} in global values (config_specificity={config_specificity} <= current_specificity={current_specificity})")
                    return live_context.values[ctx_type]
                else:
                    logger.debug(f"🔍   SKIPPING {ctx_type.__name__} from global values (config_specificity={config_specificity} > current_specificity={current_specificity}) - scope contamination prevention")

            # Then check scoped_values for this manager's scope
            if self.scope_id and self.scope_id in live_context.scoped_values:
                scoped_dict = live_context.scoped_values[self.scope_id]
                logger.debug(f"🔍   Checking scoped_values[{self.scope_id}]: {[t.__name__ for t in scoped_dict.keys()]}")
                if ctx_type in scoped_dict:
                    logger.debug(f"🔍   Found {ctx_type.__name__} in scoped_values[{self.scope_id}]")
                    return scoped_dict[ctx_type]

            # Also check parent scopes (e.g., plate scope when we're in step scope)
            if self.scope_id and "::" in self.scope_id:
                parent_scope = self.scope_id.rsplit("::", 1)[0]
                if parent_scope in live_context.scoped_values:
                    scoped_dict = live_context.scoped_values[parent_scope]
                    logger.debug(f"🔍   Checking parent scoped_values[{parent_scope}]: {[t.__name__ for t in scoped_dict.keys()]}")
                    if ctx_type in scoped_dict:
                        logger.debug(f"🔍   Found {ctx_type.__name__} in parent scoped_values[{parent_scope}]")
                        return scoped_dict[ctx_type]

            # Check lazy/base equivalents in global values
            from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
            from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService

            base_type = get_base_type_for_lazy(ctx_type)
            if base_type and base_type in live_context.values:
                # Check scope compatibility for base type
                config_scope = live_context.scopes.get(base_type.__name__) if live_context.scopes else None
                # GENERIC SCOPE RULE: Use get_scope_specificity() instead of hardcoded levels
                from openhcs.config_framework.dual_axis_resolver import get_scope_specificity
                current_specificity = get_scope_specificity(self.scope_id)
                config_specificity = get_scope_specificity(config_scope)

                if config_specificity <= current_specificity:
                    logger.debug(f"🔍   Found base type {base_type.__name__} in global values (config_specificity={config_specificity} <= current_specificity={current_specificity})")
                    return live_context.values[base_type]
                else:
                    logger.debug(f"🔍   SKIPPING base type {base_type.__name__} from global values (config_specificity={config_specificity} > current_specificity={current_specificity})")

            lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(ctx_type)
            if lazy_type and lazy_type in live_context.values:
                # Check scope compatibility for lazy type
                config_scope = live_context.scopes.get(lazy_type.__name__) if live_context.scopes else None
                # GENERIC SCOPE RULE: Use get_scope_specificity() instead of hardcoded levels
                from openhcs.config_framework.dual_axis_resolver import get_scope_specificity
                current_specificity = get_scope_specificity(self.scope_id)
                config_specificity = get_scope_specificity(config_scope)

                if config_specificity <= current_specificity:
                    logger.debug(f"🔍   Found lazy type {lazy_type.__name__} in global values (config_specificity={config_specificity} <= current_specificity={current_specificity})")
                    return live_context.values[lazy_type]
                else:
                    logger.debug(f"🔍   SKIPPING lazy type {lazy_type.__name__} from global values (config_specificity={config_specificity} > current_specificity={current_specificity})")

            logger.debug(f"🔍   NOT FOUND: {ctx_type.__name__}")
            return None

        # Handle plain dict (legacy path)
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
        Delegates to dual_axis_resolver.is_scope_visible for centralized scope logic.

        Args:
            other_scope_id: The scope_id of the other manager
            my_scope_id: The scope_id of this manager

        Returns:
            True if other_scope_id is visible from my_scope_id
        """
        from openhcs.config_framework.dual_axis_resolver import is_scope_visible
        return is_scope_visible(other_scope_id, my_scope_id)

    def _collect_live_context_from_other_windows(self) -> LiveContextSnapshot:
        """Collect live values from other open form managers for context resolution.

        REFACTORED: Now uses the main collect_live_context() class method instead of duplicating logic.

        Returns:
            LiveContextSnapshot with values (global) and scoped_values (scoped) properly separated
        """
        # Use the main class method with scope filter
        # This ensures we get the same structure as plate manager and other consumers
        return self.collect_live_context(scope_filter=self.scope_id)

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
