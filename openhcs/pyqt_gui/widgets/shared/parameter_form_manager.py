"""PyQt parameter form manager - VIEW layer for ObjectState MODEL."""

from dataclasses import dataclass
import logging
from typing import Any, Dict, Type, Optional, List, Set, Callable
from PyQt6.QtWidgets import QWidget, QVBoxLayout, QScrollArea
from PyQt6.QtCore import Qt, pyqtSignal, QTimer

from openhcs.pyqt_gui.widgets.shared.widget_creation_types import ParameterFormManager as ParameterFormManagerABC, _CombinedMeta
from openhcs.utils.performance_monitor import timer
from openhcs.ui.shared.widget_operations import WidgetOperations
from openhcs.ui.shared.widget_factory import WidgetFactory
from openhcs.ui.shared.widget_creation_registry import create_pyqt6_registry
from .layout_constants import CURRENT_LAYOUT
from openhcs.pyqt_gui.widgets.shared.services.value_collection_service import ValueCollectionService
from openhcs.pyqt_gui.widgets.shared.services.signal_service import SignalService
from openhcs.pyqt_gui.widgets.shared.services.field_change_dispatcher import FieldChangeDispatcher, FieldChangeEvent
# LiveContextService deleted - functionality moved to ObjectStateRegistry
from openhcs.pyqt_gui.widgets.shared.services.flag_context_manager import FlagContextManager
from openhcs.pyqt_gui.widgets.shared.services.form_init_service import FormBuildOrchestrator, InitialRefreshStrategy

logger = logging.getLogger(__name__)
@dataclass
class FormManagerConfig:
    """
    Configuration for ParameterFormManager initialization.

    Consolidates 8 optional parameters into a single config object,
    reducing __init__ signature from 10 → 3 parameters (70% reduction).

    Follows OpenHCS dataclass-based configuration patterns.
    """
    parent: Optional[QWidget] = None
    context_obj: Optional[Any] = None
    exclude_params: Optional[List[str]] = None
    initial_values: Optional[Dict[str, Any]] = None
    parent_manager: Optional['ParameterFormManager'] = None
    read_only: bool = False
    scope_id: Optional[str] = None
    color_scheme: Optional[Any] = None
    use_scroll_area: Optional[bool] = None  # None = auto-detect (False for nested, True for root)
    state: Optional[Any] = None  # ObjectState instance - if provided, PFM delegates to it
    field_prefix: str = ''  # Dotted path prefix for accessing flat ObjectState (e.g., 'well_filter_config')


class ParameterFormManager(QWidget, ParameterFormManagerABC, metaclass=_CombinedMeta):
    """
    React-quality reactive form manager for PyQt6.

    Inherits from both QWidget and ParameterFormManagerABC with combined metaclass.
    All abstract methods MUST be implemented by this class.

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
    - React-style lifecycle hooks and reactive updates
    - Proper ABC inheritance with metaclass conflict resolution
    """

    parameter_changed = pyqtSignal(str, object)  # param_name, value

    # Cross-window context change signal (simplified API)
    # Args: (scope_id, field_path) - field_path is None for bulk refresh
    context_changed = pyqtSignal(str, str)  # scope_id, field_path

    # NOTE: Class-level cross-cutting concerns moved to LiveContextService:
    # - _active_form_managers -> LiveContextService._active_form_managers
    # - _external_listeners -> LiveContextService._external_listeners
    # - _live_context_token_counter -> LiveContextService._live_context_token_counter
    # - _live_context_cache -> LiveContextService._live_context_cache
    # - collect_live_context() -> LiveContextService.collect()
    # - register_external_listener() -> LiveContextService.register_external_listener()
    # - unregister_external_listener() -> LiveContextService.unregister_external_listener()
    # - trigger_global_cross_window_refresh() -> LiveContextService.trigger_global_refresh()

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

    @classmethod
    def should_use_async(cls, param_count: int) -> bool:
        """Determine if async widget creation should be used based on parameter count."""
        return cls.ASYNC_WIDGET_CREATION and param_count > cls.ASYNC_THRESHOLD

    # ========== STATE DELEGATION PROPERTIES ==========
    # ObjectState is single source of truth - PFM delegates all state access

    @property
    def parameters(self) -> Dict[str, Any]:
        """Get parameters scoped to this PFM's field_prefix.

        With flat storage, filters state.parameters to only include fields
        under this PFM's prefix, and strips the prefix from keys.

        Example:
          state.parameters = {
            'well_filter_config.well_filter': 2,
            'well_filter_config.enabled': True,
            'some_other_field': 'value'
          }
          PFM with field_prefix='well_filter_config' returns:
          {'well_filter': 2, 'enabled': True}
        """
        if not self.field_prefix:
            # Root PFM: return only top-level parameters (no dots)
            return {k: v for k, v in self.state.parameters.items() if '.' not in k}

        # Nested PFM: filter by prefix and strip prefix from keys
        prefix_dot = f'{self.field_prefix}.'
        result = {}
        for path, value in self.state.parameters.items():
            if path.startswith(prefix_dot):
                remainder = path[len(prefix_dot):]
                # Only direct children (no nested dots in remainder)
                if '.' not in remainder:
                    result[remainder] = value
        return result

    @property
    def parameter_types(self) -> Dict[str, Any]:
        """Derive parameter types from object_instance using UnifiedParameterAnalyzer.

        Single code path for all object types - that's the point of UnifiedParameterAnalyzer.
        Uses self.object_instance (target object for this PFM's scope), NOT self.state.object_instance (root).
        Filters by self.parameters keys (already scoped/stripped for nested PFMs).
        """
        from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer
        param_info_dict = UnifiedParameterAnalyzer.analyze(self.object_instance)
        return {name: info.param_type for name, info in param_info_dict.items() if name in self.parameters}

    @property
    def param_defaults(self) -> Dict[str, Any]:
        """Derive defaults from object_instance (the saved baseline).

        Uses self.object_instance (target object for this PFM's scope), NOT self.state.object_instance (root).
        Uses self.parameters keys (already scoped/stripped for nested PFMs).
        """
        return {name: object.__getattribute__(self.object_instance, name)
                for name in self.parameters.keys()
                if hasattr(self.object_instance, name)}

    @property
    def _parameter_descriptions(self) -> Dict[str, str]:
        """Delegate to ObjectState._parameter_descriptions."""
        return getattr(self.state, '_parameter_descriptions', {})

    def __init__(self, state: 'ObjectState', config: Optional[FormManagerConfig] = None):
        """
        Initialize PyQt parameter form manager with ObjectState (MODEL).

        PFM is purely VIEW - it receives ObjectState and delegates all MODEL
        concerns to it. ObjectState must be created by the lifecycle owner
        (or looked up from ObjectStateRegistry) before calling PFM.

        Args:
            state: ObjectState instance containing parameters, types, defaults, user_set_fields.
                   Created by lifecycle owner or looked up from ObjectStateRegistry.
            config: Optional configuration object for UI settings
        """
        # Import here to avoid circular dependency
        from openhcs.config_framework.object_state import ObjectState

        # Unpack config or use defaults
        config = config or FormManagerConfig()

        # Store field_prefix EARLY - needed for target_obj navigation
        self.field_prefix = config.field_prefix

        # For nested PFMs, navigate to the nested object using field_prefix
        # Root PFM: analyze state.object_instance directly
        # Nested PFM: traverse object_instance using field_prefix to get nested object
        target_obj = state.object_instance
        if self.field_prefix:
            for part in self.field_prefix.split('.'):
                target_obj = getattr(target_obj, part)

        # Derive field_id from the TARGET object type (nested type for nested PFMs)
        derived_field_id = type(target_obj).__name__

        with timer(f"ParameterFormManager.__init__ ({derived_field_id})", threshold_ms=5.0):
            QWidget.__init__(self, config.parent)

            # Store ObjectState reference - PFM delegates MODEL to state
            self.state = state

            # Store target object for this PFM's scope (root or nested)
            # CRITICAL: Nested PFMs need their own object_instance for type conversions, etc.
            self.object_instance = target_obj
            self.field_id = derived_field_id  # Derived from target type
            self.context_obj = state.context_obj
            self.scope_id = state.scope_id
            self.read_only = config.read_only
            self._parent_manager = config.parent_manager

            # Track completion callbacks for async widget creation
            self._on_build_complete_callbacks = []
            self._on_placeholder_refresh_complete_callbacks = []

            # STEP 1: State data is accessed via self.state (no copying)
            # Properties delegate to ObjectState - single source of truth

            # STEP 2: Build UI config (still needed for widget creation)
            with timer("  Build config", threshold_ms=5.0):
                from openhcs.ui.shared.parameter_form_service import ParameterFormService
                from openhcs.pyqt_gui.widgets.shared.services.form_init_service import (
                    ExtractedParameters, ConfigBuilderService
                )

                self.service = ParameterFormService()
                # Single code path for all object types - that's the point of UnifiedParameterAnalyzer
                from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer

                param_info_dict = UnifiedParameterAnalyzer.analyze(target_obj)
                # self.parameters property already filters/strips keys for our prefix
                derived_param_types = {name: info.param_type for name, info in param_info_dict.items() if name in self.parameters}

                # Access state data directly - ObjectState is single source of truth
                # Pass the scoped parameters and the target object for nested PFMs
                extracted = ExtractedParameters(
                    default_value=self.parameters,  # Use scoped parameters (filtered/stripped)
                    param_type=derived_param_types,
                    description=getattr(state, '_parameter_descriptions', {}),
                    object_instance=target_obj,  # Use nested object for nested PFMs
                )
                form_config = ConfigBuilderService.build(
                    derived_field_id, extracted, state.context_obj, config.color_scheme, config.parent_manager, self.service, config
                )
                # METAPROGRAMMING: Auto-unpack all fields to self
                ValueCollectionService.unpack_to_self(self, form_config)

            # STEP 3: Initialize VIEW-only attributes
            self.widgets, self.reset_buttons, self.nested_managers = {}, {}, {}
            self._pending_nested_managers: Dict[str, 'ParameterFormManager'] = {}

            # STEP 4: VIEW-only flags (state tracking is in ObjectState)
            self._initial_load_complete, self._block_cross_window_updates, self._in_reset = False, False, False
            self._dispatching = False
            self.shared_reset_fields = set()  # VIEW-only: tracks field paths for cross-window reset styling

            # CROSS-WINDOW: Connect to change notifications (only root managers)
            # Nested managers are internal to their window and should not participate in cross-window updates
            if self._parent_manager is None:
                from openhcs.config_framework.object_state import ObjectStateRegistry
                ObjectStateRegistry.connect_listener(self._on_live_context_changed)
                # Invalidate cache so newly opened windows build fresh snapshots
                ObjectStateRegistry.increment_token(notify=False)
            
            # Register hierarchy relationship for cross-window placeholder resolution
            if self.context_obj is not None and not self._parent_manager:
                from openhcs.config_framework.context_manager import register_hierarchy_relationship
                register_hierarchy_relationship(type(self.context_obj), type(self.object_instance))
            elif self._parent_manager is not None and self._parent_manager.object_instance and self.object_instance:
                # Nested manager: register relationship from parent to this nested object
                # Needed so is_ancestor_in_context recognizes parent → child when filtering live context
                from openhcs.config_framework.context_manager import register_hierarchy_relationship
                register_hierarchy_relationship(type(self._parent_manager.object_instance), type(self.object_instance))

            # Store backward compatibility attributes
            self.parameter_info = self.config.parameter_info
            self.use_scroll_area = self.config.use_scroll_area
            self.function_target = self.config.function_target
            self.color_scheme = self.config.color_scheme

            # STEP 5: Initialize services (metaprogrammed service + auto-unpack)
            with timer("  Initialize services", threshold_ms=1.0):
                from openhcs.pyqt_gui.widgets.shared.services.form_init_service import ServiceFactoryService
                services = ServiceFactoryService.build()
                # METAPROGRAMMING: Auto-unpack all services to self with _ prefix
                ValueCollectionService.unpack_to_self(self, services, prefix="_")

            # Get widget creator from registry
            self._widget_creator = create_pyqt6_registry()

            # ANTI-DUCK-TYPING: Initialize ABC-based widget operations
            self._widget_ops = WidgetOperations()
            self._widget_factory = WidgetFactory()
            self._context_event_coordinator = None

            # STEP 6: Set up UI
            with timer("  Setup UI (widget creation)", threshold_ms=10.0):
                self.setup_ui()

            # STEP 7: Connect signals (explicit service)
            with timer("  Connect signals", threshold_ms=1.0):
                SignalService.connect_all_signals(self)

                # NOTE: Cross-window registration now handled by CALLER using:
                #   with SignalService.cross_window_registration(manager):
                #       dialog.exec()
                # For backward compatibility during migration, we still register here
                # TODO: Remove this after all callers are updated to use context manager
                SignalService.register_cross_window_signals(self)

            # Debounce timer for cross-window placeholder refresh
            self._cross_window_refresh_timer = None

            # STEP 8: _user_set_fields starts empty and is populated only when user edits widgets
            # (via _emit_parameter_change). Do NOT populate during initialization, as that would
            # include inherited values that weren't explicitly set by the user.

            # STEP 9: Mark initial load as complete
            is_nested = self._parent_manager is not None
            self._initial_load_complete = True
            if not is_nested:
                self._apply_to_nested_managers(
                    lambda name, manager: setattr(manager, '_initial_load_complete', True)
                )

            # STEP 10: Execute initial refresh strategy (enum dispatch)
            with timer("  Initial refresh", threshold_ms=10.0):
                InitialRefreshStrategy.execute(self)

    # ==================== WIDGET CREATION METHODS ====================

    def setup_ui(self):
        """Set up the UI layout."""
        from openhcs.utils.performance_monitor import timer

        is_nested = self._parent_manager is not None

        with timer("    Layout setup", threshold_ms=1.0):
            layout = QVBoxLayout(self)
            layout.setSpacing(CURRENT_LAYOUT.main_layout_spacing)
            layout.setContentsMargins(*CURRENT_LAYOUT.main_layout_margins)

        # Always apply styling
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
        """Build form UI using orchestrator service."""
        from openhcs.utils.performance_monitor import timer

        with timer("      Create content widget", threshold_ms=1.0):
            content_widget = QWidget()
            content_layout = QVBoxLayout(content_widget)
            content_layout.setSpacing(CURRENT_LAYOUT.content_layout_spacing)
            content_layout.setContentsMargins(*CURRENT_LAYOUT.content_layout_margins)

        # PHASE 2A: Use orchestrator to eliminate async/sync duplication
        orchestrator = FormBuildOrchestrator()
        use_async = orchestrator.should_use_async(len(self.form_structure.parameters))
        orchestrator.build_widgets(self, content_layout, self.form_structure.parameters, use_async)

        return content_widget

    def _create_widget_for_param(self, param_info: Any) -> Any:
        """Create widget for a parameter. Type auto-detected from param_info."""
        from openhcs.pyqt_gui.widgets.shared.widget_creation_config import create_widget_parametric
        return create_widget_parametric(self, param_info)

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

    def _create_nested_form_inline(self, param_name: str, unwrapped_type: Type = None, current_value: Any = None) -> Any:
        """Create nested PFM that shares root ObjectState with different field_prefix.

        With flat storage, nested PFMs share the same ObjectState instance as the parent,
        but use a different field_prefix to scope their access.

        Args:
            param_name: Name of the nested parameter (becomes part of field_prefix)
            unwrapped_type: Ignored (kept for ABC compatibility)
            current_value: Ignored (kept for ABC compatibility)
        """
        # Build nested field_prefix
        nested_prefix = f'{self.field_prefix}.{param_name}' if self.field_prefix else param_name

        # Create nested PFM (VIEW) that shares the same ObjectState (MODEL)
        nested_config = FormManagerConfig(
            parent=self,
            parent_manager=self,
            color_scheme=self.config.color_scheme,
            field_prefix=nested_prefix,  # Scope access to nested fields
        )
        nested_manager = ParameterFormManager(
            state=self.state,  # CRITICAL: Share the same ObjectState instance
            config=nested_config
        )

        # Inherit lazy/global editing context from parent
        try:
            nested_manager.config.is_lazy_dataclass = self.config.is_lazy_dataclass
            nested_manager.config.is_global_config_editing = self.config.is_global_config_editing
        except Exception:
            pass

        # Store nested manager
        self.nested_managers[param_name] = nested_manager

        # Register with root manager for async completion tracking
        # Count parameters with nested_prefix
        param_count = sum(1 for path in self.state.parameters.keys() if path.startswith(f'{nested_prefix}.'))
        root_manager = self
        while root_manager._parent_manager is not None:
            root_manager = root_manager._parent_manager

        if self.should_use_async(param_count):
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

        # PyQt-specific type conversions first
        converted_value = convert_widget_value_to_type(value, param_type)

        # Then apply service layer conversion (enums, basic types, Union handling, etc.)
        converted_value = self.service.convert_value_to_type(converted_value, param_type, param_name, type(self.object_instance))

        return converted_value

    def reset_all_parameters(self) -> None:
        """Reset all parameters - just call reset_parameter for each parameter."""
        from openhcs.utils.performance_monitor import timer

        with timer(f"reset_all_parameters ({self.field_id})", threshold_ms=50.0):
            # PHASE 2A: Use FlagContextManager instead of manual flag management
            # This guarantees flags are restored even on exception
            with FlagContextManager.reset_context(self, block_cross_window=True):
                # CRITICAL: Iterate over form_structure.parameters instead of self.parameters
                # form_structure only contains visible (non-hidden) parameters,
                # while self.parameters may include ui_hidden parameters that don't have widgets
                param_names = [param_info.name for param_info in self.form_structure.parameters]
                for param_name in param_names:
                    # Call reset_parameter directly to avoid nested context managers
                    self.reset_parameter(param_name)

            # OPTIMIZATION: Single placeholder refresh at the end instead of per-parameter
            # This is much faster than refreshing after each reset
            # CRITICAL: Use refresh_with_live_context to build context stack from tree registry
            # Even when resetting to defaults, we need live context for sibling inheritance
            # REFACTORING: Inline delegate calls
            self._parameter_ops_service.refresh_with_live_context(self)



    def update_parameter(self, param_name: str, value: Any) -> None:
        """Update parameter value using shared service layer.

        With flat storage, prepends field_prefix to create full dotted path.
        """
        if param_name not in self.parameters:
            return

        # Convert value using service layer
        converted_value = self.service.convert_value_to_type(
            value, self.parameter_types.get(param_name, type(value)), param_name, type(self.object_instance)
        )

        # Update corresponding widget if it exists
        # ANTI-DUCK-TYPING: Skip widget update for nested containers (they don't implement ValueSettable)
        if param_name in self.widgets:
            widget = self.widgets[param_name]
            from openhcs.ui.shared.widget_protocols import ValueSettable
            if isinstance(widget, ValueSettable):
                self._widget_service.update_widget_value(widget, converted_value, param_name, False, self)

        # Build full dotted path for state update
        dotted_path = f'{self.field_prefix}.{param_name}' if self.field_prefix else param_name

        # Update state with full dotted path
        self.state.update_parameter(dotted_path, converted_value)

        # Route through dispatcher for consistent behavior (sibling refresh, cross-window, etc.)
        event = FieldChangeEvent(param_name, converted_value, self)
        FieldChangeDispatcher.instance().dispatch(event)

    def reset_parameter(self, param_name: str) -> None:
        """Reset parameter to signature default.

        With flat storage, prepends field_prefix to create full dotted path.
        """
        if param_name not in self.parameters:
            return

        # Build full dotted path for state update
        dotted_path = f'{self.field_prefix}.{param_name}' if self.field_prefix else param_name

        with FlagContextManager.reset_context(self, block_cross_window=False):
            self._parameter_ops_service.reset_parameter(self, param_name)

        reset_value = self.state.parameters.get(dotted_path)
        event = FieldChangeEvent(param_name, reset_value, self, is_reset=True)
        FieldChangeDispatcher.instance().dispatch(event)

    # DELETED: MODEL DELEGATION - callers use self.state.get_*() directly
    # DELETED: _on_nested_parameter_changed - replaced by FieldChangeDispatcher

    def _apply_to_nested_managers(self, callback: Callable[[str, 'ParameterFormManager'], None]) -> None:
        """Apply operation to all nested managers."""
        for param_name, nested_manager in self.nested_managers.items():
            callback(param_name, nested_manager)

    def _apply_callbacks_recursively(self, callback_list_name: str) -> None:
        """REFACTORING: Unified recursive callback application - eliminates duplicate methods.

        Args:
            callback_list_name: Name of the callback list attribute (e.g., '_on_build_complete_callbacks')
        """
        callback_list = getattr(self, callback_list_name)
        for callback in callback_list:
            callback()
        callback_list.clear()

        # Recursively apply nested managers' callbacks
        for nested_manager in self.nested_managers.values():
            nested_manager._apply_callbacks_recursively(callback_list_name)

    def _on_nested_manager_complete(self, nested_manager) -> None:
        """
        Called by nested managers when they complete async widget creation.

        ANTI-DUCK-TYPING: _pending_nested_managers always exists (set in __init__).
        """
        # Find and remove this manager from pending dict
        key_to_remove = None
        for key, manager in self._pending_nested_managers.items():
            if manager is nested_manager:
                key_to_remove = key
                break

        if key_to_remove:
            del self._pending_nested_managers[key_to_remove]

        # If all nested managers are done, delegate to orchestrator
        if len(self._pending_nested_managers) == 0:
            # PHASE 2A: Use orchestrator for post-build sequence
            orchestrator = FormBuildOrchestrator()
            orchestrator._execute_post_build_sequence(self)

    # ==================== CROSS-WINDOW CONTEXT UPDATE METHODS ====================

    # DELETED: _emit_cross_window_change - moved to FieldChangeDispatcher
    # DELETED: _update_thread_local_global_config - moved to ObjectState

    def _on_live_context_changed(self):
        """Handle notification that live context changed (another form edited a value).

        Schedule a placeholder refresh so this form shows updated inherited values.
        Uses emit_signal=False to prevent infinite ping-pong between forms.
        """
        # Skip if this form triggered the change
        if getattr(self, '_block_cross_window_updates', False):
            return
        self._schedule_cross_window_refresh(changed_field=None, emit_signal=False)

    def unregister_from_cross_window_updates(self):
        """Unregister from cross-window updates."""
        try:
            from openhcs.config_framework.object_state import ObjectStateRegistry
            ObjectStateRegistry.disconnect_listener(self._on_live_context_changed)
            if self.context_obj is not None and not self._parent_manager:
                from openhcs.config_framework.context_manager import unregister_hierarchy_relationship
                unregister_hierarchy_relationship(type(self.object_instance))
            # Invalidate cache + notify listeners that a form closed
            ObjectStateRegistry.increment_token()
        except Exception as e:
            logger.warning(f"Unregister error: {e}")

    # ========== DELEGATION TO LiveContextService ==========
    def _schedule_cross_window_refresh(self, changed_field: Optional[str] = None, emit_signal: bool = True):
        """Schedule a debounced placeholder refresh for cross-window updates.

        Args:
            changed_field: If specified, only refresh this field's placeholder (targeted).
                          If None, refresh all placeholders (bulk refresh).
            emit_signal: Whether to emit context_refreshed signal after refresh.
                        Set to False when refresh is triggered by another window's
                        context_refreshed to prevent infinite ping-pong loops.
        """
        # Cancel existing timer if any
        if self._cross_window_refresh_timer is not None:
            self._cross_window_refresh_timer.stop()

        def do_refresh():
            # Check if this manager was deleted before the timer fired
            try:
                from PyQt6 import sip
                if sip.isdeleted(self):
                    return
            except (ImportError, TypeError):
                pass
            if changed_field is not None:
                # Targeted refresh: only refresh the specific field that changed
                # This field might exist in this manager OR in nested managers
                self._refresh_field_in_tree(changed_field)
            else:
                # Bulk refresh: refresh all placeholders (save/cancel/code editor)
                self._parameter_ops_service.refresh_with_live_context(self)
                self._apply_to_nested_managers(lambda _, manager: manager._enabled_field_styling_service.refresh_enabled_styling(manager))

            # CRITICAL: Only root managers emit signals to avoid nested ping-pong
            if emit_signal and self._parent_manager is None:
                self.context_changed.emit(self.scope_id or "", changed_field or "")

        self._cross_window_refresh_timer = QTimer()
        self._cross_window_refresh_timer.setSingleShot(True)
        self._cross_window_refresh_timer.timeout.connect(do_refresh)
        self._cross_window_refresh_timer.start(10)  # 10ms debounce

    def _refresh_field_in_tree(self, field_name: str):
        """Refresh a field's placeholder in this manager and nested managers."""
        if field_name in self.widgets:
            self._parameter_ops_service.refresh_single_placeholder(self, field_name)
        for nested_manager in self.nested_managers.values():
            nested_manager._refresh_field_in_tree(field_name)
