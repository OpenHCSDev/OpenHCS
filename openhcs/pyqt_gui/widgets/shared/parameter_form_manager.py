"""
Dramatically simplified PyQt parameter form manager.

This demonstrates how the widget implementation can be drastically simplified
by leveraging the comprehensive shared infrastructure we've built.
"""

import dataclasses
from dataclasses import dataclass, field, is_dataclass, fields as dataclass_fields
import logging
from typing import Any, Dict, Type, Optional, Tuple, List
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QScrollArea, QLabel, QPushButton,
    QLineEdit, QCheckBox, QComboBox, QGroupBox, QSpinBox, QDoubleSpinBox
)
from PyQt6.QtCore import Qt, pyqtSignal, QTimer

# Import ABC for type-safe widget creation
from openhcs.pyqt_gui.widgets.shared.widget_creation_types import ParameterFormManager as ParameterFormManagerABC, _CombinedMeta

# Performance monitoring
from openhcs.utils.performance_monitor import timer, get_monitor

# ANTI-DUCK-TYPING: Import ABC-based widget system
# Replaces WIDGET_UPDATE_DISPATCH and WIDGET_GET_DISPATCH tables
from openhcs.ui.shared.widget_operations import WidgetOperations
from openhcs.ui.shared.widget_factory import WidgetFactory

# DELETED: WIDGET_UPDATE_DISPATCH - replaced with WidgetOperations.set_value()
# DELETED: WIDGET_GET_DISPATCH - replaced with WidgetOperations.get_value()

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

# Import consolidated services
from openhcs.pyqt_gui.widgets.shared.services.widget_service import WidgetService
from openhcs.pyqt_gui.widgets.shared.services.value_collection_service import ValueCollectionService
from openhcs.pyqt_gui.widgets.shared.services.signal_service import SignalService
from openhcs.pyqt_gui.widgets.shared.services.parameter_ops_service import ParameterOpsService
from openhcs.pyqt_gui.widgets.shared.services.enabled_field_styling_service import EnabledFieldStylingService
from openhcs.pyqt_gui.widgets.shared.services.flag_context_manager import FlagContextManager, ManagerFlag
from openhcs.pyqt_gui.widgets.shared.services.form_init_service import (
    FormBuildOrchestrator, InitialRefreshStrategy,
    ParameterExtractionService, ConfigBuilderService, ServiceFactoryService
)
from openhcs.pyqt_gui.widgets.shared.services.field_change_dispatcher import FieldChangeDispatcher, FieldChangeEvent
from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService, LiveContextSnapshot

# ANTI-DUCK-TYPING: Removed ALL_INPUT_WIDGET_TYPES tuple
# Widget discovery now uses ABC-based WidgetOperations.get_all_value_widgets()
# which automatically finds all widgets implementing ValueGettable ABC

# Keep Qt imports for backward compatibility with existing code
from PyQt6.QtWidgets import QLineEdit, QComboBox, QPushButton, QCheckBox, QLabel, QSpinBox, QDoubleSpinBox
from openhcs.pyqt_gui.widgets.shared.no_scroll_spinbox import NoScrollSpinBox, NoScrollDoubleSpinBox, NoScrollComboBox
from openhcs.pyqt_gui.widgets.enhanced_path_widget import EnhancedPathWidget

# DELETED: ALL_INPUT_WIDGET_TYPES - replaced with WidgetOperations.get_all_value_widgets()

# Import OpenHCS core components
# Old field path detection removed - using simple field name matching
from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
from openhcs.config_framework.lazy_factory import is_lazy_dataclass





class NoneAwareLineEdit(QLineEdit):
    """QLineEdit that properly handles None values for lazy dataclass contexts."""

    def get_value(self):
        """Get value, returning None for empty text instead of empty string."""
        text = self.text().strip()
        return None if text == "" else text

    def set_value(self, value):
        """Set value, handling None properly."""
        self.setText("" if value is None else str(value))


# Register NoneAwareLineEdit as implementing ValueGettable and ValueSettable
from openhcs.ui.shared.widget_protocols import ValueGettable, ValueSettable
ValueGettable.register(NoneAwareLineEdit)
ValueSettable.register(NoneAwareLineEdit)


# DELETED: _create_optimized_reset_button() - moved to widget_creation_config.py
# See widget_creation_config.py: _create_optimized_reset_button()


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


# Register NoneAwareIntEdit as implementing ValueGettable and ValueSettable
ValueGettable.register(NoneAwareIntEdit)
ValueSettable.register(NoneAwareIntEdit)


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

    # Class-level signal for cross-window context changes
    # Emitted when a form changes a value that might affect other open windows
    # Args: (field_path, new_value, editing_object, context_object)
    context_value_changed = pyqtSignal(str, object, object, object, str)  # field_path, new_value, editing_obj, context_obj, scope_id

    # Class-level signal for cascading placeholder refreshes
    # Emitted when a form's placeholders are refreshed due to upstream changes
    # This allows downstream windows to know they should re-collect live context
    # Args: (editing_object, context_object)
    context_refreshed = pyqtSignal(object, object, str)  # editing_obj, context_obj, scope_id

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
        """Determine if async widget creation should be used based on parameter count.

        Args:
            param_count: Number of parameters in the form

        Returns:
            True if async widget creation should be used, False otherwise
        """
        return cls.ASYNC_WIDGET_CREATION and param_count > cls.ASYNC_THRESHOLD

    def __init__(self, object_instance: Any, field_id: str, config: Optional[FormManagerConfig] = None):
        """
        Initialize PyQt parameter form manager with generic object introspection.

        Args:
            object_instance: Any object to build form for (dataclass, ABC constructor, step, etc.)
            field_id: Unique identifier for the form
            config: Optional configuration object (consolidates 8 optional parameters)
        """
        # Unpack config or use defaults
        config = config or FormManagerConfig()

        with timer(f"ParameterFormManager.__init__ ({field_id})", threshold_ms=5.0):
            QWidget.__init__(self, config.parent)

            # Store core configuration (5 lines - down from 8)
            self.object_instance = object_instance
            self.field_id = field_id
            self.context_obj = config.context_obj
            self.read_only = config.read_only
            self._parent_manager = config.parent_manager
            self.scope_id = config.parent_manager.scope_id if config.parent_manager else config.scope_id

            # Track completion callbacks for async widget creation
            self._on_build_complete_callbacks = []
            self._on_placeholder_refresh_complete_callbacks = []

            # STEP 1: Extract parameters (metaprogrammed service + auto-unpack)
            with timer("  Extract parameters", threshold_ms=2.0):
                extracted = ParameterExtractionService.build(
                    object_instance, config.exclude_params, config.initial_values
                )
                # METAPROGRAMMING: Auto-unpack all fields to self
                # Field names match UnifiedParameterInfo for auto-extraction
                ValueCollectionService.unpack_to_self(self, extracted, {'_parameter_descriptions': 'description', 'parameters': 'default_value', 'parameter_types': 'param_type'})

            # STEP 2: Build config (metaprogrammed service + auto-unpack)
            with timer("  Build config", threshold_ms=5.0):
                from openhcs.ui.shared.parameter_form_service import ParameterFormService

                self.service = ParameterFormService()
                form_config = ConfigBuilderService.build(
                    field_id, extracted, config.context_obj, config.color_scheme, config.parent_manager, self.service, config
                )
                # METAPROGRAMMING: Auto-unpack all fields to self
                ValueCollectionService.unpack_to_self(self, form_config)

            # STEP 3: Extract parameter defaults for reset functionality
            with timer("  Extract parameter defaults", threshold_ms=1.0):
                from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer
                analysis_target = (
                    type(object_instance)
                    if dataclasses.is_dataclass(object_instance) or (hasattr(object_instance, '__class__') and not callable(object_instance))
                    else object_instance
                )
                defaults_info = UnifiedParameterAnalyzer.analyze(analysis_target, exclude_params=config.exclude_params or [])
                self.param_defaults = {name: info.default_value for name, info in defaults_info.items()}

            # STEP 4: Initialize tracking attributes (consolidated)
            self.widgets, self.reset_buttons, self.nested_managers = {}, {}, {}
            self.reset_fields, self._user_set_fields = set(), set()

            # CRITICAL FIX: Initialize _user_set_fields from _explicitly_set_fields if present
            # This preserves which fields were user-set when reloading a saved config
            if hasattr(object_instance, '_explicitly_set_fields'):
                explicitly_set = getattr(object_instance, '_explicitly_set_fields')
                if isinstance(explicitly_set, set):
                    self._user_set_fields = explicitly_set.copy()
                    logger.debug(f"🔍 INIT: Loaded _user_set_fields from _explicitly_set_fields: {self._user_set_fields}")

            # ANTI-DUCK-TYPING: Initialize ALL flags so FlagContextManager doesn't need getattr defaults
            self._initial_load_complete, self._block_cross_window_updates, self._in_reset = False, False, False
            self.shared_reset_fields = (
                config.parent.shared_reset_fields
                if hasattr(config.parent, 'shared_reset_fields')
                else set()
            )

            # CROSS-WINDOW: Register in active managers list (only root managers)
            # Nested managers are internal to their window and should not participate in cross-window updates
            if self._parent_manager is None:
                LiveContextService.register(self)
                # Connect to change notifications to refresh placeholders when other forms change
                LiveContextService.connect_listener(self._on_live_context_changed)
            
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
        if not is_dataclass(dataclass_instance):
            raise ValueError(f"{type(dataclass_instance)} is not a dataclass")

        # Use simplified constructor with automatic parameter extraction
        # CRITICAL: Do NOT default context_obj to dataclass_instance
        # This creates circular context bug where form uses itself as parent
        # Caller must explicitly pass context_obj if needed (e.g., Step Editor passes pipeline_config)

        # CRITICAL: Store use_scroll_area in a temporary attribute so ConfigBuilderService can use it
        # This is a workaround because FormManagerConfig doesn't have use_scroll_area field
        # but we need to pass it through to the config building process
        config = FormManagerConfig(
            parent=parent,
            context_obj=context_obj,  # No default - None means inherit from thread-local global only
            scope_id=scope_id,
            color_scheme=color_scheme,
        )

        # Store use_scroll_area as a temporary attribute on the config object
        # ConfigBuilderService will check for this and use it if present
        config._use_scroll_area_override = use_scroll_area

        return cls(
            object_instance=dataclass_instance,
            field_id=field_id,
            config=config
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
        config = FormManagerConfig(
            parent=parent,
            context_obj=context_obj
        )
        return cls(
            object_instance=object_instance,
            field_id=field_id,
            config=config
        )



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
            logger.info(f"🔧 {self.field_id}: is_nested={is_nested}, use_scroll_area={self.config.use_scroll_area}, will_create_scroll={self.config.use_scroll_area and not is_nested}")
            if self.config.use_scroll_area and not is_nested:
                scroll_area = QScrollArea()
                scroll_area.setWidgetResizable(True)
                scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
                scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
                scroll_area.setWidget(form_widget)
                layout.addWidget(scroll_area)
                logger.info(f"  ✅ Created scroll area for {self.field_id}")
            else:
                layout.addWidget(form_widget)
                logger.info(f"  ⏭️ Skipped scroll area for {self.field_id} (nested or disabled)")

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
        """
        Create widget for a single parameter based on its type.

        Uses parametric dispatch for all widget types (REGULAR, NESTED, OPTIONAL_NESTED).

        Args:
            param_info: Parameter information (OptionalDataclassInfo, DirectDataclassInfo, or GenericInfo)

        Returns:
            QWidget: The created widget
        """
        from openhcs.pyqt_gui.widgets.shared.widget_creation_config import (
            create_widget_parametric,
            WidgetCreationType
        )

        # Type-safe dispatch using discriminated unions
        from openhcs.ui.shared.parameter_info_types import OptionalDataclassInfo, DirectDataclassInfo

        if isinstance(param_info, OptionalDataclassInfo):
            # Optional[Dataclass]: use parametric dispatch
            return create_widget_parametric(self, param_info, WidgetCreationType.OPTIONAL_NESTED)
        elif isinstance(param_info, DirectDataclassInfo):
            # Direct dataclass (non-optional): use parametric dispatch
            return create_widget_parametric(self, param_info, WidgetCreationType.NESTED)
        else:
            # All regular types (including Optional[regular]): use parametric dispatch
            return create_widget_parametric(self, param_info, WidgetCreationType.REGULAR)

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

    def _create_nested_form_inline(self, param_name: str, param_type: Type, current_value: Any) -> Any:
        """Create nested form - simplified to let constructor handle parameter extraction"""
        # REFACTORING PRINCIPLE: Extract duplicate type unwrapping (was repeated 3 times)
        actual_type = ParameterTypeUtils.get_optional_inner_type(param_type) if ParameterTypeUtils.is_optional(param_type) else param_type

        # Get actual field path from FieldPathDetector (no artificial "nested_" prefix)
        # For function parameters (no parent object), use parameter name directly
        obj_type = type(self.object_instance) if self.object_instance else None
        field_path = param_name if obj_type is None else self.service.get_field_path_with_fail_loud(obj_type, param_type)

        # Determine object instance (unified logic for current_value vs default)
        if current_value is not None:
            # If current_value is a dict (saved config), convert it back to dataclass instance
            object_instance = actual_type(**current_value) if isinstance(current_value, dict) and dataclasses.is_dataclass(actual_type) else current_value
        else:
            # Create a default instance of the dataclass type for parameter extraction
            object_instance = actual_type() if dataclasses.is_dataclass(actual_type) else actual_type

        # DELEGATE TO NEW CONSTRUCTOR: Use simplified constructor with FormManagerConfig
        # Nested managers use parent manager's scope_id for cross-window grouping
        nested_config = FormManagerConfig(
            parent=self,
            context_obj=self.context_obj,
            parent_manager=self,  # Pass parent manager so setup_ui() can detect nested configs
            color_scheme=self.config.color_scheme,
            scope_id=self.scope_id
        )
        nested_manager = ParameterFormManager(
            object_instance=object_instance,
            field_id=field_path,
            config=nested_config
        )

        # Inherit lazy/global editing context from parent so resets behave correctly in nested forms
        # CRITICAL FIX: Nested forms must inherit is_global_config_editing from parent
        # This ensures GLOBAL_STATIC_DEFAULTS layer is applied to nested forms when editing GlobalPipelineConfig
        # Without this, reset fields show stale loaded values instead of static defaults
        try:
            nested_manager.config.is_lazy_dataclass = self.config.is_lazy_dataclass
            nested_manager.config.is_global_config_editing = self.config.is_global_config_editing
        except Exception:
            pass

        # DISPATCHER ARCHITECTURE: No signal connection needed here.
        # The FieldChangeDispatcher handles all nested changes:
        # - Sibling refresh via isinstance() check
        # - Cross-window via full path construction
        # - Parent doesn't need to listen to nested changes

        # Store nested manager
        self.nested_managers[param_name] = nested_manager

        # CRITICAL: Register with root manager if it's tracking async completion
        # Only register if this nested manager will use async widget creation
        if dataclasses.is_dataclass(actual_type):
            param_count = len(dataclasses.fields(actual_type))

            # Find root manager
            root_manager = self
            while root_manager._parent_manager is not None:
                root_manager = root_manager._parent_manager

            # Register with root if it's tracking and this will use async (centralized logic)
            # ANTI-DUCK-TYPING: root_manager always has _pending_nested_managers
            if self.should_use_async(param_count):
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

        # PyQt-specific type conversions first
        converted_value = convert_widget_value_to_type(value, param_type)

        # Then apply service layer conversion (enums, basic types, Union handling, etc.)
        converted_value = self.service.convert_value_to_type(converted_value, param_type, param_name, type(self.object_instance))

        return converted_value

    # DELETED: _emit_parameter_change - replaced by FieldChangeDispatcher
    # DELETED: _on_enabled_field_changed_universal - moved to FieldChangeDispatcher





    # Framework-specific methods for backward compatibility

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
            self._parameter_ops_service.refresh_with_live_context(self, use_user_modified_only=False)



    def update_parameter(self, param_name: str, value: Any) -> None:
        """Update parameter value using shared service layer."""
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

        # Route through dispatcher for consistent behavior (sibling refresh, cross-window, etc.)
        event = FieldChangeEvent(param_name, converted_value, self)
        FieldChangeDispatcher.instance().dispatch(event)

    def reset_parameter(self, param_name: str) -> None:
        """Reset parameter to signature default."""
        logger.info(f"🔄 RESET_PARAMETER: {self.field_id}.{param_name}")

        if param_name not in self.parameters:
            logger.warning(f"  ⏭️  {param_name} not in parameters, skipping")
            return

        old_value = self.parameters.get(param_name)
        was_user_set = param_name in self._user_set_fields
        logger.info(f"  📊 Before reset: value={repr(old_value)[:30]}, user_set={was_user_set}")

        # PHASE 2A: Use FlagContextManager + ParameterOpsService
        with FlagContextManager.reset_context(self, block_cross_window=False):
            self._parameter_ops_service.reset_parameter(self, param_name)

        reset_value = self.parameters.get(param_name)
        is_user_set_after = param_name in self._user_set_fields
        logger.info(f"  📊 After reset: value={repr(reset_value)[:30]}, user_set={is_user_set_after}")

        # Route through dispatcher with is_reset=True (don't re-add to _user_set_fields)
        event = FieldChangeEvent(param_name, reset_value, self, is_reset=True)
        FieldChangeDispatcher.instance().dispatch(event)

    def _get_reset_value(self, param_name: str) -> Any:
        """Get reset value based on editing context.

        For global config editing: Use static class defaults (not None)
        For lazy config editing: Use signature defaults (None for inheritance)
        For functions: Use signature defaults
        """
        # For global config editing, use static class defaults instead of None
        if self.config.is_global_config_editing and self.object_instance:
            # Get static default from class attribute
            try:
                static_default = object.__getattribute__(type(self.object_instance), param_name)
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
            # CRITICAL FIX: Read actual current values from widgets, not initial parameters
            current_values = {}

            # Read current values from widgets
            for param_name in self.parameters.keys():
                # BUGFIX: For user-set fields, use self.parameters as source of truth
                # This prevents race conditions where widget hasn't been updated yet
                # or is in placeholder state during sibling context building
                if param_name in self._user_set_fields:
                    current_values[param_name] = self.parameters.get(param_name)

                    # DEBUG: Log well_filter_config.well_filter reads from parameters
                    if self.field_id == 'well_filter_config' and param_name == 'well_filter':
                        logger.warning(f"🔍 PARAM_READ: {self.field_id}.{param_name} from self.parameters={current_values[param_name]}")
                else:
                    # PHASE 2A: Use WidgetService for consistent widget access
                    widget = WidgetService.get_widget_safe(self, param_name)
                    if widget:
                        # REFACTORING: Inline delegate call
                        raw_value = self._widget_service.get_widget_value(widget)
                        # Apply unified type conversion
                        current_values[param_name] = self._convert_widget_value(raw_value, param_name)

                        # DEBUG: Log well_filter_config.well_filter widget reads
                        if self.field_id == 'well_filter_config' and param_name == 'well_filter':
                            is_placeholder = widget.property("is_placeholder_state")
                            logger.warning(f"🔍 WIDGET_READ: {self.field_id}.{param_name} raw={raw_value}, converted={current_values[param_name]}, is_placeholder={is_placeholder}")
                    else:
                        # Fallback to initial parameter value if no widget
                        current_values[param_name] = self.parameters.get(param_name)

            # Checkbox validation is handled in widget creation

            # PHASE 2B: Collect values from nested managers using enum-driven dispatch
            # Eliminates if/elif type-checking smell with polymorphic dispatch
            def process_nested(name, manager):
                current_values[name] = self._value_collection_service.collect_nested_value(
                    self, name, manager
                )

            self._apply_to_nested_managers(process_nested)

            # Lazy dataclasses are now handled by LazyDataclassEditor, so no structure preservation needed
            return current_values

    def get_user_modified_values(self) -> Dict[str, Any]:
        """
        Get only values that were explicitly set by the user.

        For lazy dataclasses, this preserves lazy resolution for unmodified fields
        by only returning fields that are in self._user_set_fields (tracked when user edits widgets).

        For nested dataclasses, only include them if they have user-modified fields inside.

        CRITICAL: This method uses self._user_set_fields to distinguish between:
        1. Values that were explicitly set by the user (in _user_set_fields)
        2. Values that were inherited from parent or set during initialization (not in _user_set_fields)
        """
        # ANTI-DUCK-TYPING: Use isinstance check against LazyDataclass base class
        if not is_lazy_dataclass(self.object_instance):
            # For non-lazy dataclasses, return all current values
            result = self.get_current_values()

            return result

        # PERFORMANCE OPTIMIZATION: Only read values for user-set fields
        # Instead of calling get_current_values() which reads ALL widgets,
        # we only need values for fields in _user_set_fields
        user_modified = {}

        # Fast path: if no user-set fields, return empty dict
        if not self._user_set_fields:
            return user_modified

        # DEBUG: Log what fields are tracked as user-set
        logger.debug(f"🔍 GET_USER_MODIFIED: {self.field_id} - _user_set_fields = {self._user_set_fields}")

        # Only include fields that were explicitly set by the user
        # PERFORMANCE: Read directly from self.parameters instead of calling get_current_values()
        for field_name in self._user_set_fields:
            # For user-set fields, self.parameters is always the source of truth
            # (updated by FieldChangeDispatcher before any refresh happens)
            value = self.parameters.get(field_name)

            # CRITICAL FIX: Include None values for user-set fields
            # When user clears a field (backspace/delete), the None value must propagate
            # to live context so other windows can update their placeholders
            if value is not None:
                # CRITICAL: For nested dataclasses, we need to extract only user-modified fields
                # by recursively calling get_user_modified_values() on the nested manager
                if is_dataclass(value) and not isinstance(value, type):
                    # Check if there's a nested manager for this field
                    nested_manager = self.nested_managers.get(field_name)
                    if nested_manager and hasattr(nested_manager, 'get_user_modified_values'):
                        # Recursively get user-modified values from nested manager
                        nested_user_modified = nested_manager.get_user_modified_values()

                        if nested_user_modified:
                            # Reconstruct nested dataclass instance from user-modified values
                            user_modified[field_name] = type(value)(**nested_user_modified)
                    else:
                        # No nested manager, extract raw field values from nested dataclass
                        nested_user_modified = {}
                        for field in dataclass_fields(value):
                            raw_value = object.__getattribute__(value, field.name)
                            if raw_value is not None:
                                nested_user_modified[field.name] = raw_value

                        # Only include if nested dataclass has user-modified fields
                        if nested_user_modified:
                            user_modified[field_name] = type(value)(**nested_user_modified)
                else:
                    # Non-dataclass field, include if user set it
                    user_modified[field_name] = value
            else:
                # User explicitly set this field to None (cleared it)
                # Include it so live context updates propagate to other windows
                user_modified[field_name] = None

        # DEBUG: Log what's being returned
        logger.debug(f"🔍 GET_USER_MODIFIED: {self.field_id} - returning user_modified = {user_modified}")

        return user_modified

    # ==================== TREE REGISTRY INTEGRATION ====================

    def get_current_values_as_instance(self) -> Any:
        """
        Get current form values reconstructed as an instance.

        Used by ConfigNode.get_live_instance() for context stack building.
        Returns the object instance with current form values applied.

        Returns:
            Instance with current form values
        """
        current_values = self.get_current_values()

        # For dataclasses, reconstruct instance with current values
        if is_dataclass(self.object_instance) and not isinstance(self.object_instance, type):
            return dataclasses.replace(self.object_instance, **current_values)

        # For non-dataclass objects, return object_instance as-is
        # (current values are tracked in self.parameters)
        return self.object_instance

    def get_user_modified_instance(self) -> Any:
        """
        Get instance with only user-edited fields.

        Used by ConfigNode.get_user_modified_instance() for reset logic.
        Only includes fields that the user has explicitly edited.

        Returns:
            Instance with only user-modified fields
        """
        user_modified = self.get_user_modified_values()

        # For dataclasses, create instance with only user-modified fields
        if is_dataclass(self.object_instance) and not isinstance(self.object_instance, type):
            # Start with None for all fields, only set user-modified ones
            all_fields = {f.name: None for f in dataclass_fields(self.object_instance)}
            all_fields.update(user_modified)
            return dataclasses.replace(self.object_instance, **all_fields)

        # For non-dataclass objects, return object_instance
        return self.object_instance

    # ==================== UPDATE CHECKING ====================

    def _should_skip_updates(self) -> bool:
        """
        Check if updates should be skipped due to batch operations.

        REFACTORING: Consolidates duplicate flag checking logic.
        Returns True if in reset mode or blocking cross-window updates.
        """
        # ANTI-DUCK-TYPING: Use direct attribute access (all flags initialized in __init__)
        # Check self flags
        if self._in_reset:
            logger.info(f"🚫 SKIP_CHECK: {self.field_id} has _in_reset=True")
            return True
        if self._block_cross_window_updates:
            logger.info(f"🚫 SKIP_CHECK: {self.field_id} has _block_cross_window_updates=True")
            return True

        # Check nested manager flags (nested managers are also ParameterFormManager instances)
        for nested_name, nested_manager in self.nested_managers.items():
            if nested_manager._in_reset:
                logger.info(f"🚫 SKIP_CHECK: {self.field_id} nested manager {nested_name} has _in_reset=True")
                return True
            if nested_manager._block_cross_window_updates:
                logger.info(f"🚫 SKIP_CHECK: {self.field_id} nested manager {nested_name} has _block_cross_window_updates=True")
                return True

        return False

    # DELETED: _on_nested_parameter_changed - replaced by FieldChangeDispatcher

    def _apply_to_nested_managers(self, operation_func: callable) -> None:
        """Apply operation to all nested managers."""
        for param_name, nested_manager in self.nested_managers.items():
            operation_func(param_name, nested_manager)

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



    def _make_widget_readonly(self, widget: QWidget):
        """
        Make a widget read-only without greying it out.

        Args:
            widget: Widget to make read-only
        """
        # PHASE 2A: Delegate to WidgetService
        WidgetService.make_readonly(widget, self.config.color_scheme)

    # ==================== CROSS-WINDOW CONTEXT UPDATE METHODS ====================

    # DELETED: _emit_cross_window_change - moved to FieldChangeDispatcher

    def _update_thread_local_global_config(self):
        """Update thread-local GlobalPipelineConfig with current form values.

        LIVE UPDATES ARCHITECTURE:
        This is called on every parameter change when editing GlobalPipelineConfig.
        It updates the thread-local storage so other windows see changes immediately.

        The original config is stored by ConfigWindow and restored on Cancel.
        """
        from openhcs.core.config import GlobalPipelineConfig
        from openhcs.config_framework.global_config import set_global_config_for_editing

        # Get current values from form
        current_values = self.get_current_values()

        # Reconstruct nested dataclasses from (type, dict) tuples
        from openhcs.config_framework.context_manager import get_base_global_config

        # Get the current thread-local config as base for merging
        base_config = get_base_global_config()

        # Reconstruct nested dataclasses, merging current values into base
        reconstructed_values = ValueCollectionService.reconstruct_nested_dataclasses(current_values, base_config)

        # Create new GlobalPipelineConfig instance with reconstructed values
        try:
            new_config = dataclasses.replace(base_config, **reconstructed_values)
            set_global_config_for_editing(GlobalPipelineConfig, new_config)
            logger.debug(f"🔍 LIVE_UPDATES: Updated thread-local GlobalPipelineConfig")
        except Exception as e:
            logger.warning(f"🔍 LIVE_UPDATES: Failed to update thread-local GlobalPipelineConfig: {e}")
            # Don't fail the whole operation if this fails
            pass

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
        """Unregister from cross-window updates.

        SIMPLIFIED: Just unregister from LiveContextService. The token increment
        in unregister() notifies all listeners to refresh.
        """
        logger.info(f"🔍 UNREGISTER: {self.field_id}")

        try:
            # Disconnect from change notifications
            LiveContextService.disconnect_listener(self._on_live_context_changed)

            # Unregister hierarchy relationship if this is a root manager
            if self.context_obj is not None and not self._parent_manager:
                from openhcs.config_framework.context_manager import unregister_hierarchy_relationship
                unregister_hierarchy_relationship(type(self.object_instance))

            # Remove from registry (triggers token increment → notifies listeners)
            LiveContextService.unregister(self)

        except Exception as e:
            logger.warning(f"🔍 UNREGISTER: Error: {e}")

    # ========== DELEGATION TO LiveContextService ==========
    # These methods delegate to LiveContextService for backward compatibility.
    # New code should use LiveContextService directly.

    @classmethod
    def trigger_global_cross_window_refresh(cls):
        """DEPRECATED: Use LiveContextService.trigger_global_refresh() instead."""
        LiveContextService.trigger_global_refresh()

    @classmethod
    def collect_live_context(cls, scope_filter=None, for_type: Optional[Type] = None) -> LiveContextSnapshot:
        """DEPRECATED: Use LiveContextService.collect() instead."""
        return LiveContextService.collect(scope_filter, for_type)

    @staticmethod
    def _is_scope_visible_static(manager_scope: str, filter_scope) -> bool:
        """DEPRECATED: Use LiveContextService._is_scope_visible() instead."""
        return LiveContextService._is_scope_visible(manager_scope, filter_scope)

    def _on_cross_window_context_changed(self, field_path: str, new_value: object,
                                          editing_object: object, context_object: object, editing_scope_id: str):
        """Handle context_value_changed signal from another window.

        Signal signature: (field_path, new_value, editing_object, context_object)

        Uses targeted placeholder refresh for the specific field that changed,
        rather than refreshing all placeholders.

        Args:
            field_path: The full path of the field that changed (e.g., "GlobalConfig.path_planning_config.well_filter")
            new_value: The new value of the field
            editing_object: The object being edited in the other window
            context_object: The context object used by the other window
        """
        # EARLY EXIT: Scope visibility check (cheapest check first)
        if not self._is_scope_visible_static(editing_scope_id, self.scope_id):
            return

        editing_type_name = type(editing_object).__name__ if editing_object else "None"
        context_type_name = type(context_object).__name__ if context_object else "None"
        logger.info(f"🔔 CROSS_WINDOW_RECV [{self.field_id}]: path={field_path}, value={repr(new_value)[:30]}, "
                   f"from={editing_type_name}, ctx={context_type_name}, my_scope={self.scope_id}")

        # Don't refresh if this is the window that triggered the event
        if editing_object is self.object_instance:
            logger.info(f"  ⏭️  SKIP: same instance")
            return

        # Check if the event affects this form based on context hierarchy
        if not self._is_affected_by_context_change(editing_object, context_object, editing_scope_id):
            logger.info(f"  ⏭️  SKIP: not affected by context change")
            return

        # Extract the leaf field name from the path
        # e.g., "GlobalConfig.path_planning_config.well_filter" → "well_filter"
        leaf_field = field_path.split(".")[-1] if field_path else None
        logger.info(f"  ✅ AFFECTED: scheduling refresh for field={leaf_field}")

        # Schedule targeted refresh for this specific field
        self._schedule_cross_window_refresh(changed_field=leaf_field, emit_signal=True)

    def _on_cross_window_context_refreshed(self, editing_object: object, context_object: object, editing_scope_id: str):
        """Handle context_refreshed signal from another window.

        Signal signature: (editing_object, context_object)

        This is a bulk refresh (e.g., save/cancel), so refresh all placeholders.

        Args:
            editing_object: The object being edited/refreshed in the other window
            context_object: The context object used by the other window
        """
        editing_type_name = type(editing_object).__name__ if editing_object else "None"
        context_type_name = type(context_object).__name__ if context_object else "None"
        logger.info(f"🔔 CROSS_WINDOW_REFRESH [{self.field_id}]: from={editing_type_name}, ctx={context_type_name}, my_scope={self.scope_id}")

        # Don't refresh if this is the window that triggered the event
        if editing_object is self.object_instance:
            logger.info(f"  ⏭️  SKIP: same instance")
            return

        # Check if the event affects this form based on context hierarchy
        if not self._is_affected_by_context_change(editing_object, context_object, editing_scope_id):
            logger.info(f"  ⏭️  SKIP: not affected by context change")
            return

        logger.info(f"  ✅ AFFECTED: scheduling BULK refresh")
        # Bulk refresh - no specific field
        self._schedule_cross_window_refresh(changed_field=None, emit_signal=False)

    def _is_affected_by_context_change(self, editing_object: object, context_object: object, editing_scope_id: str = "") -> bool:
        """Determine if a context change from another window affects this form.

        Hierarchical rules (GENERIC - uses config_framework hierarchy functions):
        - Global config changes affect: all forms using global context or descendants
        - Ancestor config changes affect: descendants in the hierarchy
        - Same-type config changes affect: forms with same context instance
        - Nested config changes (via fields) affect: configs that inherit from them
        - Leaf node changes affect: nothing

        Args:
            editing_object: The object being edited in the other window
            context_object: The context object used by the other window

        Returns:
            True if this form should refresh placeholders due to the change
        """
        from openhcs.config_framework import is_global_config_instance
        from openhcs.config_framework.context_manager import (
            is_ancestor_in_context,
            is_same_type_in_context,
            get_root_from_scope_key,
        )
        from dataclasses import fields, is_dataclass
        import typing

        # Root isolation: different plate roots don't affect each other
        my_root = get_root_from_scope_key(self.scope_id)
        editing_root = get_root_from_scope_key(editing_scope_id)
        if editing_root and my_root and editing_root != my_root:
            return False

        editing_type = type(editing_object)

        # Global config edits affect all (respecting root isolation above)
        if is_global_config_instance(editing_object):
            return True

        # Ancestor/same-type checks for context object
        if self.context_obj is not None:
            context_obj_type = type(self.context_obj)
            if is_ancestor_in_context(editing_type, context_obj_type):
                return True
            if is_same_type_in_context(editing_type, context_obj_type):
                return True

        # Check dataclass fields for direct type match (handles nested configs)
        if is_dataclass(editing_object) and is_dataclass(self.object_instance):
            for field in fields(type(self.object_instance)):
                if field.type == editing_type:
                    return True
                origin = typing.get_origin(field.type)
                if origin is typing.Union:
                    args = typing.get_args(field.type)
                    if editing_type in args:
                        return True

        return False

    def _schedule_cross_window_refresh(self, changed_field: Optional[str] = None, emit_signal: bool = True):
        """Schedule a debounced placeholder refresh for cross-window updates.

        Args:
            changed_field: If specified, only refresh this field's placeholder (targeted).
                          If None, refresh all placeholders (bulk refresh).
            emit_signal: Whether to emit context_refreshed signal after refresh.
                        Set to False when refresh is triggered by another window's
                        context_refreshed to prevent infinite ping-pong loops.
        """
        logger.info(f"⏰ SCHEDULE_REFRESH [{self.field_id}]: field={changed_field}, emit_signal={emit_signal}, scope={self.scope_id}")

        # Cancel existing timer if any
        if self._cross_window_refresh_timer is not None:
            self._cross_window_refresh_timer.stop()

        def do_refresh():
            # CRITICAL: Check if this manager was deleted before the timer fired
            # This can happen when a window is closed while a refresh is scheduled
            try:
                from PyQt6 import sip
                if sip.isdeleted(self):
                    logger.debug(f"🔄 DO_REFRESH: manager was deleted, skipping")
                    return
            except (ImportError, TypeError):
                pass  # sip not available or object not a Qt object

            logger.info(f"🔄 DO_REFRESH [{self.field_id}]: field={changed_field}, emit_signal={emit_signal}")
            if changed_field is not None:
                # Targeted refresh: only refresh the specific field that changed
                # This field might exist in this manager OR in nested managers
                self._refresh_field_in_tree(changed_field)
            else:
                # Bulk refresh: refresh all placeholders (save/cancel/code editor)
                self._parameter_ops_service.refresh_with_live_context(self, use_user_modified_only=False)
                self._apply_to_nested_managers(lambda _, manager: manager._enabled_field_styling_service.refresh_enabled_styling(manager))

            # CRITICAL: Only root managers emit signals to avoid nested ping-pong
            if emit_signal and self._parent_manager is None:
                self.context_refreshed.emit(self.object_instance, self.context_obj, self.scope_id)

        self._cross_window_refresh_timer = QTimer()
        self._cross_window_refresh_timer.setSingleShot(True)
        self._cross_window_refresh_timer.timeout.connect(do_refresh)
        self._cross_window_refresh_timer.start(10)  # 10ms debounce

    def _refresh_field_in_tree(self, field_name: str):
        """Refresh a specific field's placeholder in this manager and all nested managers.

        The field might be in this manager directly, or in any nested manager.
        We refresh it wherever it exists.

        Args:
            field_name: The leaf field name to refresh (e.g., "well_filter")
        """
        has_widget = field_name in self.widgets
        nested_names = list(self.nested_managers.keys())
        logger.info(f"  🌳 TREE [{self.field_id}]: field={field_name}, has_widget={has_widget}, nested={nested_names}")

        # Try to refresh in this manager
        if has_widget:
            self._parameter_ops_service.refresh_single_placeholder(self, field_name)

        # Also try in all nested managers (the field might be nested)
        for nested_manager in self.nested_managers.values():
            nested_manager._refresh_field_in_tree(field_name)
