"""
Dramatically simplified PyQt parameter form manager.

This demonstrates how the widget implementation can be drastically simplified
by leveraging the comprehensive shared infrastructure we've built.
"""

import dataclasses
from dataclasses import dataclass, is_dataclass, fields as dataclass_fields
import logging
from typing import Any, Dict, Type, Optional, Tuple, List
from abc import ABCMeta
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QScrollArea, QLabel, QPushButton,
    QLineEdit, QCheckBox, QComboBox, QGroupBox, QSpinBox, QDoubleSpinBox
)
from PyQt6.QtCore import Qt, pyqtSignal, QTimer

# Import ABC for type-safe widget creation
from openhcs.pyqt_gui.widgets.shared.widget_creation_types import ParameterFormManager as ParameterFormManagerABC


def _create_combined_metaclass(base_class: type, abc_meta: type = ABCMeta) -> type:
    """Dynamically create a combined metaclass for a base class and ABC.

    Resolves metaclass conflicts by creating a new metaclass that inherits
    from both the base class's metaclass and ABCMeta.

    Args:
        base_class: The base class (e.g., QWidget)
        abc_meta: The ABC metaclass (default: ABCMeta)

    Returns:
        A new metaclass combining both
    """
    base_metaclass = type(base_class)
    if base_metaclass is abc_meta:
        return base_metaclass

    # Create combined metaclass dynamically
    class CombinedMeta(base_metaclass, abc_meta):
        pass

    return CombinedMeta


# Create combined metaclass for ParameterFormManager
_ParameterFormManagerMeta = _create_combined_metaclass(QWidget, ABCMeta)

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

# Import service classes for Phase 1: Service Extraction
from openhcs.pyqt_gui.widgets.shared.services.widget_update_service import WidgetUpdateService
from openhcs.pyqt_gui.widgets.shared.services.placeholder_refresh_service import PlaceholderRefreshService
from openhcs.pyqt_gui.widgets.shared.services.enabled_field_styling_service import EnabledFieldStylingService

# Import service classes for Phase 2A: Quick Wins + Metaprogramming
from openhcs.pyqt_gui.widgets.shared.services.flag_context_manager import FlagContextManager, ManagerFlag
from openhcs.pyqt_gui.widgets.shared.services.signal_blocking_service import SignalBlockingService
from openhcs.pyqt_gui.widgets.shared.services.nested_value_collection_service import NestedValueCollectionService
from openhcs.pyqt_gui.widgets.shared.services.widget_finder_service import WidgetFinderService
from openhcs.pyqt_gui.widgets.shared.services.widget_styling_service import WidgetStylingService
from openhcs.pyqt_gui.widgets.shared.services.form_build_orchestrator import FormBuildOrchestrator
from openhcs.pyqt_gui.widgets.shared.services.parameter_reset_service import ParameterResetService

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


class ParameterFormManager(QWidget, ParameterFormManagerABC, metaclass=_ParameterFormManagerMeta):
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
    - Type-safe ABC inheritance for static type checking
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
                from .services.initialization_services import ParameterExtractionService
                from .services.dataclass_unpacker import unpack_to_self

                extracted = ParameterExtractionService.build(
                    object_instance, config.exclude_params, config.initial_values
                )
                # METAPROGRAMMING: Auto-unpack all fields to self
                # Field names match UnifiedParameterInfo for auto-extraction
                unpack_to_self(self, extracted, {'_parameter_descriptions': 'description', 'parameters': 'default_value', 'parameter_types': 'param_type'})

            # STEP 2: Build config (metaprogrammed service + auto-unpack)
            with timer("  Build config", threshold_ms=5.0):
                from .services.initialization_services import ConfigBuilderService
                from openhcs.ui.shared.parameter_form_service import ParameterFormService
                from .services.dataclass_unpacker import unpack_to_self

                self.service = ParameterFormService()
                form_config = ConfigBuilderService.build(
                    field_id, extracted, config.context_obj, config.color_scheme, config.parent_manager, self.service
                )
                # METAPROGRAMMING: Auto-unpack all fields to self
                unpack_to_self(self, form_config)

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
            self._initial_load_complete, self._block_cross_window_updates = False, False
            self.shared_reset_fields = (
                config.parent.shared_reset_fields
                if hasattr(config.parent, 'shared_reset_fields')
                else set()
            )

            # Store backward compatibility attributes
            self.parameter_info = self.config.parameter_info
            self.use_scroll_area = self.config.use_scroll_area
            self.function_target = self.config.function_target
            self.color_scheme = self.config.color_scheme

            # STEP 5: Initialize services (metaprogrammed service + auto-unpack)
            with timer("  Initialize services", threshold_ms=1.0):
                from .services.initialization_services import ServiceFactoryService
                from .services.dataclass_unpacker import unpack_to_self

                services = ServiceFactoryService.build()
                # METAPROGRAMMING: Auto-unpack all services to self with _ prefix
                unpack_to_self(self, services, prefix="_")

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
                from .services.signal_connection_service import SignalConnectionService
                SignalConnectionService.connect_all_signals(self)

                # NOTE: Cross-window registration now handled by CALLER using:
                #   with cross_window_registration(manager):
                #       dialog.exec()
                # For backward compatibility during migration, we still register here
                # TODO: Remove this after all callers are updated to use context manager
                SignalConnectionService.register_cross_window_signals(self)

            # Debounce timer for cross-window placeholder refresh
            self._cross_window_refresh_timer = None

            # STEP 8: Detect user-set fields for lazy dataclasses
            with timer("  Detect user-set fields", threshold_ms=1.0):
                if is_dataclass(object_instance):
                    for field_name, raw_value in self.parameters.items():
                        if raw_value is not None:
                            self._user_set_fields.add(field_name)

            # STEP 9: Mark initial load as complete
            is_nested = self._parent_manager is not None
            self._initial_load_complete = True
            if not is_nested:
                self._apply_to_nested_managers(
                    lambda name, manager: setattr(manager, '_initial_load_complete', True)
                )

            # STEP 10: Execute initial refresh strategy (enum dispatch)
            with timer("  Initial refresh", threshold_ms=10.0):
                from .services.initial_refresh_strategy import InitialRefreshStrategy
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
        config = FormManagerConfig(
            parent=parent,
            context_obj=context_obj,  # No default - None means inherit from thread-local global only
            scope_id=scope_id,
            color_scheme=color_scheme
        )
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

        # OPTIMIZATION: Skip expensive operations for nested configs
        # ANTI-DUCK-TYPING: _parent_manager always exists (set in __init__)
        is_nested = self._parent_manager is not None

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
        # For function parameters (no parent dataclass), use parameter name directly
        field_path = param_name if self.dataclass_type is None else self.service.get_field_path_with_fail_loud(self.dataclass_type, param_type)

        # Determine object instance (unified logic for current_value vs default)
        if current_value is not None:
            # If current_value is a dict (saved config), convert it back to dataclass instance
            object_instance = actual_type(**current_value) if isinstance(current_value, dict) and dataclasses.is_dataclass(actual_type) else current_value
        else:
            # Create a default instance of the dataclass type for parameter extraction
            object_instance = actual_type() if dataclasses.is_dataclass(actual_type) else actual_type

        # DELEGATE TO NEW CONSTRUCTOR: Use simplified constructor with FormManagerConfig
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
        converted_value = self.service.convert_value_to_type(converted_value, param_type, param_name, self.dataclass_type)

        return converted_value

    def _emit_parameter_change(self, param_name: str, value: Any) -> None:
        """Handle parameter change from widget and update parameter data model."""

        # Convert value using unified conversion method
        converted_value = self._convert_widget_value(value, param_name)

        # Update parameter in data model
        self.parameters[param_name] = converted_value

        # CRITICAL FIX: Track that user explicitly set this field
        # This prevents placeholder updates from destroying user values
        self._user_set_fields.add(param_name)

        # Emit signal only once - this triggers sibling placeholder updates
        self.parameter_changed.emit(param_name, converted_value)





    # Framework-specific methods for backward compatibility

    def reset_all_parameters(self) -> None:
        """Reset all parameters - just call reset_parameter for each parameter."""
        from openhcs.utils.performance_monitor import timer

        with timer(f"reset_all_parameters ({self.field_id})", threshold_ms=50.0):
            # PHASE 2A: Use FlagContextManager instead of manual flag management
            # This guarantees flags are restored even on exception
            with FlagContextManager.reset_context(self, block_cross_window=True):
                param_names = list(self.parameters.keys())
                for param_name in param_names:
                    # Call _reset_parameter_impl directly to avoid nested context managers
                    self._reset_parameter_impl(param_name)

            # OPTIMIZATION: Single placeholder refresh at the end instead of per-parameter
            # This is much faster than refreshing after each reset
            # Use refresh_all_placeholders directly to avoid cross-window context collection
            # (reset to defaults doesn't need live context from other windows)
            # REFACTORING: Inline delegate calls
            self._placeholder_refresh_service.refresh_all_placeholders(self, None)
            self._apply_to_nested_managers(lambda name, manager: manager._placeholder_refresh_service.refresh_all_placeholders(manager, None))



    def update_parameter(self, param_name: str, value: Any) -> None:
        """Update parameter value using shared service layer."""

        if param_name in self.parameters:
            # Convert value using service layer
            converted_value = self.service.convert_value_to_type(value, self.parameter_types.get(param_name, type(value)), param_name, self.dataclass_type)

            # Update parameter in data model
            self.parameters[param_name] = converted_value

            # CRITICAL FIX: Track that user explicitly set this field
            # This prevents placeholder updates from destroying user values
            self._user_set_fields.add(param_name)

            # Update corresponding widget if it exists
            if param_name in self.widgets:
                # REFACTORING: Inline delegate call
                self._widget_update_service.update_widget_value(self.widgets[param_name], converted_value, param_name, False, self)

            # Emit signal for PyQt6 compatibility
            # This will trigger both local placeholder refresh AND cross-window updates (via _emit_cross_window_change)
            self.parameter_changed.emit(param_name, converted_value)

    def reset_parameter(self, param_name: str) -> None:
        """Reset parameter to signature default."""
        if param_name not in self.parameters:
            return

        # PHASE 2A: Use FlagContextManager + ParameterResetService
        with FlagContextManager.reset_context(self, block_cross_window=False):
            reset_service = ParameterResetService()
            reset_service.reset_parameter(self, param_name)

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
            # CRITICAL FIX: Read actual current values from widgets, not initial parameters
            current_values = {}

            # Read current values from widgets
            for param_name in self.parameters.keys():
                # PHASE 2A: Use WidgetFinderService for consistent widget access
                widget = WidgetFinderService.get_widget_safe(self, param_name)
                if widget:
                    # REFACTORING: Inline delegate call
                    raw_value = self._widget_update_service.get_widget_value(widget)
                    # Apply unified type conversion
                    current_values[param_name] = self._convert_widget_value(raw_value, param_name)
                else:
                    # Fallback to initial parameter value if no widget
                    current_values[param_name] = self.parameters.get(param_name)

            # Checkbox validation is handled in widget creation

            # PHASE 2B: Collect values from nested managers using enum-driven dispatch
            # Eliminates if/elif type-checking smell with polymorphic dispatch
            def process_nested(name, manager):
                current_values[name] = self._nested_value_collection_service.collect_nested_value(
                    self, name, manager
                )

            self._apply_to_nested_managers(process_nested)

            # Lazy dataclasses are now handled by LazyDataclassEditor, so no structure preservation needed
            return current_values

    def get_user_modified_values(self) -> Dict[str, Any]:
        """
        Get only values that were explicitly set by the user (non-None raw values).

        For lazy dataclasses, this preserves lazy resolution for unmodified fields
        by only returning fields where the raw value is not None.

        For nested dataclasses, only include them if they have user-modified fields inside.
        """
        # ANTI-DUCK-TYPING: Use isinstance check against LazyDataclass base class
        if not is_lazy_dataclass(self.config):
            # For non-lazy dataclasses, return all current values
            return self.get_current_values()

        user_modified = {}
        current_values = self.get_current_values()

        # Only include fields where the raw value is not None
        for field_name, value in current_values.items():
            if value is not None:
                # CRITICAL: For nested dataclasses, we need to extract only user-modified fields
                # by checking the raw values (using object.__getattribute__ to avoid resolution)
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
                    # Non-dataclass field, include if not None
                    user_modified[field_name] = value

        return user_modified



    # DELETED: _build_context_stack - pointless wrapper around build_context_stack()
    # All callers now call build_context_stack() directly from context_layer_builders.py





    def _should_skip_updates(self) -> bool:
        """
        Check if updates should be skipped due to batch operations.

        REFACTORING: Consolidates duplicate flag checking logic.
        Returns True if in reset mode or blocking cross-window updates.
        """
        # Check self flags
        if getattr(self, '_in_reset', False) or getattr(self, '_block_cross_window_updates', False):
            return True

        # Check nested manager flags
        for nested_manager in self.nested_managers.values():
            if getattr(nested_manager, '_in_reset', False) or getattr(nested_manager, '_block_cross_window_updates', False):
                return True

        return False

    def _on_nested_parameter_changed(self, param_name: str, value: Any) -> None:
        """
        Handle parameter changes from nested forms.

        When a nested form's field changes:
        1. Refresh parent form's placeholders
        2. Emit parent's parameter_changed signal
        """
        # REFACTORING: Use consolidated flag checking
        if self._should_skip_updates():
            return

        # Collect live context from other windows (only for root managers)
        # REFACTORING: Inline delegate call
        if self._parent_manager is None:
            live_context = self._placeholder_refresh_service.collect_live_context_from_other_windows(self)
        else:
            live_context = None

        # Refresh parent form's placeholders with live context
        # REFACTORING: Inline delegate call
        self._placeholder_refresh_service.refresh_all_placeholders(self, live_context)

        # Refresh all nested managers' placeholders (including siblings) with live context
        # PHASE 2A: Use helper instead of lambda
        self._call_on_nested_managers('_refresh_all_placeholders', live_context=live_context)

        # CRITICAL: Also refresh enabled styling for all nested managers
        # This ensures that when one config's enabled field changes, siblings that inherit from it update their styling
        # Example: fiji_streaming_config.enabled inherits from napari_streaming_config.enabled
        # PHASE 2A: Use helper instead of lambda
        self._call_on_nested_managers('_refresh_enabled_styling')

        # CRITICAL: Propagate parameter change signal up the hierarchy
        # This ensures cross-window updates work for nested config changes
        # The root manager will emit context_value_changed via _emit_cross_window_change
        # IMPORTANT: We DO propagate 'enabled' field changes for cross-window styling updates
        self.parameter_changed.emit(param_name, value)





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
        # PHASE 2A: Delegate to WidgetStylingService
        WidgetStylingService.make_readonly(widget, self.config.color_scheme)

    # ==================== CROSS-WINDOW CONTEXT UPDATE METHODS ====================

    def _emit_cross_window_change(self, param_name: str, value: object):
        """Emit cross-window context change signal.

        This is connected to parameter_changed signal for root managers.

        Args:
            param_name: Name of the parameter that changed
            value: New value
        """
        # REFACTORING: Use consolidated flag checking
        if self._should_skip_updates():
            return

        field_path = f"{self.field_id}.{param_name}"
        self.context_value_changed.emit(field_path, value,
                                       self.object_instance, self.context_obj)

    def unregister_from_cross_window_updates(self):
        """Manually unregister this form manager from cross-window updates.

        This should be called when the window is closing (before destruction) to ensure
        other windows refresh their placeholders without this window's live values.
        """
        import logging
        logger = logging.getLogger(__name__)
        logger.info(f"🔍 UNREGISTER: {self.field_id} (id={id(self)}) unregistering from cross-window updates")
        logger.info(f"🔍 UNREGISTER: Active managers before: {len(self._active_form_managers)}")

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
                logger.info(f"🔍 UNREGISTER: Active managers after: {len(self._active_form_managers)}")

                # CRITICAL: Trigger refresh in all remaining windows
                # They were using this window's live values, now they need to revert to saved values
                for manager in self._active_form_managers:
                    # Refresh immediately (not deferred) since we're in a controlled close event
                    manager._refresh_with_live_context()
        except (ValueError, AttributeError):
            pass  # Already removed or list doesn't exist



    def _on_cross_window_event(self, editing_object: object, context_object: object, **kwargs):
        """REFACTORING: Unified handler for cross-window events - eliminates duplicate methods.

        Handles both context_value_changed and context_refreshed signals with identical logic.

        Args:
            editing_object: The object being edited/refreshed in the other window
            context_object: The context object used by the other window
            **kwargs: Ignored extra args (field_path, new_value from context_value_changed)
        """
        # Don't refresh if this is the window that triggered the event
        if editing_object is self.object_instance:
            return

        # Check if the event affects this form based on context hierarchy
        if not self._is_affected_by_context_change(editing_object, context_object):
            return

        # Debounce the refresh to avoid excessive updates
        self._schedule_cross_window_refresh()

    # Aliases for signal connections (Qt requires exact signature match)
    _on_cross_window_context_changed = _on_cross_window_event
    _on_cross_window_context_refreshed = _on_cross_window_event

    def _is_affected_by_context_change(self, editing_object: object, context_object: object) -> bool:
        """Determine if a context change from another window affects this form.

        Hierarchical rules:
        - GlobalPipelineConfig changes affect: PipelineConfig, Steps
        - PipelineConfig changes affect: Steps in that pipeline
        - Step changes affect: nothing (leaf node)

        Args:
            editing_object: The object being edited in the other window
            context_object: The context object used by the other window

        Returns:
            True if this form should refresh placeholders due to the change
        """
        from openhcs.core.config import GlobalPipelineConfig, PipelineConfig

        # If other window is editing GlobalPipelineConfig, everyone is affected
        if isinstance(editing_object, GlobalPipelineConfig):
            return True

        # If other window is editing PipelineConfig, check if we're a step in that pipeline
        if isinstance(editing_object, PipelineConfig):
            # We're affected if our context_obj is the same PipelineConfig instance
            return self.context_obj is editing_object

        # Step changes don't affect other windows (leaf node)
        return False

    def _schedule_cross_window_refresh(self):
        """Schedule a debounced placeholder refresh for cross-window updates."""
        # Cancel existing timer if any
        if self._cross_window_refresh_timer is not None:
            self._cross_window_refresh_timer.stop()

        # Schedule new refresh after 200ms delay (debounce)
        # REFACTORING: Inlined _do_cross_window_refresh (single-use method)
        def do_refresh():
            # REFACTORING: Inline delegate calls
            live_context = self._placeholder_refresh_service.collect_live_context_from_other_windows(self)
            self._placeholder_refresh_service.refresh_all_placeholders(self, live_context)
            self._apply_to_nested_managers(lambda name, manager: manager._placeholder_refresh_service.refresh_all_placeholders(manager, live_context))
            self._apply_to_nested_managers(lambda name, manager: manager._enabled_styling_service.refresh_enabled_styling(manager))
            self.context_refreshed.emit(self.object_instance, self.context_obj)

        self._cross_window_refresh_timer = QTimer()
        self._cross_window_refresh_timer.setSingleShot(True)
        self._cross_window_refresh_timer.timeout.connect(do_refresh)
        self._cross_window_refresh_timer.start(200)  # 200ms debounce






