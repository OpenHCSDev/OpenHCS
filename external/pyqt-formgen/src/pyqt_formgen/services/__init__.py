"""
Service layer for form management.

Cross-cutting concerns and reusable services for signal management,
widget operations, and value collection.
"""

from .signal_service import SignalService
from .widget_service import WidgetService
from .value_collection_service import ValueCollectionService
from .flag_context_manager import FlagContextManager
from .field_change_dispatcher import FieldChangeDispatcher, FieldChangeEvent
from .parameter_ops_service import ParameterOpsService
from .enabled_field_styling_service import EnabledFieldStylingService
from .enum_dispatch_service import EnumDispatchService
from .search_service import SearchService
from .pattern_data_manager import PatternDataManager
from .system_monitor_core import SystemMonitorCore
from .persistent_system_monitor import PersistentSystemMonitor

# Also export as modules for form_init_service's ServiceRegistryMeta
from . import signal_service
from . import widget_service
from . import value_collection_service
from . import parameter_ops_service
from . import enabled_field_styling_service
from . import enum_dispatch_service
from . import search_service
from . import pattern_data_manager
from . import system_monitor_core
from . import persistent_system_monitor

__all__ = [
    "SignalService",
    "WidgetService",
    "ValueCollectionService",
    "FlagContextManager",
    "FieldChangeDispatcher",
    "FieldChangeEvent",
    "ParameterOpsService",
    "EnabledFieldStylingService",
    "EnumDispatchService",
    "SearchService",
    "PatternDataManager",
    "SystemMonitorCore",
    "PersistentSystemMonitor",
    "signal_service",
    "widget_service",
    "value_collection_service",
    "parameter_ops_service",
    "enabled_field_styling_service",
    "enum_dispatch_service",
    "search_service",
    "pattern_data_manager",
    "system_monitor_core",
    "persistent_system_monitor",
]
