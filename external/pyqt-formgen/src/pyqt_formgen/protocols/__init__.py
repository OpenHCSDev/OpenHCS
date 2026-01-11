"""
Widget protocol definitions and adapters.

ABC-based widget contracts that eliminate duck typing in favor of
explicit, fail-loud inheritance-based architecture.
"""

from .widget_protocols import (
    ValueGettable,
    ValueSettable,
    PlaceholderCapable,
    RangeConfigurable,
    EnumSelectable,
    ChangeSignalEmitter,
)
from .widget_adapters import (
    LineEditAdapter,
    SpinBoxAdapter,
    DoubleSpinBoxAdapter,
    ComboBoxAdapter,
    CheckBoxAdapter,
    PyQtWidgetMeta,
)
from .function_registry import FunctionRegistryProtocol, register_function_registry, get_function_registry
from .preview_formatter import PreviewFormatterRegistry, register_preview_formatter
from .form_config import FormGenConfig, set_form_config, get_form_config
from .llm_service import LLMServiceProtocol, register_llm_service, get_llm_service
from .codegen_provider import CodegenProvider, register_codegen_provider, get_codegen_provider
from .log_providers import (
    LogDiscoveryProvider,
    ServerScanProvider,
    register_log_discovery_provider,
    get_log_discovery_provider,
    register_server_scan_provider,
    get_server_scan_provider,
)
from .window_factory import WindowFactoryProtocol, register_window_factory, get_window_factory
from .component_selection import (
    ComponentSelectionProvider,
    FunctionSelectionProvider,
    register_component_selection_provider,
    get_component_selection_provider,
    register_function_selection_provider,
    get_function_selection_provider,
)

__all__ = [
    "ValueGettable",
    "ValueSettable",
    "PlaceholderCapable",
    "RangeConfigurable",
    "EnumSelectable",
    "ChangeSignalEmitter",
    "LineEditAdapter",
    "SpinBoxAdapter",
    "DoubleSpinBoxAdapter",
    "ComboBoxAdapter",
    "CheckBoxAdapter",
    "PyQtWidgetMeta",
    "FunctionRegistryProtocol",
    "register_function_registry",
    "get_function_registry",
    "PreviewFormatterRegistry",
    "register_preview_formatter",
    "FormGenConfig",
    "set_form_config",
    "get_form_config",
    "LLMServiceProtocol",
    "register_llm_service",
    "get_llm_service",
    "CodegenProvider",
    "register_codegen_provider",
    "get_codegen_provider",
    "LogDiscoveryProvider",
    "ServerScanProvider",
    "register_log_discovery_provider",
    "get_log_discovery_provider",
    "register_server_scan_provider",
    "get_server_scan_provider",
    "WindowFactoryProtocol",
    "register_window_factory",
    "get_window_factory",
    "ComponentSelectionProvider",
    "FunctionSelectionProvider",
    "register_component_selection_provider",
    "get_component_selection_provider",
    "register_function_selection_provider",
    "get_function_selection_provider",
]
