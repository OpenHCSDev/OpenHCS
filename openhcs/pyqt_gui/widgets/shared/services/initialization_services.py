"""
Metaprogrammed initialization services for ParameterFormManager.

Auto-generates service classes from builder functions using decorator-based registry.
All boilerplate eliminated via type introspection and auto-discovery.
"""

from dataclasses import dataclass, field, make_dataclass, fields as dataclass_fields
from typing import Any, Dict, Optional, Type, Callable
import inspect
import sys
from abc import ABC

from .initialization_step_factory import InitializationStepFactory
from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer
from openhcs.ui.shared.parameter_form_config_factory import pyqt_config
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.config_framework import get_base_config_type
from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService

# Import all service classes
from . import (
    widget_update_service,
    placeholder_refresh_service,
    enabled_field_styling_service,
    widget_finder_service,
    widget_styling_service,
    form_build_orchestrator,
    parameter_reset_service,
    nested_value_collection_service,
    signal_blocking_service,
    signal_connection_service,
    enum_dispatch_service,
)


# ============================================================================
# Builder Registry (auto-generates services via decorator)
# ============================================================================

_BUILDER_REGISTRY: Dict[Type, tuple[str, Callable]] = {}  # {output_type: (service_name, builder_func)}


# ============================================================================
# Output Dataclasses
# ============================================================================

@dataclass
class ExtractedParameters:
    """Result of parameter extraction from object_instance.

    Auto-discovery rules:
    - Regular fields are auto-extracted from UnifiedParameterInfo
    - Fields with field(metadata={'initial_values': True}) receive initial_values override
    - Fields with field(metadata={'computed': callable}) use the callable

    Field names MUST match UnifiedParameterInfo field names for auto-extraction.
    """
    default_value: Dict[str, Any] = field(default_factory=dict, metadata={'initial_values': True})
    param_type: Dict[str, Type] = field(default_factory=dict)
    description: Dict[str, str] = field(default_factory=dict)
    dataclass_type: Type = field(default=None, metadata={'computed': lambda obj, *_: type(obj)})


@dataclass
class ParameterFormConfig:
    """Configuration object for ParameterFormManager."""
    config: Any  # The pyqt_config object
    form_structure: Any  # Result of service.analyze_parameters()
    global_config_type: Type
    placeholder_prefix: str


@dataclass
class DerivationContext:
    """Context for computing derived config values via properties."""
    context_obj: Any
    extracted: ExtractedParameters
    color_scheme: Any

    @property
    def global_config_type(self) -> Type:
        return getattr(self.context_obj, 'global_config_type', get_base_config_type())

    @property
    def placeholder_prefix(self) -> str:
        return "Pipeline default"

    @property
    def is_lazy_dataclass(self) -> bool:
        return self.extracted.dataclass_type and LazyDefaultPlaceholderService.has_lazy_resolution(self.extracted.dataclass_type)

    @property
    def is_global_config_editing(self) -> bool:
        return not self.is_lazy_dataclass


# METAPROGRAMMING: Auto-generate ManagerServices dataclass via metaclass
class ServiceRegistryMeta(type):
    """Metaclass that auto-discovers service classes from imported modules."""

    def __new__(mcs, name, bases, namespace):
        # Auto-discover all service classes from current module's globals
        current_module = sys.modules[__name__]
        service_fields = [('service', type(None), field(default=None))]

        for attr_name in dir(current_module):
            attr = getattr(current_module, attr_name)
            # Check if it's a module and has a service class
            if not inspect.ismodule(attr):
                continue

            # Auto-discover service class from module (CamelCase version of module name)
            module_name = attr.__name__.split('.')[-1]
            class_name = ''.join(word.capitalize() for word in module_name.split('_'))

            if hasattr(attr, class_name):
                service_class = getattr(attr, class_name)
                # Skip abstract classes - only instantiate concrete services
                if inspect.isabstract(service_class):
                    continue
                service_fields.append((module_name, service_class, field(default=None)))

        # Generate dataclass using make_dataclass
        return make_dataclass(name, service_fields)


class ManagerServices(metaclass=ServiceRegistryMeta):
    """Auto-generated dataclass - fields created by ServiceRegistryMeta."""
    pass


# ============================================================================
# Decorator for auto-registering builders
# ============================================================================

def builder_for(output_type: Type, service_name: str):
    """Decorator to register builder function and auto-generate service class."""
    def decorator(func: Callable) -> Callable:
        _BUILDER_REGISTRY[output_type] = (service_name, func)
        return func
    return decorator


# ============================================================================
# Builder Functions (auto-registered)
# ============================================================================

# METAPROGRAMMING: Auto-generate builder functions from their output types
def _auto_generate_builders():
    """Auto-generate all builder functions via introspection of their output types."""

    # Builder 1: ExtractedParameters
    def _extract_parameters(object_instance, exclude_params, initial_values):
        param_info_dict = UnifiedParameterAnalyzer.analyze(object_instance, exclude_params=exclude_params or [])
        extracted = {}
        computed = {}

        for fld in dataclass_fields(ExtractedParameters):
            # Computed fields use their metadata callable
            if 'computed' in fld.metadata:
                computed[fld.name] = fld.metadata['computed'](object_instance, exclude_params, initial_values)
                continue

            # Auto-extract from UnifiedParameterInfo
            extracted[fld.name] = {name: getattr(info, fld.name) for name, info in param_info_dict.items()}

            # Override with initial_values if field has initial_values metadata
            if initial_values and fld.metadata.get('initial_values'):
                extracted[fld.name].update(initial_values)

        return ExtractedParameters(**extracted, **computed)

    # Builder 2: ParameterFormConfig
    def _build_config(field_id, extracted, context_obj, color_scheme, parent_manager, service):
        config = pyqt_config(
            field_id=field_id,
            color_scheme=color_scheme or PyQt6ColorScheme(),
            function_target=extracted.dataclass_type,
            use_scroll_area=True
        )

        # Derive context-dependent values
        ctx = DerivationContext(context_obj, extracted, color_scheme)
        vars(config).update(vars(ctx))

        # Create type-safe input for analyze_parameters using extracted fields
        from openhcs.ui.shared.parameter_form_service import ParameterAnalysisInput
        analysis_input = ParameterAnalysisInput(
            field_id=field_id,
            parent_dataclass_type=extracted.dataclass_type,
            **{k: getattr(extracted, k) for k in ['default_value', 'param_type', 'description']}
        )
        form_structure = service.analyze_parameters(analysis_input)

        return ParameterFormConfig(config, form_structure, ctx.global_config_type, ctx.placeholder_prefix)

    # Builder 3: ManagerServices
    def _create_services():
        services = {}
        for fld in dataclass_fields(ManagerServices):
            if fld.type is type(None):
                services[fld.name] = fld.default
                continue

            # Resolve dependencies only if class has custom __init__
            has_custom_init = fld.type.__init__ is not object.__init__
            sig = inspect.signature(fld.type.__init__) if has_custom_init else None
            params = [p for p in sig.parameters.values() if p.name != 'self'] if sig else []
            deps = {p.name: p.annotation() for p in params}
            services[fld.name] = fld.type(**deps)

        return ManagerServices(**services)

    # Register all builders
    builder_for(ExtractedParameters, 'ParameterExtractionService')(_extract_parameters)
    builder_for(ParameterFormConfig, 'ConfigBuilderService')(_build_config)
    builder_for(ManagerServices, 'ServiceFactoryService')(_create_services)


# Execute auto-generation
_auto_generate_builders()


# ============================================================================
# Auto-generate service classes from registry
# ============================================================================

# METAPROGRAMMING: Auto-generate all service classes from builder registry
for output_type, (service_name, builder_func) in _BUILDER_REGISTRY.items():
    service_class = InitializationStepFactory.create_step(service_name, output_type, builder_func)
    globals()[service_name] = service_class

