"""
OpenHCS Introspection Package

Re-exports from python_introspect with OpenHCS-specific type resolution registered.

This package provides:
- SignatureAnalyzer: Extract parameter info from functions/dataclasses
- UnifiedParameterAnalyzer: Unified interface for all parameter sources
- Lazy dataclass utilities: Discovery and patching for lazy dataclasses

The core introspection logic lives in python_introspect (external dependency).
This module registers OpenHCS-specific namespace providers and type resolvers.
"""

# Re-export from python_introspect
from python_introspect import (
    SignatureAnalyzer,
    ParameterInfo,
    DocstringInfo,
    DocstringExtractor,
    UnifiedParameterAnalyzer,
    UnifiedParameterInfo,
    register_namespace_provider,
    register_type_resolver,
)

# OpenHCS-specific utilities (stay in this repo)
from openhcs.introspection.lazy_dataclass_utils import (
    discover_lazy_dataclass_types,
    patch_lazy_constructors,
)


# =============================================================================
# REGISTER OPENHCS-SPECIFIC TYPE RESOLUTION
# =============================================================================

def _openhcs_namespace_provider():
    """Provide OpenHCS types for forward reference resolution."""
    try:
        import openhcs.config_framework.lazy_factory as lazy_module
        import openhcs.core.config as config_module
        return {**vars(lazy_module), **vars(config_module)}
    except ImportError:
        return {}


def _openhcs_type_resolver(t):
    """Resolve OpenHCS lazy types to their base types."""
    try:
        class_name = t.__name__

        # Handle PipelineConfig -> GlobalPipelineConfig
        if class_name == 'PipelineConfig':
            from openhcs.core.config import GlobalPipelineConfig
            return GlobalPipelineConfig

        # Handle LazyXxxConfig -> XxxConfig
        if class_name.startswith('Lazy') and class_name.endswith('Config'):
            base_class_name = class_name[4:]  # Remove 'Lazy'
            from openhcs.core import config as config_module
            if hasattr(config_module, base_class_name):
                return getattr(config_module, base_class_name)

        return None  # Defer to other resolvers
    except (ImportError, AttributeError):
        return None


# Register on module load
register_namespace_provider(_openhcs_namespace_provider)
register_type_resolver(_openhcs_type_resolver)


__all__ = [
    # Signature analysis (from python_introspect)
    'SignatureAnalyzer',
    'ParameterInfo',
    'DocstringInfo',
    'DocstringExtractor',
    # Unified analysis (from python_introspect)
    'UnifiedParameterAnalyzer',
    'UnifiedParameterInfo',
    # Plugin registration (from python_introspect)
    'register_namespace_provider',
    'register_type_resolver',
    # Lazy dataclass utilities (OpenHCS-specific)
    'discover_lazy_dataclass_types',
    'patch_lazy_constructors',
]

