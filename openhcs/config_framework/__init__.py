"""
Generic configuration framework for lazy dataclass resolution.

This framework provides a complete system for hierarchical configuration management
with lazy resolution, dual-axis inheritance, and UI integration.

Key Features:
- Lazy dataclass factory with dynamic field resolution
- Dual-axis inheritance (context hierarchy + sibling inheritance)
- Contextvars-based context management
- Placeholder text generation for UI
- Thread-local global configuration storage

Quick Start:
    >>> from openhcs.config_framework import (
    ...     set_base_config_type,
    ...     LazyDataclassFactory,
    ...     config_context,
    ... )
    >>> from myapp.config import GlobalConfig
    >>> 
    >>> # Initialize framework
    >>> set_base_config_type(GlobalConfig)
    >>> 
    >>> # Create lazy dataclass
    >>> LazyStepConfig = LazyDataclassFactory.make_lazy_simple(StepConfig)
    >>> 
    >>> # Use with context
    >>> with config_context(pipeline_config):
    ...     step = LazyStepConfig()
    ...     # Fields resolve from pipeline_config context

Architecture:
    The framework uses a dual-axis resolution system:
    
    X-Axis (Context Hierarchy):
        Step context → Pipeline context → Global context → Static defaults
    
    Y-Axis (Sibling Inheritance):
        Fields within the same context inherit from sibling dataclasses
    
    This enables sophisticated configuration patterns where fields can inherit
    from both parent contexts and sibling configurations.

Modules:
    - lazy_factory: Lazy dataclass factory and decorator system
    - dual_axis_resolver: Dual-axis inheritance resolver
    - context_manager: Contextvars-based context management
    - placeholder: Placeholder text generation for UI
    - global_config: Thread-local global configuration storage
    - config: Framework configuration (pluggable types and behaviors)
"""

# Factory
from openhcs.config_framework.lazy_factory import (
    LazyDataclassFactory,
    auto_create_decorator,
    register_lazy_type_mapping,
    get_base_type_for_lazy,
    get_lazy_type_for_base,
    ensure_global_config_context,
    # Global config type checking
    GlobalConfigBase,
    GlobalConfigMeta,
    is_global_config_type,
    is_global_config_instance,
    # Raw-value-preserving utilities
    replace_raw,
)

# Resolver
from openhcs.config_framework.dual_axis_resolver import (
    resolve_field_inheritance,
    _has_concrete_field_override,
)

# Context
from openhcs.config_framework.context_manager import (
    config_context,
    get_current_temp_global,
    set_current_temp_global,
    clear_current_temp_global,
    merge_configs,
    extract_all_configs,
    get_base_global_config,
    # Context hierarchy utilities
    get_context_type_stack,
    get_normalized_stack,
    get_types_before_in_stack,
    is_ancestor_in_context,
    is_same_type_in_context,
    # Hierarchy registry (populated by form managers)
    register_hierarchy_relationship,
    unregister_hierarchy_relationship,
    get_ancestors_from_hierarchy,
    # Scope key utilities
    get_root_from_scope_key,
    is_scope_affected,
    # Context stack building (framework-agnostic)
    build_context_stack,
)

# Placeholder
from openhcs.config_framework.placeholder import LazyDefaultPlaceholderService

# Global config
from openhcs.config_framework.global_config import (
    set_current_global_config,
    get_current_global_config,
    set_global_config_for_editing,
)

# Configuration
from openhcs.config_framework.config import (
    set_base_config_type,
    get_base_config_type,
)

# Cache warming
from openhcs.config_framework.cache_warming import (
    prewarm_config_analysis_cache,
    prewarm_callable_analysis_cache,
)

# Live context resolver
from openhcs.config_framework.live_context_resolver import LiveContextResolver

# Token cache
from openhcs.config_framework.token_cache import TokenCache, SingleValueTokenCache, CacheKey

__all__ = [
    # Factory
    'LazyDataclassFactory',
    'auto_create_decorator',
    'register_lazy_type_mapping',
    'get_base_type_for_lazy',
    'get_lazy_type_for_base',
    'ensure_global_config_context',
    # Global config type checking
    'GlobalConfigBase',
    'GlobalConfigMeta',
    'is_global_config_type',
    'is_global_config_instance',
    # Resolver
    'resolve_field_inheritance',
    '_has_concrete_field_override',
    # Context
    'config_context',
    'get_current_temp_global',
    'set_current_temp_global',
    'clear_current_temp_global',
    'merge_configs',
    'extract_all_configs',
    'get_base_global_config',
    'get_context_type_stack',
    'get_root_from_scope_key',
    'is_scope_affected',
    'build_context_stack',
    # Placeholder
    'LazyDefaultPlaceholderService',
    # Global config
    'set_current_global_config',
    'get_current_global_config',
    'set_global_config_for_editing',
    # Configuration
    'set_base_config_type',
    'get_base_config_type',
    # Cache warming
    'prewarm_config_analysis_cache',
    'prewarm_callable_analysis_cache',
    # Live context resolver
    'LiveContextResolver',
    # Token cache
    'TokenCache',
    'SingleValueTokenCache',
    'CacheKey',
]

__version__ = '1.0.0'
__author__ = 'OpenHCS Team'
__description__ = 'Generic configuration framework for lazy dataclass resolution'

