"""
Generic cache warming for configuration analysis.

This module provides a generic function to pre-warm analysis caches for any
configuration hierarchy, eliminating first-load penalties in UI forms.
"""

import dataclasses
import logging
from typing import Type, Set, Optional, get_args, get_origin, Callable

from openhcs.introspection.signature_analyzer import SignatureAnalyzer
from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer
from openhcs.ui.shared.parameter_form_service import ParameterFormService

logger = logging.getLogger(__name__)


def _extract_all_dataclass_types(base_type: Type, visited: Optional[Set[Type]] = None) -> Set[Type]:
    """
    Recursively extract all dataclass types from a configuration hierarchy.
    
    Uses type introspection to discover all nested dataclass fields automatically.
    This is fully generic and works for any dataclass hierarchy.
    
    Args:
        base_type: Root dataclass type to analyze
        visited: Set of already-visited types (for cycle detection)
    
    Returns:
        Set of all dataclass types found in the hierarchy
    """
    if visited is None:
        visited = set()
    
    # Avoid infinite recursion on circular references
    if base_type in visited:
        return visited
    
    # Only process dataclasses
    if not dataclasses.is_dataclass(base_type):
        return visited
    
    visited.add(base_type)
    
    # Introspect all fields to find nested dataclasses
    for field in dataclasses.fields(base_type):
        field_type = field.type
        
        # Handle Optional[T] -> extract T
        origin = get_origin(field_type)
        if origin is not None:
            # For Union types (including Optional), check all args
            args = get_args(field_type)
            for arg in args:
                if arg is type(None):
                    continue
                if dataclasses.is_dataclass(arg):
                    _extract_all_dataclass_types(arg, visited)
        elif dataclasses.is_dataclass(field_type):
            # Direct dataclass field
            _extract_all_dataclass_types(field_type, visited)
    
    return visited


def prewarm_callable_analysis_cache(*callables: Callable) -> None:
    """
    Pre-warm analysis caches for callable signatures (functions, methods, constructors).

    This is useful for warming caches for step editors, function pattern editors, etc.
    that analyze function signatures rather than dataclass hierarchies.

    Args:
        *callables: One or more callables to analyze (functions, methods, __init__, etc.)

    Example:
        >>> from openhcs.core.steps.abstract import AbstractStep
        >>> from openhcs.config_framework import prewarm_callable_analysis_cache
        >>> prewarm_callable_analysis_cache(AbstractStep.__init__)
    """
    for callable_obj in callables:
        SignatureAnalyzer.analyze(callable_obj)
        UnifiedParameterAnalyzer.analyze(callable_obj)

    logger.debug(f"Pre-warmed analysis cache for {len(callables)} callables")


def prewarm_config_analysis_cache(base_config_type: Type) -> None:
    """
    Pre-warm analysis caches for all config types in a hierarchy.

    This is a fully generic function that:
    1. Uses type introspection to discover all dataclass types in the hierarchy
    2. Pre-analyzes each type to populate analysis caches
    3. Also analyzes the lazy version of the base config (if it exists)
    4. Eliminates 1000ms+ first-load penalty when opening config windows

    After this runs, first load is as fast as second load (~170ms instead of ~1000ms).

    Args:
        base_config_type: Root configuration type (e.g., GlobalPipelineConfig)

    Example:
        >>> from myapp.config import GlobalConfig
        >>> from openhcs.config_framework import prewarm_config_analysis_cache
        >>> prewarm_config_analysis_cache(GlobalConfig)
    """
    # Discover all dataclass types in the hierarchy using introspection
    config_types = _extract_all_dataclass_types(base_config_type)

    # Also add the lazy version of the base config if it exists
    # (e.g., GlobalPipelineConfig -> PipelineConfig)
    lazy_name = base_config_type.__name__.replace("Global", "")
    if lazy_name != base_config_type.__name__:
        import importlib
        module = importlib.import_module(base_config_type.__module__)
        lazy_type = getattr(module, lazy_name, None)

        if lazy_type is not None and dataclasses.is_dataclass(lazy_type):
            config_types.add(lazy_type)

    # Create a single service instance to warm the class-level cache
    service = ParameterFormService()

    # Pre-analyze all config types to populate caches
    for config_type in config_types:
        # Warm SignatureAnalyzer cache (dataclass field analysis)
        SignatureAnalyzer._analyze_dataclass(config_type)

        # Warm UnifiedParameterAnalyzer cache (parameter info with descriptions)
        param_info = UnifiedParameterAnalyzer.analyze(config_type)

        # Warm ParameterFormService cache (form structure analysis)
        # This is the expensive part that builds the recursive FormStructure
        if dataclasses.is_dataclass(config_type):
            # Extract parameters from the dataclass
            params = {}
            param_types = {}
            for field in dataclasses.fields(config_type):
                params[field.name] = None  # Dummy value
                param_types[field.name] = field.type

            # Analyze to warm the cache
            service.analyze_parameters(
                params, param_types,
                field_id='cache_warming',
                parameter_info=param_info,
                parent_dataclass_type=config_type
            )

    logger.debug(f"Pre-warmed analysis cache for {len(config_types)} config types")

