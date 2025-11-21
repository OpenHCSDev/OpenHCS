"""
Utilities for working with lazy dataclasses.

Provides introspection and patching utilities for lazy dataclass types,
including automatic discovery and constructor patching for code execution.
"""

import dataclasses
import inspect
import logging
from contextlib import contextmanager
from typing import Dict, List, Type

logger = logging.getLogger(__name__)


def discover_lazy_dataclass_types() -> List[Type]:
    """
    Automatically discover all lazy dataclass types from openhcs.core.config.
    
    Uses introspection to find all classes that have lazy resolution methods,
    preventing hardcoding and ensuring all lazy types are discovered.
    
    Returns:
        List of lazy dataclass types that have lazy resolution capabilities
    """
    from openhcs.config_framework.placeholder import LazyDefaultPlaceholderService
    import openhcs.core.config as config_module
    
    lazy_types = []
    for name, obj in inspect.getmembers(config_module):
        # Check if it's a class and has lazy resolution
        if inspect.isclass(obj) and LazyDefaultPlaceholderService.has_lazy_resolution(obj):
            lazy_types.append(obj)
            logger.debug(f"Discovered lazy type: {name}")
    
    return lazy_types


@contextmanager
def patch_lazy_constructors():
    """
    Context manager that patches lazy dataclass constructors to preserve None vs concrete distinction.

    This is critical for code editors that use exec() to create dataclass instances.
    Without patching, lazy dataclasses would resolve None values to concrete defaults
    during construction, making it impossible to distinguish between explicitly set
    values and inherited values.

    The patched constructor only sets fields that are explicitly provided in kwargs,
    leaving all other fields as None. This preserves the None vs concrete distinction
    needed for proper hierarchical inheritance.

    Usage:
        with patch_lazy_constructors():
            exec(code_string, namespace)
            # Lazy dataclasses created during exec() will preserve None values

    Example:
        # Without patching:
        LazyZarrConfig(compression='gzip')  # All unspecified fields resolve to defaults

        # With patching:
        with patch_lazy_constructors():
            LazyZarrConfig(compression='gzip')  # Only compression is set, rest are None
    """
    import logging
    logger = logging.getLogger(__name__)
    logger.info("🔧 patch_lazy_constructors: ENTERING")

    # Store original constructors
    original_constructors: Dict[Type, callable] = {}

    # Discover all lazy dataclass types automatically
    lazy_types = discover_lazy_dataclass_types()
    logger.info(f"🔧 patch_lazy_constructors: Discovered {len(lazy_types)} lazy types")
    
    # Patch all discovered lazy types
    for lazy_type in lazy_types:
        # Store original constructor
        original_constructors[lazy_type] = lazy_type.__init__
        logger.info(f"🔧 patch_lazy_constructors: Patching {lazy_type.__name__} (id={id(lazy_type)})")

        # Create patched constructor that uses raw values
        def create_patched_init(original_init, dataclass_type):
            def patched_init(self, **kwargs):
                import logging
                logger = logging.getLogger(__name__)
                logger.info(f"🔧 PATCHED {dataclass_type.__name__}.__init__: kwargs={kwargs}")

                # CRITICAL: Set tracking attributes FIRST (before setting field values)
                # This is required for lazy resolution to work correctly
                object.__setattr__(self, '_explicitly_set_fields', set(kwargs.keys()))

                # Check if this is a lazy dataclass with global config type
                # (created by @global_pipeline_config decorator)
                if hasattr(original_init, '__self__'):
                    # Bound method - extract class
                    cls = original_init.__self__.__class__
                elif hasattr(original_init, '__func__'):
                    # Unbound method
                    cls = dataclass_type
                else:
                    cls = dataclass_type

                # Try to extract global_config_type from the original init's closure or class
                global_config_type = None
                if hasattr(original_init, '__code__') and hasattr(original_init, '__closure__'):
                    # Check closure variables for global_config_type
                    if original_init.__closure__:
                        for cell in original_init.__closure__:
                            try:
                                val = cell.cell_contents
                                if isinstance(val, type) and hasattr(val, '__dataclass_fields__'):
                                    global_config_type = val
                                    break
                            except (ValueError, AttributeError):
                                pass

                if global_config_type:
                    object.__setattr__(self, '_global_config_type', global_config_type)

                # Compute config field name from dataclass type name
                import re
                def _camel_to_snake_local(name: str) -> str:
                    s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
                    return re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()

                # Remove "Lazy" prefix if present
                type_name = dataclass_type.__name__
                if type_name.startswith('Lazy'):
                    type_name = type_name[4:]  # Remove "Lazy" prefix
                config_field_name = _camel_to_snake_local(type_name)
                object.__setattr__(self, '_config_field_name', config_field_name)

                # Use raw value approach instead of calling original constructor
                # This prevents lazy resolution during code execution
                for field in dataclasses.fields(dataclass_type):
                    value = kwargs.get(field.name, None)
                    object.__setattr__(self, field.name, value)

                # Initialize any required lazy dataclass attributes
                if hasattr(dataclass_type, '_is_lazy_dataclass'):
                    object.__setattr__(self, '_is_lazy_dataclass', True)

            return patched_init
        
        # Apply the patch
        lazy_type.__init__ = create_patched_init(original_constructors[lazy_type], lazy_type)
    
    try:
        logger.info("🔧 patch_lazy_constructors: YIELDING (patch active)")
        yield
    finally:
        logger.info("🔧 patch_lazy_constructors: EXITING (restoring original constructors)")
        # Restore original constructors
        for lazy_type, original_init in original_constructors.items():
            lazy_type.__init__ = original_init

