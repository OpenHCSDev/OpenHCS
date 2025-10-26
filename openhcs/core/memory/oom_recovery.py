"""
GPU Out of Memory (OOM) recovery utilities.

Provides comprehensive OOM detection and cache clearing for all supported
GPU frameworks in OpenHCS.

REFACTORED: Uses enum-driven metaprogramming to eliminate 71% of code duplication.
All OOM patterns and cache clearing operations are defined in framework_ops.py.
"""

import gc
import logging
from typing import Optional

from openhcs.constants.constants import MemoryType
from openhcs.core.memory.framework_ops import _FRAMEWORK_OPS
from openhcs.core.utils import optional_import

logger = logging.getLogger(__name__)


def _is_oom_error(e: Exception, memory_type: str) -> bool:
    """
    Detect Out of Memory errors for all GPU frameworks.

    Auto-generated from framework_ops.py OOM patterns.

    Args:
        e: Exception to check
        memory_type: Memory type string (e.g., 'torch', 'cupy')

    Returns:
        True if exception is an OOM error for the given framework
    """
    # Find the MemoryType enum for this memory_type string
    mem_type_enum = None
    for mt in MemoryType:
        if mt.value == memory_type:
            mem_type_enum = mt
            break

    if mem_type_enum is None:
        return False

    ops = _FRAMEWORK_OPS[mem_type_enum]
    error_str = str(e).lower()

    # Check framework-specific exception types
    for exc_type_expr in ops['oom_exception_types']:
        try:
            # Import the module and get the exception type
            mod_name = ops['import_name']
            mod = optional_import(mod_name)
            if mod is None:
                continue

            # Evaluate the exception type expression
            exc_type_str = exc_type_expr.format(mod='mod')
            # Extract the attribute path (e.g., 'mod.cuda.OutOfMemoryError' -> ['cuda', 'OutOfMemoryError'])
            parts = exc_type_str.split('.')[1:]  # Skip 'mod'
            exc_type = mod
            for part in parts:
                if hasattr(exc_type, part):
                    exc_type = getattr(exc_type, part)
                else:
                    exc_type = None
                    break

            if exc_type is not None and isinstance(e, exc_type):
                return True
        except Exception:
            continue

    # String-based detection using framework-specific patterns
    return any(pattern in error_str for pattern in ops['oom_string_patterns'])


def _clear_cache_for_memory_type(memory_type: str, device_id: Optional[int] = None):
    """
    Clear GPU cache for specific memory type.

    Auto-generated from framework_ops.py cache clearing operations.

    Args:
        memory_type: Memory type string (e.g., 'torch', 'cupy')
        device_id: GPU device ID (optional, currently unused but kept for API compatibility)
    """
    # Find the MemoryType enum for this memory_type string
    mem_type_enum = None
    for mt in MemoryType:
        if mt.value == memory_type:
            mem_type_enum = mt
            break

    if mem_type_enum is None:
        logger.warning(f"Unknown memory type for cache clearing: {memory_type}")
        gc.collect()
        return

    ops = _FRAMEWORK_OPS[mem_type_enum]

    # Get the module
    mod_name = ops['import_name']
    mod = optional_import(mod_name)

    if mod is None:
        logger.warning(f"Module {mod_name} not available for cache clearing")
        gc.collect()
        return

    # Execute cache clearing operations
    cache_clear_expr = ops['oom_clear_cache']
    if cache_clear_expr:
        try:
            # Execute cache clear directly (device context handled by the operations themselves)
            exec(cache_clear_expr.format(mod=mod_name), {mod_name: mod, 'gc': gc})
        except Exception as e:
            logger.warning(f"Failed to clear cache for {memory_type}: {e}")

    # Always trigger Python garbage collection
    gc.collect()


def _execute_with_oom_recovery(func_callable, memory_type: str, max_retries: int = 2):
    """
    Execute function with automatic OOM recovery.
    
    Args:
        func_callable: Function to execute
        memory_type: Memory type from MemoryType enum
        max_retries: Maximum number of retry attempts
        
    Returns:
        Function result
        
    Raises:
        Original exception if not OOM or retries exhausted
    """
    for attempt in range(max_retries + 1):
        try:
            return func_callable()
        except Exception as e:
            if not _is_oom_error(e, memory_type) or attempt == max_retries:
                raise
                
            # Clear cache and retry
            _clear_cache_for_memory_type(memory_type)
