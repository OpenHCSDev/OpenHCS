"""Performance optimization layer for parameter form operations.

This module provides caching and memoization for expensive operations in the
parameter form system, including:
- Type introspection and analysis
- Dataclass field analysis
- Lazy type lookups
- Form structure analysis

All caches use weak references where appropriate to avoid memory leaks and
implement proper invalidation strategies.
"""

import functools
import weakref
from typing import Dict, Type, Any, Optional, Tuple, Callable
from dataclasses import dataclass, is_dataclass, fields
import hashlib
import inspect


# ==================== TYPE ANALYSIS CACHE ====================

class TypeAnalysisCache:
    """Cache for expensive type introspection operations.
    
    Uses weak references to avoid keeping types alive unnecessarily.
    Thread-safe for read-heavy workloads (common in UI).
    """
    
    def __init__(self):
        # WeakKeyDictionary: keys are types, automatically cleaned up when type is GC'd
        self._dataclass_fields_cache: weakref.WeakKeyDictionary = weakref.WeakKeyDictionary()
        self._is_dataclass_cache: weakref.WeakKeyDictionary = weakref.WeakKeyDictionary()
        self._lazy_type_mapping: Dict[Type, Type] = {}  # Base type -> Lazy type
        self._base_type_mapping: Dict[Type, Type] = {}  # Lazy type -> Base type
    
    def get_dataclass_fields(self, dataclass_type: Type) -> Optional[Tuple]:
        """Get cached dataclass fields or compute and cache them.
        
        Returns tuple of field objects for hashability and immutability.
        """
        if not is_dataclass(dataclass_type):
            return None
            
        if dataclass_type not in self._dataclass_fields_cache:
            field_tuple = tuple(fields(dataclass_type))
            self._dataclass_fields_cache[dataclass_type] = field_tuple
            
        return self._dataclass_fields_cache[dataclass_type]
    
    def is_dataclass_cached(self, obj_or_type: Any) -> bool:
        """Cached version of is_dataclass check."""
        # For instances, check the type
        check_type = type(obj_or_type) if not inspect.isclass(obj_or_type) else obj_or_type
        
        if check_type not in self._is_dataclass_cache:
            result = is_dataclass(obj_or_type)
            self._is_dataclass_cache[check_type] = result
            
        return self._is_dataclass_cache[check_type]
    
    def register_lazy_type_pair(self, base_type: Type, lazy_type: Type):
        """Register a base type <-> lazy type mapping for fast lookup."""
        self._lazy_type_mapping[base_type] = lazy_type
        self._base_type_mapping[lazy_type] = base_type
    
    def get_lazy_type(self, base_type: Type) -> Optional[Type]:
        """Get the lazy version of a base type."""
        return self._lazy_type_mapping.get(base_type)
    
    def get_base_type(self, lazy_type: Type) -> Optional[Type]:
        """Get the base version of a lazy type."""
        return self._base_type_mapping.get(lazy_type)
    
    def clear(self):
        """Clear all caches. Use sparingly - only when type definitions change."""
        self._dataclass_fields_cache.clear()
        self._is_dataclass_cache.clear()
        self._lazy_type_mapping.clear()
        self._base_type_mapping.clear()


# Global singleton instance
_type_analysis_cache = TypeAnalysisCache()


def get_type_analysis_cache() -> TypeAnalysisCache:
    """Get the global type analysis cache instance."""
    return _type_analysis_cache


# ==================== PARAMETER ANALYSIS CACHE ====================

class ParameterAnalysisCache:
    """Cache for UnifiedParameterAnalyzer results.
    
    Caches the expensive parameter analysis operation that involves:
    - Signature inspection
    - Dataclass field extraction
    - Docstring parsing
    - Type annotation resolution
    """
    
    def __init__(self):
        # Cache key: (type_id, is_instance) -> analysis result
        # Use type id instead of type object to avoid keeping types alive
        self._analysis_cache: Dict[Tuple[int, bool], Dict] = {}
        # Track which type IDs are still alive
        self._type_refs: weakref.WeakValueDictionary = weakref.WeakValueDictionary()
    
    def get_cache_key(self, target: Any) -> Tuple[int, bool]:
        """Generate cache key for a target object or type."""
        if inspect.isclass(target):
            # For classes, use the class itself
            type_obj = target
            is_instance = False
        else:
            # For instances, use the instance's type
            type_obj = type(target)
            is_instance = True
        
        # Store weak reference to keep track of type lifetime
        type_id = id(type_obj)
        self._type_refs[type_id] = type_obj
        
        return (type_id, is_instance)
    
    def get(self, target: Any) -> Optional[Dict]:
        """Get cached analysis result for target."""
        cache_key = self.get_cache_key(target)
        return self._analysis_cache.get(cache_key)
    
    def set(self, target: Any, result: Dict):
        """Cache analysis result for target."""
        cache_key = self.get_cache_key(target)
        self._analysis_cache[cache_key] = result
    
    def clear(self):
        """Clear the analysis cache."""
        self._analysis_cache.clear()
        self._type_refs.clear()
    
    def cleanup_dead_refs(self):
        """Remove cache entries for types that have been garbage collected."""
        # Get all type IDs that are still alive
        alive_ids = set(self._type_refs.keys())
        
        # Remove cache entries for dead types
        dead_keys = [key for key in self._analysis_cache.keys() if key[0] not in alive_ids]
        for key in dead_keys:
            del self._analysis_cache[key]


# Global singleton instance
_parameter_analysis_cache = ParameterAnalysisCache()


def get_parameter_analysis_cache() -> ParameterAnalysisCache:
    """Get the global parameter analysis cache instance."""
    return _parameter_analysis_cache


# ==================== PLACEHOLDER RESOLUTION CACHE ====================

@dataclass(frozen=True)
class PlaceholderCacheKey:
    """Immutable cache key for placeholder resolution.
    
    Includes context hash to invalidate when context changes.
    """
    dataclass_type_id: int  # id(dataclass_type)
    field_name: str
    context_hash: str  # Hash of current context state
    
    @staticmethod
    def from_context(dataclass_type: Type, field_name: str, context_obj: Any = None) -> 'PlaceholderCacheKey':
        """Create cache key from current context."""
        type_id = id(dataclass_type)
        
        # Hash the context object to detect changes
        # For None context, use empty string
        if context_obj is None:
            context_hash = ""
        else:
            # Create a stable hash from context object's relevant fields
            # Use repr for simplicity - could be optimized further
            try:
                context_str = repr(context_obj)
                context_hash = hashlib.md5(context_str.encode()).hexdigest()[:16]
            except Exception:
                # If repr fails, use object id (less cache hits but safe)
                context_hash = str(id(context_obj))
        
        return PlaceholderCacheKey(type_id, field_name, context_hash)


class PlaceholderResolutionCache:
    """Cache for placeholder text resolution results.
    
    This is the most frequently called operation during form updates,
    so caching provides significant performance benefits.
    
    Cache invalidation strategy:
    - Context changes invalidate via context_hash in key
    - Type changes invalidate via weak references
    - Manual clear() for explicit invalidation
    """
    
    def __init__(self):
        self._cache: Dict[PlaceholderCacheKey, Optional[str]] = {}
        self._type_refs: weakref.WeakValueDictionary = weakref.WeakValueDictionary()
        self._hit_count = 0
        self._miss_count = 0
    
    def get(self, dataclass_type: Type, field_name: str, context_obj: Any = None) -> Optional[str]:
        """Get cached placeholder text or None if not cached."""
        # Track type reference
        type_id = id(dataclass_type)
        self._type_refs[type_id] = dataclass_type
        
        cache_key = PlaceholderCacheKey.from_context(dataclass_type, field_name, context_obj)
        
        if cache_key in self._cache:
            self._hit_count += 1
            return self._cache[cache_key]
        
        self._miss_count += 1
        return None
    
    def set(self, dataclass_type: Type, field_name: str, context_obj: Any, result: Optional[str]):
        """Cache placeholder text result."""
        cache_key = PlaceholderCacheKey.from_context(dataclass_type, field_name, context_obj)
        self._cache[cache_key] = result
    
    def clear(self):
        """Clear all cached placeholder results."""
        self._cache.clear()
        self._hit_count = 0
        self._miss_count = 0
    
    def get_stats(self) -> Dict[str, int]:
        """Get cache statistics for performance monitoring."""
        total = self._hit_count + self._miss_count
        hit_rate = (self._hit_count / total * 100) if total > 0 else 0
        
        return {
            'hits': self._hit_count,
            'misses': self._miss_count,
            'total_requests': total,
            'hit_rate_percent': hit_rate,
            'cache_size': len(self._cache)
        }
    
    def cleanup_dead_refs(self):
        """Remove cache entries for types that have been garbage collected."""
        alive_ids = set(self._type_refs.keys())
        dead_keys = [key for key in self._cache.keys() if key.dataclass_type_id not in alive_ids]
        for key in dead_keys:
            del self._cache[key]


# Global singleton instance
_placeholder_resolution_cache = PlaceholderResolutionCache()


def get_placeholder_resolution_cache() -> PlaceholderResolutionCache:
    """Get the global placeholder resolution cache instance."""
    return _placeholder_resolution_cache


# ==================== FORM STRUCTURE CACHE ====================

def cached_form_structure_analysis(func: Callable) -> Callable:
    """Decorator to cache form structure analysis results.
    
    Uses functools.lru_cache with a reasonable size limit.
    Cache key is based on the dataclass type.
    """
    @functools.lru_cache(maxsize=128)
    def _cached_wrapper(dataclass_type: Type):
        return func(dataclass_type)
    
    @functools.wraps(func)
    def wrapper(dataclass_type: Type):
        # Only cache for types, not instances
        if inspect.isclass(dataclass_type):
            return _cached_wrapper(dataclass_type)
        else:
            # For instances, use the type
            return _cached_wrapper(type(dataclass_type))
    
    # Expose cache_clear for manual invalidation
    wrapper.cache_clear = _cached_wrapper.cache_clear
    wrapper.cache_info = _cached_wrapper.cache_info
    
    return wrapper

