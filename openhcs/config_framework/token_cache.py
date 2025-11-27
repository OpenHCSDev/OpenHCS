"""
Token-based cache invalidation service.

Provides a reusable abstraction for caching values that should be invalidated
when a global token changes (e.g., when any form value changes).
"""

from typing import TypeVar, Generic, Optional, Callable, Tuple, Any, Dict
from dataclasses import dataclass

T = TypeVar('T')


@dataclass(frozen=True)
class CacheKey:
    """Immutable cache key that can include multiple components."""
    components: Tuple[Any, ...]
    
    def __hash__(self):
        return hash(self.components)
    
    def __eq__(self, other):
        if not isinstance(other, CacheKey):
            return False
        return self.components == other.components
    
    @classmethod
    def from_args(cls, *args) -> 'CacheKey':
        """Create cache key from variable arguments."""
        return cls(components=args)


class TokenCache(Generic[T]):
    """
    Generic token-based cache with automatic invalidation.
    
    The cache is invalidated when the token changes. This is useful for caching
    values that depend on global state (e.g., form values) that can change.
    
    Example:
        # Create cache with token provider
        cache = TokenCache(lambda: ParameterFormManager._live_context_token_counter)
        
        # Get or compute value
        value = cache.get_or_compute(
            key=CacheKey.from_args('scope', 'param_name'),
            compute_fn=lambda: expensive_computation()
        )
        
        # Cache is automatically invalidated when token changes
    """
    
    def __init__(self, token_provider: Callable[[], int]):
        """
        Initialize token cache.
        
        Args:
            token_provider: Function that returns the current token value
        """
        self._token_provider = token_provider
        self._cache: Dict[CacheKey, T] = {}
        self._last_token: int = -1
    
    def get_or_compute(self, key: CacheKey, compute_fn: Callable[[], T]) -> T:
        """
        Get cached value or compute and cache it.
        
        Args:
            key: Cache key
            compute_fn: Function to compute value if cache miss
            
        Returns:
            Cached or computed value
        """
        current_token = self._token_provider()
        
        # Invalidate entire cache if token changed
        if current_token != self._last_token:
            self._cache.clear()
            self._last_token = current_token
        
        # Check cache
        if key in self._cache:
            return self._cache[key]
        
        # Compute and cache
        value = compute_fn()
        self._cache[key] = value
        return value
    
    def invalidate(self):
        """Manually invalidate the entire cache."""
        self._cache.clear()
        self._last_token = -1
    
    def get(self, key: CacheKey) -> Optional[T]:
        """
        Get cached value without computing.
        
        Args:
            key: Cache key
            
        Returns:
            Cached value or None if not found or token changed
        """
        current_token = self._token_provider()
        
        # Invalidate if token changed
        if current_token != self._last_token:
            self._cache.clear()
            self._last_token = current_token
            return None
        
        return self._cache.get(key)
    
    def put(self, key: CacheKey, value: T):
        """
        Put value in cache.
        
        Args:
            key: Cache key
            value: Value to cache
        """
        current_token = self._token_provider()
        
        # Update token if changed
        if current_token != self._last_token:
            self._cache.clear()
            self._last_token = current_token
        
        self._cache[key] = value


class SingleValueTokenCache(Generic[T]):
    """
    Simplified token cache for single values (no key needed).
    
    Useful when you only need to cache one value that depends on a token.
    
    Example:
        cache = SingleValueTokenCache(lambda: token_counter)
        value = cache.get_or_compute(lambda: expensive_computation())
    """
    
    def __init__(self, token_provider: Callable[[], int]):
        """
        Initialize single-value token cache.
        
        Args:
            token_provider: Function that returns the current token value
        """
        self._token_provider = token_provider
        self._cached_value: Optional[T] = None
        self._cached_token: int = -1
    
    def get_or_compute(self, compute_fn: Callable[[], T]) -> T:
        """
        Get cached value or compute and cache it.
        
        Args:
            compute_fn: Function to compute value if cache miss
            
        Returns:
            Cached or computed value
        """
        current_token = self._token_provider()
        
        # Check cache
        if current_token == self._cached_token and self._cached_value is not None:
            return self._cached_value
        
        # Compute and cache
        value = compute_fn()
        self._cached_value = value
        self._cached_token = current_token
        return value
    
    def invalidate(self):
        """Manually invalidate the cache."""
        self._cached_value = None
        self._cached_token = -1

