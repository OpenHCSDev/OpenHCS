"""
Central Context Stack Registry - Single Source of Truth for Resolved Config Values.

This service eliminates the architectural smell where forms build their own context
stacks internally. Instead, the registry maintains context stacks for all scopes and
serves as the single source of truth for resolved values.

Architecture:
- Singleton service managing all resolved configuration values
- Immutability pattern: stores concrete values separately, never mutates context_obj
- Materialization API: creates new instances with resolved values applied
- Signal-based reactivity: emits value_changed when resolved values change
- Lazy resolution: creates fresh lazy instances within context for proper inheritance

Usage:
    registry = ContextStackRegistry.instance()

    # Register scope
    registry.register_scope(scope_id, context_obj, dataclass_type)

    # Live edits (immutable) - from forms with nested types
    registry.set(scope_id, field_name, value, dataclass_type)

    # Read resolved value (for forms with nested types)
    resolved = registry.resolve(scope_id, dataclass_type, field_name)

    # Read resolved value (for preview labels using stored type)
    resolved = registry.resolve(scope_id, field_name=field_name)

    # Materialize for compilation
    materialized = registry.get_materialized_object(scope_id)
"""

from typing import Any, Dict, Optional, Set
from dataclasses import fields, is_dataclass
import logging
from contextlib import ExitStack

from PyQt6.QtCore import QObject, pyqtSignal

from openhcs.config_framework.context_manager import (
    build_context_stack,
    config_context,
    get_root_from_scope_key,
)
from openhcs.config_framework.lazy_factory import get_base_type_for_lazy

logger = logging.getLogger(__name__)


class ContextStackRegistry(QObject):
    """Central registry for context stacks and resolved configuration values.
    
    Maintains single source of truth for all resolved config values across the application.
    Forms write to registry, UI reads from registry, no duplicate resolution paths.
    """
    
    # Signal: (scope_id, field_path, old_value, new_value)
    value_changed = pyqtSignal(str, str, object, object)
    
    _instance: Optional['ContextStackRegistry'] = None
    
    def __init__(self):
        super().__init__()
        
        # Registered scopes: scope_id -> (context_obj, dataclass_type)
        self._scopes: Dict[str, tuple[Any, type]] = {}
        
        # Concrete value overrides: scope_id -> {field_path: value}
        self._concrete_values: Dict[str, Dict[str, Any]] = {}
        
        # Resolved value cache: scope_id -> {field_path: value}
        self._resolved_cache: Dict[str, Dict[str, Any]] = {}
        
        # LiveContextService token tracking for cache invalidation
        self._last_live_context_token: int = 0
    
    @classmethod
    def instance(cls) -> 'ContextStackRegistry':
        """Get singleton instance."""
        if cls._instance is None:
            cls._instance = cls()
        return cls._instance
    
    @classmethod
    def reset_instance(cls) -> None:
        """Reset singleton (for testing)."""
        cls._instance = None
    
    def register_scope(self, scope_id: str, context_obj: Any, dataclass_type: type) -> None:
        """Register a scope for resolution.
        
        If scope_id already exists, REPLACES context_obj and clears concrete values (code mode).
        
        Args:
            scope_id: Unique scope identifier (plate path or plate::step_token)
            context_obj: The object being edited (step, pipeline_config, etc.)
            dataclass_type: The dataclass type being edited
        """
        is_replacement = scope_id in self._scopes
        
        self._scopes[scope_id] = (context_obj, dataclass_type)
        
        if is_replacement:
            # Code mode replacement - clear concrete values and cache
            self._concrete_values[scope_id] = {}
            self._resolved_cache[scope_id] = {}
            logger.info(f"📦 REPLACED scope: {scope_id} (code mode)")
        else:
            # New registration
            self._concrete_values[scope_id] = {}
            self._resolved_cache[scope_id] = {}
            logger.info(f"📦 REGISTERED scope: {scope_id}")
    
    def unregister_scope(self, scope_id: str) -> None:
        """Unregister scope. Called when form closes or item deleted."""
        self._scopes.pop(scope_id, None)
        self._concrete_values.pop(scope_id, None)
        self._resolved_cache.pop(scope_id, None)
        logger.info(f"📦 UNREGISTERED scope: {scope_id}")
    
    def set(
        self, scope_id: str, field_name: str, value: Any, dataclass_type: Optional[type] = None
    ) -> None:
        """Set a concrete value override. Does NOT mutate context_obj (immutable).

        Emits value_changed if resolved value changes.

        Args:
            scope_id: Scope identifier
            field_name: Field name (e.g., "well_filter")
            value: New value to set
            dataclass_type: The dataclass type for this field. If None, uses stored root type.
        """
        if scope_id not in self._scopes:
            logger.warning(f"Cannot set value for unregistered scope: {scope_id}")
            return

        _, stored_dataclass_type = self._scopes[scope_id]
        if dataclass_type is None:
            dataclass_type = stored_dataclass_type

        # Build cache key matching resolve()
        cache_key = f"{dataclass_type.__name__}.{field_name}"

        # Get old resolved value before change
        old_value = self.resolve(scope_id, dataclass_type, field_name)

        # Store concrete value with cache_key (immutable - don't mutate context_obj)
        self._concrete_values[scope_id][cache_key] = value

        # Invalidate cache for this scope and descendants
        self._invalidate_cache(scope_id, cache_key)

        # Get new resolved value after change
        new_value = self.resolve(scope_id, dataclass_type, field_name)
        
        # Emit signal if resolved value actually changed
        if old_value != new_value:
            logger.info(f"⚡ VALUE CHANGED: {scope_id}.{field_path}: {old_value} -> {new_value}")
            self.value_changed.emit(scope_id, field_path, old_value, new_value)

    def resolve(
        self, scope_id: str, dataclass_type: Optional[type] = None, field_name: Optional[str] = None
    ) -> Any:
        """Resolve field value through context hierarchy using lazy dataclass resolution.

        Resolution order:
        1. Check concrete values (live edits)
        2. Check cache
        3. Build context stack and resolve via fresh lazy instance

        Args:
            scope_id: Scope identifier
            dataclass_type: The dataclass type to resolve for. If None, uses stored root type.
            field_name: Name of the field to resolve (e.g., "well_filter")

        Returns:
            Resolved value (raw, not formatted as placeholder text)
        """
        if scope_id not in self._scopes:
            logger.warning(f"Cannot resolve for unregistered scope: {scope_id}")
            return None

        context_obj, stored_dataclass_type = self._scopes[scope_id]

        # Use stored type if not provided
        if dataclass_type is None:
            dataclass_type = stored_dataclass_type

        if field_name is None:
            logger.warning(f"resolve() called without field_name for {scope_id}")
            return None

        # Cache key combines type and field for proper namespacing
        cache_key = f"{dataclass_type.__name__}.{field_name}"
        logger.debug(f"🔍 Resolving {scope_id}.{cache_key}")

        # Check concrete values first (live edits)
        if cache_key in self._concrete_values.get(scope_id, {}):
            value = self._concrete_values[scope_id][cache_key]
            logger.debug(f"  ✅ Found in concrete values: {repr(value)[:50]}")
            return value

        # Check cache
        if cache_key in self._resolved_cache.get(scope_id, {}):
            value = self._resolved_cache[scope_id][cache_key]
            logger.debug(f"  ✅ Found in cache: {repr(value)[:50]}")
            return value

        # Build live context from all registered scopes
        live_context = self._build_live_context(scope_id)

        # Get lazy version of the dataclass type for resolution
        from openhcs.config_framework.placeholder import LazyDefaultPlaceholderService
        lazy_type = dataclass_type
        if not LazyDefaultPlaceholderService.has_lazy_resolution(dataclass_type):
            lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(dataclass_type)
            if not lazy_type:
                lazy_type = dataclass_type  # Fall back to original

        # Build context stack
        stack = build_context_stack(
            context_obj=context_obj,
            overlay=self._concrete_values.get(scope_id, {}),
            dataclass_type=lazy_type,
            live_context=live_context,
        )

        # Resolve by creating fresh lazy instance within context
        # This is the same approach used by get_lazy_resolved_placeholder()
        with stack:
            try:
                instance = lazy_type()
                resolved_value = getattr(instance, field_name)
                logger.debug(f"  ✅ Resolved via lazy instance: {repr(resolved_value)[:50]}")
            except Exception as e:
                logger.debug(f"  ⚠️ Failed to resolve: {e}")
                resolved_value = None

        # Cache result
        self._resolved_cache[scope_id][cache_key] = resolved_value

        return resolved_value

    def get_materialized_object(self, scope_id: str) -> Any:
        """Get context_obj with all resolved values applied. Returns NEW instance.

        This is used for compilation and code generation - creates a concrete instance
        with all lazy fields resolved and concrete values applied.

        Args:
            scope_id: Scope identifier

        Returns:
            New instance with resolved values applied
        """
        if scope_id not in self._scopes:
            logger.warning(f"Cannot materialize unregistered scope: {scope_id}")
            return None

        context_obj, dataclass_type = self._scopes[scope_id]

        # Resolve all fields using the new resolution API
        materialized_kwargs = {}

        if is_dataclass(context_obj):
            for field in fields(context_obj):
                field_name = field.name
                # Use resolve() which properly handles lazy dataclass resolution
                resolved_value = self.resolve(scope_id, dataclass_type, field_name)
                materialized_kwargs[field_name] = resolved_value

        # Create new instance
        try:
            return dataclass_type(**materialized_kwargs)
        except Exception as e:
            logger.error(f"Failed to materialize {scope_id}: {e}")
            return context_obj  # Fallback to original

    def get_resolved_state(self, scope_id: str) -> Dict[str, Any]:
        """Get complete resolved state for dirty tracking.

        Returns dict of all field paths to their resolved values.

        Args:
            scope_id: Scope identifier

        Returns:
            Dict mapping field_path -> resolved_value
        """
        if scope_id not in self._scopes:
            return {}

        context_obj, dataclass_type = self._scopes[scope_id]
        resolved_state = {}

        # Get all field paths and resolve each
        if is_dataclass(context_obj):
            for field in fields(context_obj):
                field_name = field.name
                resolved_state[field_name] = self.resolve(scope_id, dataclass_type, field_name)

        return resolved_state

    def _build_live_context(self, scope_id: str) -> Dict[type, Dict[str, Any]]:
        """Build live context dict from all registered scopes.

        This replaces LiveContextService.collect() for registry-based resolution.

        Args:
            scope_id: Current scope being resolved

        Returns:
            Dict mapping dataclass_type -> field_values
        """
        live_context = {}

        for other_scope_id, (other_obj, other_type) in self._scopes.items():
            if other_scope_id == scope_id:
                continue  # Skip self

            # Get base type for lazy dataclasses
            base_type = get_base_type_for_lazy(other_type)

            # Merge concrete values with object's fields
            field_values = {}

            if is_dataclass(other_obj):
                for field in fields(other_obj):
                    field_name = field.name
                    # Prefer concrete values over object's values
                    if field_name in self._concrete_values.get(other_scope_id, {}):
                        field_values[field_name] = self._concrete_values[other_scope_id][field_name]
                    else:
                        field_values[field_name] = getattr(other_obj, field_name, None)

            live_context[base_type] = field_values

        return live_context

    def _invalidate_cache(self, scope_id: str, field_path: str) -> None:
        """Invalidate resolved cache for scope and all visible descendants.

        When a value changes, we need to invalidate cache for:
        1. The scope itself
        2. All scopes where this scope is visible (descendants)

        Args:
            scope_id: Scope that changed
            field_path: Field that changed
        """
        # Invalidate self
        self._resolved_cache[scope_id] = {}

        # Invalidate all scopes where this scope is visible
        editing_root = get_root_from_scope_key(scope_id)

        for other_scope_id in self._scopes.keys():
            if other_scope_id == scope_id:
                continue

            # Check if editing_scope_id is visible to other_scope_id
            if self._is_scope_visible(scope_id, other_scope_id):
                self._resolved_cache[other_scope_id] = {}

    def _is_scope_visible(self, editing_scope_id: Optional[str], target_scope_id: Optional[str]) -> bool:
        """Check if edits from editing_scope_id should affect target_scope_id.

        Uses same visibility rules as ParameterFormManager and ResolvedItemStateService.

        Args:
            editing_scope_id: Scope where edit happened
            target_scope_id: Scope to check visibility for

        Returns:
            True if editing_scope affects target_scope
        """
        # Guard against None scope IDs
        if editing_scope_id is None or target_scope_id is None:
            return False

        # Global config edits affect everything
        if 'Global' in editing_scope_id:
            return True

        # Same scope
        if editing_scope_id == target_scope_id:
            return True

        # Same root (same plate)
        editing_root = get_root_from_scope_key(editing_scope_id)
        target_root = get_root_from_scope_key(target_scope_id)

        if editing_root and target_root:
            return editing_root == target_root

        return False

    def clear_all(self) -> None:
        """Clear all state. Called on pipeline close/reset."""
        self._scopes.clear()
        self._concrete_values.clear()
        self._resolved_cache.clear()
        logger.info("Cleared all registry state")

