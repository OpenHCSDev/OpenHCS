"""
Live context resolution service for configuration framework.

Provides cached resolution of config attributes using live values,
avoiding redundant context building and resolution operations.

This service is completely generic and UI-agnostic:
- No knowledge of ParameterFormManager or any UI components
- No knowledge of steps, orchestrators, or domain concepts
- Only knows about dataclasses, context stacks, and attribute resolution
- Caller is responsible for providing live context data
"""

from typing import Any, Dict, Type, Optional, Tuple
from dataclasses import is_dataclass, replace as dataclass_replace
from openhcs.config_framework.context_manager import config_context
import logging
import contextvars

logger = logging.getLogger(__name__)

# Import the cache disable flag from lazy_factory
from openhcs.config_framework.lazy_factory import _disable_lazy_cache


class LiveContextResolver:
    """
    Pure service for resolving config attributes with live values.

    Caches resolved config values to avoid expensive context stack building + resolution.
    Token-based invalidation ensures cache coherency.

    Completely generic - works with any dataclasses and any context hierarchy.
    UI layer is responsible for:
    - Collecting live context from form managers
    - Providing the current token
    - Building the context stack
    """

    def __init__(self):
        self._resolved_value_cache: Dict[Tuple, Any] = {}
        # Cache merged contexts to avoid creating new dataclass instances
        self._merged_context_cache: Dict[Tuple, Any] = {}

    def resolve_config_attr(
        self,
        config_obj: object,
        attr_name: str,
        context_stack: list,
        live_context: Dict[Type, Dict[str, Any]],
        cache_token: int
    ) -> Any:
        """
        Resolve config attribute through context hierarchy with caching.

        Completely generic - no knowledge of UI, steps, orchestrators, or domain concepts.

        Args:
            config_obj: Config dataclass instance to resolve attribute from
            attr_name: Attribute name to resolve (e.g., 'enabled')
            context_stack: List of context objects to resolve through (e.g., [global_config, pipeline_config, step])
            live_context: Live values from form managers, keyed by type
            cache_token: Current cache token for invalidation

        Returns:
            Resolved attribute value
        """
        # CRITICAL: Disable lazy cache during resolution
        # Flash detection uses historical snapshots with different tokens
        # The lazy cache uses current token, which breaks flash detection
        token = _disable_lazy_cache.set(True)
        try:
            # Build cache key using object identities
            context_ids = tuple(id(ctx) for ctx in context_stack)
            cache_key = (id(config_obj), attr_name, context_ids, cache_token)

            # Check resolved value cache
            if cache_key in self._resolved_value_cache:
                return self._resolved_value_cache[cache_key]

            # Cache miss - resolve
            resolved_value = self._resolve_uncached(
                config_obj, attr_name, context_stack, live_context
            )

            # Store in cache
            self._resolved_value_cache[cache_key] = resolved_value

            return resolved_value
        finally:
            # Restore lazy cache state
            _disable_lazy_cache.reset(token)

    def resolve_all_lazy_attrs(
        self,
        obj: object,
        context_stack: list,
        live_context: Dict[Type, Dict[str, Any]],
        cache_token: int
    ) -> Dict[str, Any]:
        """
        Resolve ALL lazy dataclass attributes on an object in one context setup.

        This introspects the object to find all dataclass fields and resolves them
        all at once, which is much faster than resolving each field individually.

        Works for both dataclass and non-dataclass objects (e.g., FunctionStep).
        For non-dataclass objects, discovers attributes by introspecting the object.

        Args:
            obj: Object with lazy dataclass attributes to resolve
            context_stack: List of context objects (outermost to innermost)
            live_context: Dict mapping config types to field values
            cache_token: Current token for cache invalidation

        Returns:
            Dict mapping attribute names to resolved values
        """
        from dataclasses import fields, is_dataclass
        import logging
        logger = logging.getLogger(__name__)

        # Discover attribute names from the object
        if is_dataclass(obj):
            # Dataclass: use fields() to get all field names
            attr_names = [f.name for f in fields(obj)]
            logger.debug(f"🔍 resolve_all_lazy_attrs: obj is dataclass {type(obj).__name__}, found {len(attr_names)} fields: {attr_names}")
        else:
            # Non-dataclass: introspect object to find dataclass attributes
            # Get all attributes from the object's __dict__ and class
            attr_names = []
            for attr_name in dir(obj):
                if attr_name.startswith('_'):
                    continue
                try:
                    attr_value = getattr(obj, attr_name)
                    # Check if this attribute is a dataclass (lazy or not)
                    if is_dataclass(attr_value):
                        attr_names.append(attr_name)
                except (AttributeError, TypeError):
                    continue
            logger.debug(f"🔍 resolve_all_lazy_attrs: obj is non-dataclass {type(obj).__name__}, found {len(attr_names)} dataclass attrs: {attr_names}")

        if not attr_names:
            logger.debug(f"🔍 resolve_all_lazy_attrs: No attributes found for {type(obj).__name__}, returning empty dict")
            return {}

        # Use existing resolve_all_config_attrs method
        return self.resolve_all_config_attrs(
            config_obj=obj,
            attr_names=attr_names,
            context_stack=context_stack,
            live_context=live_context,
            cache_token=cache_token
        )

    def resolve_all_config_attrs(
        self,
        config_obj: object,
        attr_names: list[str],
        context_stack: list,
        live_context: Dict[Type, Dict[str, Any]],
        cache_token: int
    ) -> Dict[str, Any]:
        """
        Resolve multiple config attributes in one shot (O(1) context setup).

        This is MUCH faster than calling resolve_config_attr() for each attribute
        because we only build the merged context once and resolve all attributes
        within that context.

        Args:
            config_obj: Config object to resolve attributes on
            attr_names: List of attribute names to resolve
            context_stack: List of context objects (outermost to innermost)
            live_context: Dict mapping config types to field values
            cache_token: Current token for cache invalidation

        Returns:
            Dict mapping attribute names to resolved values
        """
        # CRITICAL: Disable lazy cache during resolution
        # Flash detection uses historical snapshots with different tokens
        # The lazy cache uses current token, which breaks flash detection
        token = _disable_lazy_cache.set(True)
        try:
            # Check which attributes are already cached
            context_ids = tuple(id(ctx) for ctx in context_stack)
            results = {}
            uncached_attrs = []

            for attr_name in attr_names:
                cache_key = (id(config_obj), attr_name, context_ids, cache_token)
                if cache_key in self._resolved_value_cache:
                    results[attr_name] = self._resolved_value_cache[cache_key]
                else:
                    uncached_attrs.append(attr_name)

            # If all cached, return immediately
            if not uncached_attrs:
                return results

            # Resolve all uncached attributes in one context setup
            # Build merged contexts once (reuse existing _resolve_uncached logic)
            # Make live_context hashable (same logic as _resolve_uncached)
            def make_hashable(obj):
                if isinstance(obj, dict):
                    return tuple(sorted((str(k), make_hashable(v)) for k, v in obj.items()))
                elif isinstance(obj, list):
                    return tuple(make_hashable(item) for item in obj)
                elif isinstance(obj, set):
                    return tuple(sorted(str(make_hashable(item)) for item in obj))
                elif isinstance(obj, (int, str, float, bool, type(None))):
                    return obj
                else:
                    return str(obj)

            live_context_key = tuple(
                (str(type_key), make_hashable(values))
                for type_key, values in sorted(live_context.items(), key=lambda x: str(x[0]))
            )
            merged_cache_key = (context_ids, live_context_key)

            if merged_cache_key in self._merged_context_cache:
                merged_contexts = self._merged_context_cache[merged_cache_key]
            else:
                # Merge live values into each context object
                merged_contexts = [
                    self._merge_live_values(ctx, live_context.get(type(ctx)))
                    for ctx in context_stack
                ]
                self._merged_context_cache[merged_cache_key] = merged_contexts

            # Resolve all uncached attributes in one nested context
            # Build nested context managers once, then resolve all attributes
            from openhcs.config_framework.context_manager import config_context

            def resolve_all_in_context(contexts_remaining):
                if not contexts_remaining:
                    # Innermost level - get all attributes
                    return {attr_name: getattr(config_obj, attr_name) for attr_name in uncached_attrs}

                # Enter context and recurse
                ctx = contexts_remaining[0]
                with config_context(ctx):
                    return resolve_all_in_context(contexts_remaining[1:])

            uncached_results = resolve_all_in_context(merged_contexts) if merged_contexts else {
                attr_name: getattr(config_obj, attr_name) for attr_name in uncached_attrs
            }

            # Cache and merge results
            for attr_name, value in uncached_results.items():
                cache_key = (id(config_obj), attr_name, context_ids, cache_token)
                self._resolved_value_cache[cache_key] = value
                results[attr_name] = value

            return results
        finally:
            # Restore lazy cache state
            _disable_lazy_cache.reset(token)

    def invalidate(self) -> None:
        """Invalidate all caches."""
        self._resolved_value_cache.clear()
        self._merged_context_cache.clear()

    def reconstruct_live_values(self, live_values: Dict[str, Any]) -> Dict[str, Any]:
        """Materialize live values by reconstructing nested dataclasses."""
        if not live_values:
            return {}

        return {
            field_name: self._reconstruct_value(field_value)
            for field_name, field_value in live_values.items()
        }

    def _resolve_uncached(
        self,
        config_obj: object,
        attr_name: str,
        context_stack: list,
        live_context: Dict[Type, Dict[str, Any]]
    ) -> Any:
        """Resolve config attribute through context hierarchy (uncached)."""
        # CRITICAL OPTIMIZATION: Cache merged contexts to avoid creating new dataclass instances
        # Build cache key for merged contexts
        context_ids = tuple(id(ctx) for ctx in context_stack)

        # Make live_context hashable by converting lists to tuples recursively
        def make_hashable(obj):
            if isinstance(obj, dict):
                # Sort by string representation of keys to handle unhashable keys
                return tuple(sorted((str(k), make_hashable(v)) for k, v in obj.items()))
            elif isinstance(obj, list):
                return tuple(make_hashable(item) for item in obj)
            elif isinstance(obj, set):
                return tuple(sorted(str(make_hashable(item)) for item in obj))
            elif isinstance(obj, (int, str, float, bool, type(None))):
                return obj
            else:
                # For other types (enums, objects, etc.), use string representation
                return str(obj)

        live_context_key = tuple(
            (str(type_key), make_hashable(values))  # Convert type to string for hashability
            for type_key, values in sorted(live_context.items(), key=lambda x: str(x[0]))
        )
        merged_cache_key = (context_ids, live_context_key)

        # Check merged context cache
        if merged_cache_key in self._merged_context_cache:
            merged_contexts = self._merged_context_cache[merged_cache_key]
        else:
            # Merge live values into each context object
            merged_contexts = [
                self._merge_live_values(ctx, live_context.get(type(ctx)))
                for ctx in context_stack
            ]
            # Store in cache
            self._merged_context_cache[merged_cache_key] = merged_contexts

        # Resolve through nested context stack
        return self._resolve_through_contexts(merged_contexts, config_obj, attr_name)

    def _resolve_through_contexts(self, merged_contexts: list, config_obj: object, attr_name: str) -> Any:
        """Resolve through nested context stack using config_context()."""
        # Build nested context managers
        if not merged_contexts:
            # No context - just get attribute directly
            return getattr(config_obj, attr_name)

        # Nest contexts from outermost to innermost
        def resolve_in_context(contexts_remaining):
            if not contexts_remaining:
                # Innermost level - get the attribute
                if attr_name == 'well_filter':
                    from openhcs.config_framework.context_manager import extract_all_configs_from_context
                    available_configs = extract_all_configs_from_context()
                    logger.info(f"🔍 INNERMOST CONTEXT: Resolving {type(config_obj).__name__}.{attr_name}")
                    logger.info(f"🔍 INNERMOST CONTEXT: available_configs = {list(available_configs.keys())}")
                    for config_name, config_instance in available_configs.items():
                        if 'WellFilterConfig' in config_name:
                            wf_value = getattr(config_instance, 'well_filter', 'N/A')
                            logger.info(f"🔍 INNERMOST CONTEXT: {config_name}.well_filter = {wf_value}")
                return getattr(config_obj, attr_name)

            # Enter context and recurse
            ctx = contexts_remaining[0]
            with config_context(ctx):
                return resolve_in_context(contexts_remaining[1:])

        return resolve_in_context(merged_contexts)

    def _merge_live_values(self, base_obj: object, live_values: Optional[Dict[str, Any]]) -> object:
        """Merge live values into base object.

        CRITICAL: Passes None values through to dataclasses.replace(). When a field is reset
        to None in a form, the None value should override the saved concrete value in the
        base object. This allows the lazy resolution system to walk up the MRO to find the
        inherited value from parent context.

        Example: PipelineConfig form resets well_filter_config.enabled to None
        → dataclasses.replace(saved_pipeline_config, well_filter_config=LazyWellFilterConfig(enabled=None))
        → When resolving enabled, the None triggers MRO walk to GlobalPipelineConfig
        """
        if live_values is None or not is_dataclass(base_obj):
            return base_obj

        # Reconstruct nested dataclasses recursively
        reconstructed_values = self.reconstruct_live_values(live_values)

        # Merge into base object (including None values to override saved concrete values)
        if reconstructed_values:
            return dataclass_replace(base_obj, **reconstructed_values)  # type: ignore[arg-type]
        else:
            return base_obj

    def _reconstruct_value(self, value: Any) -> Any:
        """
        Recursively reconstruct nested dataclasses from (type, dict) tuples.

        Handles arbitrary nesting depth without nested if statements.
        """
        # Base case: not a tuple
        if not isinstance(value, tuple):
            return value

        # Base case: not a (type, dict) tuple
        if len(value) != 2:
            return value

        dataclass_type, field_dict = value

        # Base case: not a dataclass type
        if not is_dataclass(dataclass_type):
            return value

        # Recursive case: reconstruct nested fields
        reconstructed_fields = {
            field_name: self._reconstruct_value(field_value)
            for field_name, field_value in field_dict.items()
        }

        # Create dataclass instance
        return dataclass_type(**reconstructed_fields)  # type: ignore[misc]
