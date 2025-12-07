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

logger = logging.getLogger(__name__)


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

    def invalidate(self) -> None:
        """Invalidate all caches."""
        self._resolved_value_cache.clear()

    def reconstruct_live_values(self, live_values: Dict[str, Any]) -> Dict[str, Any]:
        """Return live values unchanged."""
        return live_values if live_values else {}

    def _resolve_uncached(
        self,
        config_obj: object,
        attr_name: str,
        context_stack: list,
        live_context: Dict[Type, Dict[str, Any]]
    ) -> Any:
        """Resolve config attribute through context hierarchy (uncached)."""
        # Merge live values into each context object
        merged_contexts = [
            self._merge_live_values(ctx, live_context.get(type(ctx)))
            for ctx in context_stack
        ]

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
