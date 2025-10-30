"""
Context Layer Builders for ParameterFormManager.

Implements builder pattern for constructing context stacks, replacing 200+ lines
of nested if/else logic with composable, auto-registered builders.

Pattern mirrors OpenHCS metaprogramming patterns:
- Enum-driven dispatch (ContextLayerType)
- ABC with auto-registration via metaclass
- Fail-loud architecture (no defensive programming)
- Single source of truth (CONTEXT_LAYER_BUILDERS registry)
"""

from abc import ABC, ABCMeta, abstractmethod
from enum import Enum
from typing import Any, Dict, List, Optional, TYPE_CHECKING
from contextlib import ExitStack
import dataclasses
import logging

if TYPE_CHECKING:
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

logger = logging.getLogger(__name__)


# ============================================================================
# HELPER FUNCTIONS - Query _active_form_managers directly
# ============================================================================

def _find_manager_for_type(manager: 'ParameterFormManager', target_type: type) -> Optional['ParameterFormManager']:
    """
    Find active manager for a given type by querying _active_form_managers registry.

    This replaces the live_context dict lookup pattern. Instead of:
        live_values = live_context.get(target_type)

    We now do:
        target_manager = _find_manager_for_type(manager, target_type)
        live_values = target_manager.get_values() if target_manager else None

    Args:
        manager: Current ParameterFormManager instance (for scope filtering)
        target_type: Type to find (e.g., PipelineConfig, GlobalPipelineConfig)

    Returns:
        ParameterFormManager instance for target_type, or None if not found
    """
    from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
    from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService

    for other_manager in manager._active_form_managers:
        # Skip self
        if other_manager is manager:
            continue

        # Scope filtering: only collect from same scope OR global scope (None)
        if other_manager.scope_id is not None and manager.scope_id is not None:
            if other_manager.scope_id != manager.scope_id:
                continue

        # Type matching: exact, base, or lazy
        obj_type = type(other_manager.object_instance)

        # Exact match
        if obj_type == target_type:
            logger.debug(f"Found manager for {target_type.__name__} (exact match): {other_manager.field_id}")
            return other_manager

        # Base type match
        base_type = get_base_type_for_lazy(obj_type)
        if base_type == target_type:
            logger.debug(f"Found manager for {target_type.__name__} (base match): {other_manager.field_id}")
            return other_manager

        # Lazy type match
        lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(obj_type)
        if lazy_type == target_type:
            logger.debug(f"Found manager for {target_type.__name__} (lazy match): {other_manager.field_id}")
            return other_manager

    logger.debug(f"No manager found for {target_type.__name__}")
    return None


def _get_manager_values(manager: 'ParameterFormManager', use_user_modified_only: bool) -> dict:
    """
    Get values from manager based on mode.

    Args:
        manager: ParameterFormManager instance
        use_user_modified_only: If True, get only user-modified values (for reset behavior)
                                 If False, get all current values (for normal refresh)

    Returns:
        Dict of field names to values
    """
    return manager.get_user_modified_values() if use_user_modified_only else manager.get_current_values()


def _reconstruct_nested_dataclasses(live_values: dict, base_instance=None) -> dict:
    """
    Reconstruct nested dataclasses from tuple format (type, dict) to instances.

    get_user_modified_values() returns nested dataclasses as (type, dict) tuples
    to preserve only user-modified fields. This function reconstructs them as instances
    by merging the user-modified fields into the base instance's nested dataclasses.

    Moved from PlaceholderRefreshService to be a shared helper.

    Args:
        live_values: Dict with values, may contain (type, dict) tuples for nested dataclasses
        base_instance: Base dataclass instance to merge into (for nested dataclass fields)

    Returns:
        Dict with nested dataclasses reconstructed as instances
    """
    from dataclasses import is_dataclass

    reconstructed = {}
    for field_name, value in live_values.items():
        if isinstance(value, tuple) and len(value) == 2:
            # Nested dataclass in tuple format: (type, dict)
            dataclass_type, field_dict = value

            # If we have a base instance, merge into its nested dataclass
            # ANTI-DUCK-TYPING: Use dataclass introspection instead of hasattr
            if base_instance and is_dataclass(base_instance):
                import dataclasses
                field_names = {f.name for f in dataclasses.fields(base_instance)}
                if field_name in field_names:
                    base_nested = getattr(base_instance, field_name)
                    if base_nested is not None and is_dataclass(base_nested):
                        # Merge user-modified fields into base nested dataclass
                        reconstructed[field_name] = dataclasses.replace(base_nested, **field_dict)
                    else:
                        # No base nested dataclass, create fresh instance
                        reconstructed[field_name] = dataclass_type(**field_dict)
                else:
                    # Field not in base instance, create fresh instance
                    reconstructed[field_name] = dataclass_type(**field_dict)
            else:
                # No base instance, create fresh instance
                reconstructed[field_name] = dataclass_type(**field_dict)
        else:
            # Regular value, pass through
            reconstructed[field_name] = value
    return reconstructed


# ============================================================================
# CONTEXT LAYER TYPE ENUM - Defines execution order
# ============================================================================

class ContextLayerType(Enum):
    """
    Context layer types in application order.

    Order matters! Layers are applied in enum definition order:
    1. GLOBAL_STATIC_DEFAULTS - Fresh GlobalPipelineConfig() for root editing
    2. GLOBAL_LIVE_VALUES - Live GlobalPipelineConfig from other windows
    3. PARENT_CONTEXT - Parent context(s) with live values
    4. PARENT_OVERLAY - Parent's user-modified values
    5. SIBLING_CONTEXTS - Sibling nested manager values (overrides parent values)
    6. CURRENT_OVERLAY - Current form values (always applied last)
    """
    GLOBAL_STATIC_DEFAULTS = "global_static_defaults"
    GLOBAL_LIVE_VALUES = "global_live_values"
    PARENT_CONTEXT = "parent_context"
    PARENT_OVERLAY = "parent_overlay"
    SIBLING_CONTEXTS = "sibling_contexts"
    CURRENT_OVERLAY = "current_overlay"


# ============================================================================
# CONTEXT LAYER - Data structure for a single context layer
# ============================================================================

class ContextLayer:
    """
    Represents a single context layer to be applied to the stack.
    
    Attributes:
        layer_type: Type of layer (for debugging/logging)
        instance: Dataclass instance or SimpleNamespace to apply
        mask_with_none: Whether to mask with None values (for GlobalPipelineConfig editing)
    """
    
    def __init__(self, layer_type: ContextLayerType, instance: Any, mask_with_none: bool = False):
        self.layer_type = layer_type
        self.instance = instance
        self.mask_with_none = mask_with_none
    
    def apply_to_stack(self, stack: ExitStack) -> None:
        """Apply this layer to the context stack."""
        from openhcs.config_framework.context_manager import config_context
        stack.enter_context(config_context(self.instance, mask_with_none=self.mask_with_none))


# ============================================================================
# AUTO-REGISTRATION METACLASS - Must be defined before builders
# ============================================================================

# Registry must exist before metaclass tries to register builders
CONTEXT_LAYER_BUILDERS: Dict[ContextLayerType, 'ContextLayerBuilder'] = {}


class ContextLayerBuilderMeta(ABCMeta):
    """
    Metaclass for auto-registering context layer builders.

    When a concrete builder class is defined with _layer_type attribute,
    it's automatically registered in CONTEXT_LAYER_BUILDERS.
    """
    def __new__(cls, name, bases, attrs):
        new_class = super().__new__(cls, name, bases, attrs)

        # Only register concrete classes (not ABC itself)
        if not getattr(new_class, '__abstractmethods__', None):
            layer_type = getattr(new_class, '_layer_type', None)
            if layer_type:
                CONTEXT_LAYER_BUILDERS[layer_type] = new_class()
                logger.debug(f"Registered builder {name} for {layer_type}")

        return new_class


# ============================================================================
# CONTEXT LAYER BUILDER ABC - Base class for all builders
# ============================================================================

class ContextLayerBuilder(ABC, metaclass=ContextLayerBuilderMeta):
    """
    ABC for building context layers.

    Each builder is responsible for one type of context layer.
    Builders auto-register via metaclass when they define _layer_type.
    """

    @abstractmethod
    def can_build(self, manager: 'ParameterFormManager', **kwargs) -> bool:
        """
        Check if this builder can create a layer.

        Args:
            manager: ParameterFormManager instance
            **kwargs: Additional context (live_context, skip_parent_overlay, overlay, etc.)

        Returns:
            True if this builder should create a layer
        """
        pass

    @abstractmethod
    def build(self, manager: 'ParameterFormManager', **kwargs) -> Optional[Any]:
        """
        Build the context layer(s).

        Args:
            manager: ParameterFormManager instance
            **kwargs: Additional context (live_context, skip_parent_overlay, overlay, etc.)

        Returns:
            ContextLayer, List[ContextLayer], or None
        """
        pass


# ============================================================================
# BUILDER IMPLEMENTATIONS - One per ContextLayerType
# ============================================================================

class GlobalStaticDefaultsBuilder(ContextLayerBuilder):
    """
    Builder for GLOBAL_STATIC_DEFAULTS layer.
    
    Creates fresh GlobalPipelineConfig() instance to mask thread-local loaded instance.
    Only applies when editing root GlobalPipelineConfig form (no parent context).
    """
    _layer_type = ContextLayerType.GLOBAL_STATIC_DEFAULTS
    
    def can_build(self, manager: 'ParameterFormManager', **kwargs) -> bool:
        return (manager.config.is_global_config_editing and
                manager.global_config_type is not None and
                manager.context_obj is None)
    
    def build(self, manager: 'ParameterFormManager', **kwargs) -> Optional[ContextLayer]:
        static_defaults = manager.global_config_type()
        return ContextLayer(
            layer_type=self._layer_type,
            instance=static_defaults,
            mask_with_none=True
        )


class GlobalLiveValuesBuilder(ContextLayerBuilder):
    """
    Builder for GLOBAL_LIVE_VALUES layer.

    Applies live GlobalPipelineConfig values from other open windows.
    Merges live values into thread-local GlobalPipelineConfig.
    Queries _active_form_managers directly instead of using live_context dict.
    """
    _layer_type = ContextLayerType.GLOBAL_LIVE_VALUES

    def can_build(self, manager: 'ParameterFormManager', **kwargs) -> bool:
        # Don't apply if we're editing root GlobalPipelineConfig (static defaults already applied)
        is_root_global_config = (manager.config.is_global_config_editing and
                                 manager.global_config_type is not None and
                                 manager.context_obj is None)

        return not is_root_global_config and manager.global_config_type is not None

    def build(self, manager: 'ParameterFormManager', use_user_modified_only=False, **kwargs) -> Optional[ContextLayer]:
        # Query _active_form_managers directly for GlobalPipelineConfig manager
        global_manager = _find_manager_for_type(manager, manager.global_config_type)
        if global_manager is None:
            logger.debug(f"No GlobalPipelineConfig manager found in _active_form_managers")
            return None

        # Get values from the manager
        global_live_values = _get_manager_values(global_manager, use_user_modified_only)
        if not global_live_values:
            return None

        try:
            from openhcs.config_framework.context_manager import get_base_global_config
            thread_local_global = get_base_global_config()
            if thread_local_global is not None:
                # Reconstruct nested dataclasses from tuple format
                global_live_values = _reconstruct_nested_dataclasses(
                    global_live_values, thread_local_global
                )
                global_live_instance = dataclasses.replace(
                    thread_local_global, **global_live_values
                )
                logger.debug(f"Built GLOBAL_LIVE_VALUES layer with {len(global_live_values)} fields")
                return ContextLayer(
                    layer_type=self._layer_type,
                    instance=global_live_instance
                )
        except Exception as e:
            logger.warning(f"Failed to apply live GlobalPipelineConfig: {e}")

        return None


class ParentContextBuilder(ContextLayerBuilder):
    """
    Builder for PARENT_CONTEXT layer(s).

    Applies parent context(s) with live values merged in.
    Returns list of layers (one per parent context).
    Queries _active_form_managers directly instead of using live_context dict.
    """
    _layer_type = ContextLayerType.PARENT_CONTEXT

    def can_build(self, manager: 'ParameterFormManager', **kwargs) -> bool:
        return manager.context_obj is not None

    def build(self, manager: 'ParameterFormManager', use_user_modified_only=False, **kwargs) -> List[ContextLayer]:
        """Returns list of layers (one per parent context)."""
        contexts = manager.context_obj if isinstance(manager.context_obj, list) else [manager.context_obj]
        layers = []

        for ctx in contexts:
            layer = self._build_single_context(manager, ctx, use_user_modified_only)
            if layer:
                layers.append(layer)

        return layers

    def _build_single_context(self, manager: 'ParameterFormManager', ctx: Any, use_user_modified_only: bool) -> Optional[ContextLayer]:
        """Build layer for a single parent context."""
        ctx_type = type(ctx)

        # Query _active_form_managers directly for parent context manager
        parent_manager = _find_manager_for_type(manager, ctx_type)

        if parent_manager is not None:
            try:
                # Get live values from the parent manager
                live_values = _get_manager_values(parent_manager, use_user_modified_only)
                if live_values:
                    live_values = _reconstruct_nested_dataclasses(live_values, ctx)
                    live_instance = dataclasses.replace(ctx, **live_values)
                    logger.debug(f"Built PARENT_CONTEXT layer for {ctx_type.__name__} with {len(live_values)} live fields")
                    return ContextLayer(layer_type=self._layer_type, instance=live_instance)
            except Exception as e:
                logger.warning(f"Failed to apply live parent context for {ctx_type.__name__}: {e}")

        # No live manager or failed to merge, use static context
        logger.debug(f"Built PARENT_CONTEXT layer for {ctx_type.__name__} (static, no live values)")
        return ContextLayer(layer_type=self._layer_type, instance=ctx)


class SiblingContextsBuilder(ContextLayerBuilder):
    """
    Builder for SIBLING_CONTEXTS layer(s).

    Applies sibling nested manager values for sibling inheritance.
    Queries parent's nested_managers directly instead of using live_context dict.
    Only applies for nested managers (not root managers).
    """
    _layer_type = ContextLayerType.SIBLING_CONTEXTS

    def can_build(self, manager: 'ParameterFormManager', **kwargs) -> bool:
        # Only apply for nested managers
        result = manager._parent_manager is not None
        logger.info(f"🔍 SIBLING_CAN_BUILD: {manager.field_id} - parent={manager._parent_manager is not None}, result={result}")
        return result

    def build(self, manager: 'ParameterFormManager', use_user_modified_only=False, **kwargs) -> List[ContextLayer]:
        """Returns list of layers (one per sibling context)."""
        layers = []

        # Query parent's nested_managers directly (no live_context dict needed!)
        if manager._parent_manager is None:
            return layers

        logger.info(f"🔍 SIBLING_BUILD: Building for {manager.field_id}, parent has {len(manager._parent_manager.nested_managers)} nested managers")

        # Iterate through sibling managers
        for sibling_name, sibling_manager in manager._parent_manager.nested_managers.items():
            # Skip self
            if sibling_manager is manager:
                logger.info(f"🔍 SIBLING_BUILD: Skipping {sibling_name} (self)")
                continue

            # Get values from sibling manager
            sibling_values = _get_manager_values(sibling_manager, use_user_modified_only)
            if not sibling_values:
                logger.info(f"🔍 SIBLING_BUILD: Skipping {sibling_name} (no values)")
                continue

            # Create instance from sibling values
            try:
                sibling_type = type(sibling_manager.object_instance)
                sibling_instance = sibling_type(**sibling_values)
                layers.append(ContextLayer(layer_type=self._layer_type, instance=sibling_instance))
                logger.info(f"🔍 SIBLING_CONTEXT: Added {sibling_type.__name__} ({sibling_name}) to context stack for {manager.field_id}")
            except Exception as e:
                logger.warning(f"Failed to create sibling context for {sibling_name}: {e}")

        logger.info(f"🔍 SIBLING_BUILD: Created {len(layers)} sibling layers for {manager.field_id}")
        return layers


class ParentOverlayBuilder(ContextLayerBuilder):
    """
    Builder for PARENT_OVERLAY layer.
    
    Applies parent's user-modified values for sibling inheritance.
    Only applies after initial form load to avoid polluting placeholders.
    """
    _layer_type = ContextLayerType.PARENT_OVERLAY
    
    def can_build(self, manager: 'ParameterFormManager', skip_parent_overlay=False, **kwargs) -> bool:
        parent_manager = manager._parent_manager
        return (not skip_parent_overlay and
                parent_manager is not None and
                parent_manager._initial_load_complete)
    
    def build(self, manager: 'ParameterFormManager', **kwargs) -> Optional[ContextLayer]:
        parent_manager = manager._parent_manager
        parent_user_values = parent_manager.get_user_modified_values()
        
        if not parent_user_values or not parent_manager.dataclass_type:
            return None
        
        # Exclude current nested config and parent's excluded params
        excluded_keys = {manager.field_id}
        parent_exclude_params = getattr(parent_manager.config, 'exclude_params', None)
        if parent_exclude_params:
            excluded_keys.update(parent_exclude_params)
        
        filtered_parent_values = {k: v for k, v in parent_user_values.items() if k not in excluded_keys}
        
        if not filtered_parent_values:
            return None
        
        # Use lazy version of parent type for sibling inheritance
        from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
        parent_type = parent_manager.dataclass_type
        lazy_parent_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(parent_type)
        if lazy_parent_type:
            parent_type = lazy_parent_type
        
        # Add excluded params from parent's object_instance
        parent_values_with_excluded = filtered_parent_values.copy()
        parent_exclude_params = getattr(parent_manager.config, 'exclude_params', None)
        if parent_exclude_params:
            # ANTI-DUCK-TYPING: Use dataclass introspection instead of hasattr
            from dataclasses import is_dataclass, fields
            if is_dataclass(parent_manager.object_instance):
                field_names = {f.name for f in fields(parent_manager.object_instance)}
                for excluded_param in parent_exclude_params:
                    if excluded_param not in parent_values_with_excluded and excluded_param in field_names:
                        parent_values_with_excluded[excluded_param] = getattr(parent_manager.object_instance, excluded_param)
        
        # Create parent overlay instance
        parent_overlay_instance = parent_type(**parent_values_with_excluded)
        
        # For root global config editing, use mask_with_none=True
        is_root_global_config = (manager.config.is_global_config_editing and
                                 manager.global_config_type is not None and
                                 manager.context_obj is None)
        
        return ContextLayer(
            layer_type=self._layer_type,
            instance=parent_overlay_instance,
            mask_with_none=is_root_global_config
        )


class CurrentOverlayBuilder(ContextLayerBuilder):
    """
    Builder for CURRENT_OVERLAY layer.

    Converts overlay dict to dataclass instance and applies as top layer.
    Always applied last to ensure current form values override everything.
    """
    _layer_type = ContextLayerType.CURRENT_OVERLAY

    def can_build(self, manager: 'ParameterFormManager', **kwargs) -> bool:
        # Always build - current overlay is always applied
        return True

    def build(self, manager: 'ParameterFormManager', overlay=None, **kwargs) -> Optional[ContextLayer]:
        if overlay is None:
            return None

        # Convert overlay dict to object instance
        if isinstance(overlay, dict):
            overlay_instance = self._dict_to_instance(manager, overlay)
        else:
            # Already an instance - use as-is
            overlay_instance = overlay

        # For global config editing, use mask_with_none=True to preserve None values
        # This ensures that explicitly set None values override parent values
        is_global_config_editing = (manager.config.is_global_config_editing and
                                    manager.global_config_type is not None)

        return ContextLayer(
            layer_type=self._layer_type,
            instance=overlay_instance,
            mask_with_none=is_global_config_editing
        )

    def _dict_to_instance(self, manager: 'ParameterFormManager', overlay: dict) -> Any:
        """Convert overlay dict to dataclass instance or SimpleNamespace."""
        # Empty dict and object_instance exists - use original instance
        if not overlay and manager.object_instance is not None:
            return manager.object_instance

        # No dataclass_type - use SimpleNamespace
        if not manager.dataclass_type:
            from types import SimpleNamespace
            return SimpleNamespace(**overlay)

        # Add excluded params from object_instance
        overlay_with_excluded = overlay.copy()
        exclude_params = getattr(manager.config, 'exclude_params', None) or []
        # ANTI-DUCK-TYPING: Use dataclass introspection instead of hasattr
        from dataclasses import is_dataclass, fields
        if is_dataclass(manager.object_instance):
            field_names = {f.name for f in fields(manager.object_instance)}
            for excluded_param in exclude_params:
                if excluded_param not in overlay_with_excluded and excluded_param in field_names:
                    overlay_with_excluded[excluded_param] = getattr(manager.object_instance, excluded_param)

        # Try to instantiate dataclass
        try:
            return manager.dataclass_type(**overlay_with_excluded)
        except TypeError:
            # Function or other non-instantiable type: use SimpleNamespace
            from types import SimpleNamespace
            filtered_overlay = {k: v for k, v in overlay.items() if k not in (getattr(manager.config, 'exclude_params', None) or [])}
            return SimpleNamespace(**filtered_overlay)


# ============================================================================
# UNIFIED CONTEXT BUILDING FUNCTION
# ============================================================================

def build_context_stack(manager: 'ParameterFormManager', overlay, skip_parent_overlay: bool = False, use_user_modified_only: bool = False) -> ExitStack:
    """
    UNIFIED: Build context stack using builder pattern.

    Replaces 200+ line _build_context_stack method with composable builders.
    Builders query _active_form_managers directly instead of using live_context dict.

    Args:
        manager: ParameterFormManager instance
        overlay: Current form values (dict or dataclass instance)
        skip_parent_overlay: If True, skip parent's user-modified values
        use_user_modified_only: If True, builders query only user-modified values from managers (for reset behavior)
                                 If False, builders query all current values (for normal refresh behavior)

    Returns:
        ExitStack with nested contexts in correct order
    """
    stack = ExitStack()

    # Build layers in enum order
    for layer_type in ContextLayerType:
        builder = CONTEXT_LAYER_BUILDERS.get(layer_type)
        if not builder:
            continue

        if not builder.can_build(manager, skip_parent_overlay=skip_parent_overlay, overlay=overlay):
            continue

        layers = builder.build(manager, use_user_modified_only=use_user_modified_only, skip_parent_overlay=skip_parent_overlay, overlay=overlay)

        # Handle single layer or list of layers
        if isinstance(layers, list):
            for layer in layers:
                if layer:
                    layer.apply_to_stack(stack)
        elif layers:
            layers.apply_to_stack(stack)

    return stack

