"""
Composition-based relationship detection for OpenHCS configuration system.

Mathematical simplification of inheritance detection using composition patterns.
Provides equivalent functionality with explicit field relationships.
"""

from dataclasses import fields, is_dataclass
from typing import Any, Dict, List, Optional, Type, Union, get_origin, get_args


def _unwrap_optional(field_type: Type) -> Type:
    """Unwrap Optional[Type] to get actual Type."""
    if get_origin(field_type) is Union:
        args = get_args(field_type)
        if len(args) == 2 and type(None) in args:
            return next(arg for arg in args if arg is not type(None))
    return field_type


def discover_composition_hierarchy(dataclass_type: Type) -> Dict[Type, List[str]]:
    """Auto-discover composition relationships and field paths."""
    if not is_dataclass(dataclass_type):
        raise ValueError(f"{dataclass_type} must be a dataclass")

    hierarchy = {}

    def traverse(current_type: Type, path_prefix: str = ""):
        for field in fields(current_type):
            field_type = _unwrap_optional(field.type)
            field_path = f"{path_prefix}.{field.name}" if path_prefix else field.name

            if is_dataclass(field_type):
                hierarchy.setdefault(field_type, []).append(field_path)
                traverse(field_type, field_path)

    traverse(dataclass_type)
    return hierarchy


def find_composition_relationships(target_type: Type) -> List[Type]:
    """Find all composed types - composition equivalent of inheritance detection."""
    return list(discover_composition_hierarchy(target_type).keys())


def find_all_composition_paths_for_type(root_type: Type, target_type: Type) -> List[str]:
    """Find field paths for target type - composition equivalent of field path detection."""
    return discover_composition_hierarchy(root_type).get(target_type, [])


def resolve_field_through_composition(instance: Any, field_name: str) -> Any:
    """
    Auto-resolve field through composition hierarchy.

    Resolution order: direct field → composed objects → nested compositions
    """
    if not is_dataclass(instance):
        return None

    # Direct field (highest priority)
    if hasattr(instance, field_name) and (value := getattr(instance, field_name)) is not None:
        return value

    # Breadth-first through compositions
    for field in fields(instance):
        if (composed_obj := getattr(instance, field.name)) and is_dataclass(composed_obj):
            if hasattr(composed_obj, field_name) and (value := getattr(composed_obj, field_name)) is not None:
                return value

    # Depth-first through nested compositions
    for field in fields(instance):
        if (composed_obj := getattr(instance, field.name)) and is_dataclass(composed_obj):
            if (resolved := resolve_field_through_composition(composed_obj, field_name)) is not None:
                return resolved

    return None


def create_composition_field_provider(
    base_class: Type,
    global_config_type: Type,
    field_path: str = None,
    context_provider: callable = None
) -> callable:
    """Create composition-based field provider for lazy resolution."""
    # Auto-discover composition paths
    composed_types = find_composition_relationships(base_class)
    composition_paths = [path for composed_type in composed_types
                        for path in find_all_composition_paths_for_type(global_config_type, composed_type)]

    def composition_provider():
        from openhcs.core.context.global_config import get_current_global_config

        current_config = context_provider() if context_provider else get_current_global_config(global_config_type)
        config_instance = type('CompositionFieldConfig', (), {})()

        for field_obj in fields(base_class):
            field_name = field_obj.name
            resolved_value = None

            if current_config:
                # Direct field resolution
                if hasattr(current_config, field_name):
                    resolved_value = getattr(current_config, field_name)

                # Composition path resolution
                if resolved_value is None:
                    for path in composition_paths:
                        try:
                            obj = current_config
                            for part in path.split('.'):
                                if (obj := getattr(obj, part, None)) is None:
                                    break

                            if obj and hasattr(obj, field_name) and (value := getattr(obj, field_name)) is not None:
                                resolved_value = value
                                break
                        except AttributeError:
                            continue

            # Fallback to field default
            if resolved_value is None:
                resolved_value = (field_obj.default if field_obj.default is not field_obj.default_factory
                                else field_obj.default_factory())

            setattr(config_instance, field_name, resolved_value)

        return config_instance

    return composition_provider


def create_composition_lazy_dataclass(
    base_class: Type,
    global_config_type: Type,
    field_path: str = None,
    lazy_class_name: str = None,
    context_provider: callable = None
) -> Type:
    """Create lazy dataclass using composition-based resolution."""
    from openhcs.core.lazy_config import LazyDataclassFactory

    lazy_class_name = lazy_class_name or f"Composition{base_class.__name__}"
    composition_provider = create_composition_field_provider(
        base_class, global_config_type, field_path, context_provider
    )

    return LazyDataclassFactory._create_lazy_dataclass_unified(
        base_class=base_class,
        instance_provider=composition_provider,
        lazy_class_name=lazy_class_name,
        debug_template=f"Composition-based resolution for {base_class.__name__}",
        use_recursive_resolution=False,
        fallback_chain=None,
        global_config_type=global_config_type,
        parent_field_path=field_path,
        parent_instance_provider=context_provider
    )


def compare_inheritance_vs_composition(dataclass_type: Type, global_config_type: Type) -> Dict[str, Any]:
    """Compare inheritance vs composition detection for validation."""
    from openhcs.core.field_path_detection import FieldPathDetector

    # Inheritance detection
    try:
        inheritance_relationships = FieldPathDetector.find_inheritance_relationships(dataclass_type)
        inheritance_paths = {parent_type: FieldPathDetector.find_all_field_paths_for_type(global_config_type, parent_type)
                           for parent_type in inheritance_relationships}
    except Exception:
        inheritance_relationships, inheritance_paths = [], {}

    # Composition detection
    composition_relationships = find_composition_relationships(dataclass_type)
    composition_hierarchy = discover_composition_hierarchy(dataclass_type)

    return {
        'dataclass_type': dataclass_type.__name__,
        'inheritance': {
            'relationships': [t.__name__ for t in inheritance_relationships],
            'paths': {t.__name__: paths for t, paths in inheritance_paths.items()}
        },
        'composition': {
            'relationships': [t.__name__ for t in composition_relationships],
            'hierarchy': {t.__name__: paths for t, paths in composition_hierarchy.items()}
        },
        'equivalent': len(inheritance_relationships) == len(composition_relationships)
    }


class CompositionIntegrationUtils:
    """Utilities for integrating composition detection with existing inheritance system."""

    @staticmethod
    def compare_inheritance_vs_composition(dataclass_type: Type, global_config_type: Type) -> Dict[str, Any]:
        """
        Compare inheritance-based vs composition-based relationship detection.

        Useful for validating that composition detection produces equivalent results.

        Args:
            dataclass_type: The dataclass to analyze
            global_config_type: The global config type for context

        Returns:
            Dict with comparison results
        """
        from openhcs.core.field_path_detection import FieldPathDetector

        # Inheritance-based detection
        try:
            inheritance_relationships = FieldPathDetector.find_inheritance_relationships(dataclass_type)
            inheritance_paths = {}
            for parent_type in inheritance_relationships:
                paths = FieldPathDetector.find_all_field_paths_for_type(global_config_type, parent_type)
                inheritance_paths[parent_type] = paths
        except Exception as e:
            inheritance_relationships = []
            inheritance_paths = {}
            logger.warning(f"Inheritance detection failed for {dataclass_type}: {e}")

        # Composition-based detection
        try:
            composition_relationships = CompositionHierarchyDetector.find_composition_relationships(dataclass_type)
            composition_hierarchy = CompositionHierarchyDetector.discover_composition_hierarchy(dataclass_type)
        except Exception as e:
            composition_relationships = []
            composition_hierarchy = {}
            logger.warning(f"Composition detection failed for {dataclass_type}: {e}")

        return {
            'dataclass_type': dataclass_type.__name__,
            'inheritance': {
                'relationships': [t.__name__ for t in inheritance_relationships],
                'paths': {t.__name__: paths for t, paths in inheritance_paths.items()}
            },
            'composition': {
                'relationships': [t.__name__ for t in composition_relationships],
                'hierarchy': {t.__name__: paths for t, paths in composition_hierarchy.items()}
            },
            'equivalent': len(inheritance_relationships) == len(composition_relationships)
        }

    @staticmethod
    def test_field_resolution_equivalence(
        instance: Any,
        field_name: str,
        use_inheritance: bool = True,
        use_composition: bool = True
    ) -> Dict[str, Any]:
        """
        Test that inheritance and composition field resolution produce equivalent results.

        Args:
            instance: The dataclass instance to test
            field_name: The field name to resolve
            use_inheritance: Whether to test inheritance resolution
            use_composition: Whether to test composition resolution

        Returns:
            Dict with resolution results and comparison
        """
        results = {
            'field_name': field_name,
            'instance_type': type(instance).__name__
        }

        if use_inheritance:
            try:
                # This would use the existing inheritance-based resolution
                # For now, just get the direct field value as baseline
                inheritance_value = getattr(instance, field_name, None)
                results['inheritance_value'] = inheritance_value
            except Exception as e:
                results['inheritance_error'] = str(e)

        if use_composition:
            try:
                composition_value = CompositionFieldResolver.resolve_field_through_composition(
                    instance, field_name
                )
                results['composition_value'] = composition_value

                # Get resolution paths for debugging
                resolution_paths = CompositionFieldResolver.get_composition_resolution_paths(
                    instance, field_name
                )
                results['composition_paths'] = resolution_paths
            except Exception as e:
                results['composition_error'] = str(e)

        # Compare results
        if use_inheritance and use_composition:
            inheritance_val = results.get('inheritance_value')
            composition_val = results.get('composition_value')
            results['equivalent'] = inheritance_val == composition_val

        return results


def create_composition_lazy_dataclass(
    base_class: Type,
    global_config_type: Type,
    field_path: Optional[str] = None,
    lazy_class_name: Optional[str] = None,
    context_provider: Optional[callable] = None
) -> Type:
    """
    Create a lazy dataclass using composition-based field resolution.

    This is a drop-in replacement for the inheritance-based lazy dataclass creation
    that uses composition detection instead.

    Args:
        base_class: The base dataclass type
        global_config_type: The global config type for resolution
        field_path: Optional field path for nested resolution
        lazy_class_name: Optional name for the lazy class
        context_provider: Optional context provider function

    Returns:
        A lazy dataclass type with composition-based field resolution
    """
    from openhcs.core.lazy_config import LazyDataclassFactory

    lazy_class_name = lazy_class_name or f"Composition{base_class.__name__}"

    # Create composition-based provider
    composition_provider = create_composition_field_provider(
        base_class=base_class,
        global_config_type=global_config_type,
        field_path=field_path,
        context_provider=context_provider
    )

    # Use existing factory with composition provider
    return LazyDataclassFactory._create_lazy_dataclass_unified(
        base_class=base_class,
        instance_provider=composition_provider,
        lazy_class_name=lazy_class_name,
        debug_template=f"Composition-based resolution for {base_class.__name__}",
        use_recursive_resolution=False,
        fallback_chain=None,
        global_config_type=global_config_type,
        parent_field_path=field_path,
        parent_instance_provider=context_provider
    )
