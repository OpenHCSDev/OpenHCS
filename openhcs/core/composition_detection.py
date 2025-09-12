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


def discover_composition_hierarchy_from_instance(instance: Any) -> Dict[Type, List[str]]:
    """Auto-discover composition relationships by introspecting an actual instance."""
    hierarchy = {}
    visited_objects = set()  # Prevent infinite recursion

    def traverse(obj: Any, obj_type: Type, path_prefix: str = ""):
        obj_id = id(obj)
        if obj_id in visited_objects:
            return
        visited_objects.add(obj_id)

        if is_dataclass(obj_type):
            # Handle dataclass fields
            for field in fields(obj_type):
                field_type = _unwrap_optional(field.type)
                field_path = f"{path_prefix}.{field.name}" if path_prefix else field.name

                if is_dataclass(field_type):
                    hierarchy.setdefault(field_type, []).append(field_path)
                    # Get the actual field value to continue traversal
                    # Use object.__getattribute__ to avoid triggering lazy resolution
                    try:
                        field_value = object.__getattribute__(obj, field.name)
                        if field_value is not None:
                            traverse(field_value, field_type, field_path)
                    except AttributeError:
                        pass
        else:
            # Handle regular object by introspecting its actual attributes
            for attr_name in dir(obj):
                if attr_name.startswith('_'):
                    continue

                try:
                    attr_value = object.__getattribute__(obj, attr_name)

                    # Skip methods and other non-data attributes
                    if callable(attr_value):
                        continue

                    # Check if this attribute is a dataclass instance
                    if attr_value is not None and is_dataclass(attr_value):
                        attr_type = type(attr_value)
                        field_path = f"{path_prefix}.{attr_name}" if path_prefix else attr_name
                        hierarchy.setdefault(attr_type, []).append(field_path)
                        traverse(attr_value, attr_type, field_path)

                except (AttributeError, TypeError):
                    continue

    traverse(instance, type(instance))
    return hierarchy


def discover_composition_hierarchy(root_type: Type) -> Dict[Type, List[str]]:
    """Auto-discover composition relationships and field paths for dataclass types."""
    if not is_dataclass(root_type):
        # For non-dataclass types, we can't reliably discover composition without an instance
        # Return empty hierarchy - caller should use discover_composition_hierarchy_from_instance
        return {}

    hierarchy = {}
    visited_types = set()

    def traverse(current_type: Type, path_prefix: str = ""):
        if current_type in visited_types:
            return
        visited_types.add(current_type)

        for field in fields(current_type):
            field_type = _unwrap_optional(field.type)
            field_path = f"{path_prefix}.{field.name}" if path_prefix else field.name

            if is_dataclass(field_type):
                hierarchy.setdefault(field_type, []).append(field_path)
                traverse(field_type, field_path)

    traverse(root_type)
    return hierarchy


def find_composition_relationships(target_type: Type) -> List[Type]:
    """Find all composed types - composition equivalent of inheritance detection."""
    return list(discover_composition_hierarchy(target_type).keys())


def find_all_composition_paths_for_type(root_type: Type, target_type: Type) -> List[str]:
    """Find field paths for target type - composition equivalent of field path detection."""
    return discover_composition_hierarchy(root_type).get(target_type, [])


# resolve_field_through_composition removed - dual-axis resolver handles composition resolution


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
                # Use dual-axis resolver for composition resolution
                from openhcs.core.dual_axis_resolver_recursive import get_recursive_resolver
                resolver = get_recursive_resolver()
                composition_value = resolver.resolve_field(instance, field_name)
                results['composition_value'] = composition_value
                results['composition_paths'] = ['dual-axis-resolver']  # Simplified path info
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
