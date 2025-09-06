"""
Automatic field path detection utility for OpenHCS configuration types.

This module provides utilities for automatically detecting field paths in dataclass
types, eliminating hardcoded field names and providing a single source of truth
for type introspection logic across the UI system.
"""

import dataclasses
import inspect
import os
import typing
from typing import Type, Optional, Union, get_origin, get_args
from dataclasses import fields

# Configuration flag for switching between inheritance and composition detection
USE_COMPOSITION_DETECTION = os.getenv('OPENHCS_USE_COMPOSITION_DETECTION', 'false').lower() == 'true'


class FieldPathDetector:
    """Automatic field path detection utility for dataclass type introspection."""

    @staticmethod
    def find_field_path_for_type(parent_type: Type, child_type: Type) -> Optional[str]:
        """
        Find field path by inspecting parent type annotations.

        Works with both dataclasses (via fields) and regular classes (via constructor parameters).

        Args:
            parent_type: The parent class/dataclass type to search within
            child_type: The child type to find the field path for

        Returns:
            The field path string (e.g., 'path_planning', 'vfs') or None if not found
        """
        try:
            if not inspect.isclass(parent_type):
                return None

            # Handle dataclass parent types first (dataclasses are classes, so check this first)
            if dataclasses.is_dataclass(parent_type):
                # Get all fields from parent type
                parent_fields = fields(parent_type)

                for field in parent_fields:
                    field_type = FieldPathDetector._unwrap_optional_type(field.type)

                    # Check for direct type match (handles the common case)
                    if field_type == child_type:
                        return field.name

            # Handle regular class parent types by searching constructor parameters
            # This also serves as fallback for dataclasses if no field match found
            return FieldPathDetector._find_field_path_in_constructor(parent_type, child_type)

        except Exception:
            # Fail gracefully for any type introspection issues
            return None

    @staticmethod
    def _find_field_path_in_constructor(parent_type: Type, child_type: Type) -> Optional[str]:
        """
        Find field path by searching constructor parameters of a class.

        This allows FieldPathDetector to work with regular classes by treating
        their constructor parameters as if they were dataclass fields.

        Args:
            parent_type: The parent class type to search within
            child_type: The child type to find the parameter for

        Returns:
            The parameter name if found, or None if not found
        """
        try:
            # Get constructor signature
            sig = inspect.signature(parent_type.__init__)

            # Try to get type hints, but fall back to raw annotations if it fails
            try:
                type_hints = typing.get_type_hints(parent_type.__init__)
            except (NameError, AttributeError):
                type_hints = {}

            for param_name, param in sig.parameters.items():
                # Skip 'self' parameter
                if param_name == 'self':
                    continue

                # Get parameter type from type hints or raw annotation
                param_type = type_hints.get(param_name, param.annotation)

                # Skip parameters without type annotations or with None type
                if param_type is None or param_type == inspect.Parameter.empty:
                    continue

                # Handle string annotations (forward references)
                if isinstance(param_type, str):
                    # Compare string annotation with target type name
                    if param_type == child_type.__name__:
                        return param_name
                    continue

                # Handle ForwardRef objects and Optional types with ForwardRef
                if FieldPathDetector._matches_forward_ref_type(param_type, child_type):
                    return param_name

                # Handle resolved Optional types (e.g., typing.Optional[ActualClass])
                if FieldPathDetector._matches_resolved_optional_type(param_type, child_type):
                    return param_name

                # Unwrap optional types for regular type objects
                unwrapped_type = FieldPathDetector._unwrap_optional_type(param_type)

                # Check for direct type match
                if unwrapped_type == child_type:
                    return param_name

            return None

        except Exception:
            # Fail gracefully for any type introspection issues
            return None

    @staticmethod
    def _matches_resolved_optional_type(param_type: Type, target_type: Type) -> bool:
        """
        Check if a resolved Optional type matches the target type.

        Handles cases like:
        - typing.Optional[ActualClass] where ActualClass is the resolved type
        """
        try:
            # Check if it's Optional/Union with resolved types
            if hasattr(param_type, '__origin__') and hasattr(param_type, '__args__'):
                # For Optional/Union types, check each argument
                for arg in param_type.__args__:
                    # Skip NoneType
                    if arg is type(None):
                        continue
                    # Check if the argument matches our target type
                    if arg == target_type:
                        return True

            return False

        except Exception:
            return False

    @staticmethod
    def _matches_forward_ref_type(param_type: Type, target_type: Type) -> bool:
        """
        Check if a parameter type (which may contain ForwardRef) matches the target type.

        Handles cases like:
        - ForwardRef('LazyStepMaterializationConfig')
        - typing.Optional[ForwardRef('LazyStepMaterializationConfig')]
        """
        try:
            # Check if it's a ForwardRef directly
            if hasattr(param_type, '__forward_arg__'):
                return param_type.__forward_arg__ == target_type.__name__

            # Check if it's Optional[ForwardRef(...)] or Union[ForwardRef(...), None]
            if hasattr(param_type, '__origin__') and hasattr(param_type, '__args__'):
                # For Optional/Union types, check each argument
                for arg in param_type.__args__:
                    if hasattr(arg, '__forward_arg__'):
                        if arg.__forward_arg__ == target_type.__name__:
                            return True

            return False

        except Exception:
            return False

    @staticmethod
    def _unwrap_optional_type(field_type: Type) -> Type:
        """
        Convert Optional[T] -> T, Union[T, None] -> T, etc.

        Extracted from the common logic in scattered implementations.
        """
        # Handle Optional types (Union[Type, None])
        if hasattr(typing, 'get_origin') and get_origin(field_type) is Union:
            # Get the non-None type from Optional[Type] or Union[Type, None]
            args = get_args(field_type)
            if len(args) == 2 and type(None) in args:
                # Return the non-None type
                return args[0] if args[1] is type(None) else args[1]

        # Return the type as-is if not a generic/optional type
        return field_type

    @staticmethod
    def find_all_field_paths_for_type(parent_type: Type, target_type: Type) -> list[str]:
        """
        Find ALL field paths that contain the target type in the parent config structure.

        This enables automatic hierarchy discovery for lazy resolution by recursively
        searching through nested dataclass structures to find all instances of a
        target type.

        Args:
            parent_type: The parent dataclass type to search within
            target_type: The target dataclass type to find all field paths for

        Returns:
            List of field paths (e.g., ['materialization_defaults', 'nested.path'])

        Examples:
            >>> FieldPathDetector.find_all_field_paths_for_type(
            ...     GlobalPipelineConfig, StepMaterializationConfig
            ... )
            ['materialization_defaults']
        """
        paths = []

        def _recursive_search(current_type: Type, current_path: str = ""):
            if not dataclasses.is_dataclass(current_type):
                return

            for field in dataclasses.fields(current_type):
                field_type = FieldPathDetector._unwrap_optional_type(field.type)
                field_path = f"{current_path}.{field.name}" if current_path else field.name

                # Direct type match
                if field_type == target_type:
                    paths.append(field_path)
                # Recursive search in nested dataclasses
                elif dataclasses.is_dataclass(field_type):
                    _recursive_search(field_type, field_path)

        _recursive_search(parent_type)
        return paths

    @staticmethod
    def find_inheritance_relationships(target_type: Type) -> list[Type]:
        """
        Find all parent dataclasses that target_type inherits from.

        This method recursively traverses the inheritance chain to discover
        all dataclass parents, enabling automatic sibling inheritance detection
        for lazy configuration resolution.

        Args:
            target_type: The dataclass type to analyze for inheritance relationships

        Returns:
            List of parent dataclass types in inheritance order

        Examples:
            >>> FieldPathDetector.find_inheritance_relationships(StepMaterializationConfig)
            [PathPlanningConfig]
        """
        inheritance_chain = []

        for base in target_type.__bases__:
            if base != object and dataclasses.is_dataclass(base):
                inheritance_chain.append(base)
                # Recursively find parent relationships
                inheritance_chain.extend(FieldPathDetector.find_inheritance_relationships(base))

        return inheritance_chain

    @staticmethod
    def find_all_relationships(target_type: Type) -> list:
        """
        Find ALL relationships - both inheritance AND composition.

        This detects relationships regardless of implementation approach,
        providing complete relationship discovery for lazy resolution.

        Args:
            target_type: The dataclass type to analyze

        Returns:
            List of all related types (inherited + composed, deduplicated)
        """
        all_relationships = []

        # Find inheritance relationships
        inheritance_relationships = FieldPathDetector.find_inheritance_relationships(target_type)
        all_relationships.extend(inheritance_relationships)

        # Find composition relationships
        from openhcs.core.composition_detection import find_composition_relationships
        composition_relationships = find_composition_relationships(target_type)
        all_relationships.extend(composition_relationships)

        # Deduplicate while preserving order
        seen = set()
        deduplicated = []
        for rel_type in all_relationships:
            if rel_type not in seen:
                seen.add(rel_type)
                deduplicated.append(rel_type)

        return deduplicated

    @staticmethod
    def find_all_field_paths_unified(root_type: Type, target_type: Type) -> list:
        """
        Find ALL field paths - both inheritance AND composition paths.

        Args:
            root_type: The root dataclass to search within
            target_type: The target type to find paths for

        Returns:
            List of all field paths where target_type appears (inheritance + composition)
        """
        all_paths = []

        # Find inheritance-based paths
        inheritance_paths = FieldPathDetector.find_all_field_paths_for_type(root_type, target_type)
        all_paths.extend(inheritance_paths)

        # Find composition-based paths
        from openhcs.core.composition_detection import find_all_composition_paths_for_type
        composition_paths = find_all_composition_paths_for_type(root_type, target_type)
        all_paths.extend(composition_paths)

        # Deduplicate while preserving order
        seen = set()
        deduplicated = []
        for path in all_paths:
            if path not in seen:
                seen.add(path)
                deduplicated.append(path)

        return deduplicated

    @staticmethod
    def resolve_field_unified(instance, field_name: str):
        """
        Unified field resolution that works with both inheritance and composition.

        This provides the most comprehensive field resolution by trying both
        inheritance-based attribute access and composition-based traversal.

        Args:
            instance: The dataclass instance to resolve from
            field_name: The field name to resolve

        Returns:
            The resolved field value, or None if not found
        """
        # First try direct attribute access (works for inheritance)
        if hasattr(instance, field_name):
            value = getattr(instance, field_name)
            if value is not None:
                return value

        # Then try composition-based resolution
        from openhcs.core.composition_detection import resolve_field_through_composition
        composition_result = resolve_field_through_composition(instance, field_name)
        if composition_result is not None:
            return composition_result

        return None