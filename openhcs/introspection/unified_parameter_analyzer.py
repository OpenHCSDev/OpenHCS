"""Unified parameter analysis interface for all parameter sources in OpenHCS TUI.

This module provides a single, consistent interface for analyzing parameters from:
- Functions and methods
- Dataclasses and their fields
- Nested dataclass structures
- Any callable or type with parameters

Replaces the fragmented approach of SignatureAnalyzer vs FieldIntrospector.
"""

import inspect
import dataclasses
from typing import Dict, Union, Callable, Type, Any, Optional
from dataclasses import dataclass

from openhcs.introspection.signature_analyzer import SignatureAnalyzer, ParameterInfo


@dataclass
class UnifiedParameterInfo:
    """Unified parameter information that works for all parameter sources."""
    name: str
    param_type: Type
    default_value: Any
    is_required: bool
    description: Optional[str] = None
    source_type: str = "unknown"  # "function", "dataclass", "nested"
    
    @classmethod
    def from_parameter_info(cls, param_info: ParameterInfo, source_type: str = "function") -> "UnifiedParameterInfo":
        """Convert from existing ParameterInfo to unified format."""
        return cls(
            name=param_info.name,
            param_type=param_info.param_type,
            default_value=param_info.default_value,
            is_required=param_info.is_required,
            description=param_info.description,
            source_type=source_type
        )


class UnifiedParameterAnalyzer:
    """Single interface for analyzing parameters from any source.
    
    This class provides a unified way to extract parameter information
    from functions, dataclasses, and other parameter sources, ensuring
    consistent behavior across the entire application.
    """
    
    @staticmethod
    def analyze(target: Union[Callable, Type, object], exclude_params: Optional[list] = None) -> Dict[str, UnifiedParameterInfo]:
        """Analyze parameters from any source.

        Args:
            target: Function, method, dataclass type, or instance to analyze
            exclude_params: Optional list of parameter names to exclude from analysis

        Returns:
            Dictionary mapping parameter names to UnifiedParameterInfo objects

        Examples:
            # Function analysis
            param_info = UnifiedParameterAnalyzer.analyze(my_function)

            # Dataclass analysis
            param_info = UnifiedParameterAnalyzer.analyze(MyDataclass)

            # Instance analysis
            param_info = UnifiedParameterAnalyzer.analyze(my_instance)

            # Instance analysis with exclusions (e.g., exclude 'func' from FunctionStep)
            param_info = UnifiedParameterAnalyzer.analyze(step_instance, exclude_params=['func'])
        """
        if target is None:
            return {}

        # Determine the type of target and route to appropriate analyzer
        if inspect.isfunction(target) or inspect.ismethod(target):
            result = UnifiedParameterAnalyzer._analyze_callable(target)
        elif inspect.isclass(target):
            if dataclasses.is_dataclass(target):
                result = UnifiedParameterAnalyzer._analyze_dataclass_type(target)
            else:
                # CRITICAL FIX: For classes, use _analyze_object_instance with use_signature_defaults=True
                # This traverses MRO to get all inherited parameters with signature defaults
                # Create a dummy instance just to get the class hierarchy analyzed
                try:
                    dummy_instance = target.__new__(target)
                    result = UnifiedParameterAnalyzer._analyze_object_instance(dummy_instance, use_signature_defaults=True)
                except:
                    # If we can't create a dummy instance, fall back to just analyzing __init__
                    result = UnifiedParameterAnalyzer._analyze_callable(target.__init__)
        elif dataclasses.is_dataclass(target):
            # Instance of dataclass
            result = UnifiedParameterAnalyzer._analyze_dataclass_instance(target)
        else:
            # Try to analyze as callable
            if callable(target):
                result = UnifiedParameterAnalyzer._analyze_callable(target)
            else:
                # For regular object instances (like step instances), analyze their class constructor
                result = UnifiedParameterAnalyzer._analyze_object_instance(target)

        # Apply exclusions if specified
        if exclude_params:
            result = {name: info for name, info in result.items() if name not in exclude_params}

        return result
    
    @staticmethod
    def _analyze_callable(callable_obj: Callable) -> Dict[str, UnifiedParameterInfo]:
        """Analyze a callable (function, method, etc.)."""
        # Use existing SignatureAnalyzer for callables
        param_info_dict = SignatureAnalyzer.analyze(callable_obj)

        # Convert to unified format
        unified_params = {}
        for name, param_info in param_info_dict.items():
            unified_params[name] = UnifiedParameterInfo.from_parameter_info(
                param_info,
                source_type="function"
            )

        return unified_params
    
    @staticmethod
    def _analyze_dataclass_type(dataclass_type: Type) -> Dict[str, UnifiedParameterInfo]:
        """Analyze a dataclass type using existing SignatureAnalyzer infrastructure."""
        # CRITICAL FIX: Use existing SignatureAnalyzer._analyze_dataclass method
        # which already handles all the docstring extraction properly
        param_info_dict = SignatureAnalyzer._analyze_dataclass(dataclass_type)

        # Convert to unified format
        unified_params = {}
        for name, param_info in param_info_dict.items():
            unified_params[name] = UnifiedParameterInfo.from_parameter_info(
                param_info,
                source_type="dataclass"
            )

        return unified_params

    @staticmethod
    def _analyze_object_instance(instance: object, use_signature_defaults: bool = False) -> Dict[str, UnifiedParameterInfo]:
        """Analyze a regular object instance by examining its full inheritance hierarchy.

        Args:
            instance: Object instance to analyze
            use_signature_defaults: If True, use signature defaults instead of instance values
        """
        # Use MRO to get all constructor parameters from the inheritance chain
        instance_class = type(instance)
        all_params = {}

        # Traverse MRO from most specific to most general (like dual-axis resolver)
        for cls in instance_class.__mro__:
            if cls == object:
                continue

            # Skip classes without custom __init__
            if not hasattr(cls, '__init__') or cls.__init__ == object.__init__:
                continue

            try:
                # Analyze this class's constructor
                class_params = UnifiedParameterAnalyzer._analyze_callable(cls.__init__)

                # Remove 'self' parameter
                if 'self' in class_params:
                    del class_params['self']

                # Special handling for **kwargs - if we see 'kwargs', skip this class
                # and let parent classes provide the actual parameters
                if 'kwargs' in class_params and len(class_params) <= 2:
                    # This class uses **kwargs, skip it and let parent classes define parameters
                    continue

                # Add parameters that haven't been seen yet (most specific wins)
                for param_name, param_info in class_params.items():
                    if param_name not in all_params and param_name != 'kwargs':
                        # CRITICAL FIX: For reset functionality, use signature defaults instead of instance values
                        if use_signature_defaults:
                            default_value = param_info.default_value
                        else:
                            # Get current value from instance if it exists
                            default_value = getattr(instance, param_name, param_info.default_value)

                        # Create parameter info with appropriate default value
                        all_params[param_name] = UnifiedParameterInfo(
                            name=param_name,
                            param_type=param_info.param_type,
                            default_value=default_value,
                            is_required=param_info.is_required,
                            description=param_info.description,  # CRITICAL FIX: Include description
                            source_type="object_instance"
                        )

            except Exception:
                # Skip classes that can't be analyzed - this is legitimate since some classes
                # in MRO might not have analyzable constructors (e.g., ABC, object)
                continue

        return all_params

    @staticmethod
    def _analyze_dataclass_instance(instance: object) -> Dict[str, UnifiedParameterInfo]:
        """Analyze a dataclass instance."""
        from openhcs.utils.performance_monitor import timer

        # Get the type and analyze it
        with timer(f"      Analyze dataclass type {type(instance).__name__}", threshold_ms=5.0):
            dataclass_type = type(instance)
            unified_params = UnifiedParameterAnalyzer._analyze_dataclass_type(dataclass_type)

        # Check if this specific instance is a lazy config - if so, use raw field values
        with timer("      Check lazy config", threshold_ms=1.0):
            from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
            # CRITICAL FIX: Don't check class name - PipelineConfig is lazy but doesn't start with "Lazy"
            # get_base_type_for_lazy() is the authoritative check for lazy dataclasses
            is_lazy_config = get_base_type_for_lazy(dataclass_type) is not None

        # Update default values with current instance values
        with timer(f"      Extract {len(unified_params)} field values from instance", threshold_ms=5.0):
            for name, param_info in unified_params.items():
                if hasattr(instance, name):
                    if is_lazy_config:
                        # For lazy configs, get raw field value to avoid triggering resolution
                        # Use object.__getattribute__() to bypass lazy property getters
                        current_value = object.__getattribute__(instance, name)
                    else:
                        # For regular dataclasses, use normal getattr
                        current_value = getattr(instance, name)

                    # Create new UnifiedParameterInfo with current value as default
                    unified_params[name] = UnifiedParameterInfo(
                        name=param_info.name,
                        param_type=param_info.param_type,
                        default_value=current_value,
                        is_required=param_info.is_required,
                        description=param_info.description,
                        source_type="dataclass_instance"
                    )

        return unified_params
    
    @staticmethod
    def analyze_nested(target: Union[Callable, Type, object], parent_info: Dict[str, UnifiedParameterInfo] = None) -> Dict[str, UnifiedParameterInfo]:
        """Analyze parameters with nested dataclass support.
        
        This method provides enhanced analysis that can handle nested dataclasses
        and maintain parent context information.
        
        Args:
            target: The target to analyze
            parent_info: Optional parent parameter information for context
            
        Returns:
            Dictionary of unified parameter information with nested support
        """
        base_params = UnifiedParameterAnalyzer.analyze(target)
        
        # For each parameter, check if it's a nested dataclass
        enhanced_params = {}
        for name, param_info in base_params.items():
            enhanced_params[name] = param_info
            
            # If this parameter is a dataclass, mark it as having nested structure
            if dataclasses.is_dataclass(param_info.param_type):
                # Update source type to indicate nesting capability
                enhanced_params[name] = UnifiedParameterInfo(
                    name=param_info.name,
                    param_type=param_info.param_type,
                    default_value=param_info.default_value,
                    is_required=param_info.is_required,
                    description=param_info.description,
                    source_type=f"{param_info.source_type}_nested"
                )
        
        return enhanced_params


# Backward compatibility aliases
# These allow existing code to continue working while migration happens
ParameterAnalyzer = UnifiedParameterAnalyzer
analyze_parameters = UnifiedParameterAnalyzer.analyze
