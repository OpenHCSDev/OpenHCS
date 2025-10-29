"""
Abstract base class for parameter services with auto-discovery dispatch.

This module provides a unified pattern for all services that operate on parameters
based on their ParameterInfo type. It eliminates code duplication and enforces
consistent architecture across all parameter services.

Key features:
1. Auto-discovery of handler methods based on naming convention
2. Type-safe dispatch using ParameterInfo discriminated unions
3. Zero boilerplate - just define handler methods
4. Consistent pattern across all services

Pattern:
    Instead of:
        class MyService:
            def process(self, info):
                if isinstance(info, OptionalDataclassInfo):
                    # handle optional dataclass
                elif isinstance(info, DirectDataclassInfo):
                    # handle direct dataclass
                else:
                    # handle generic
    
    Use:
        class MyService(ParameterServiceABC):
            def _get_handler_prefix(self) -> str:
                return '_process_'
            
            def _process_OptionalDataclassInfo(self, info, ...):
                # Type checker knows info is OptionalDataclassInfo!
                ...
            
            def _process_DirectDataclassInfo(self, info, ...):
                # Type checker knows info is DirectDataclassInfo!
                ...
            
            def _process_GenericInfo(self, info, ...):
                # Type checker knows info is GenericInfo!
                ...

Services using this pattern:
- ParameterResetService: _reset_OptionalDataclassInfo, etc.
- NestedValueCollectionService: _collect_OptionalDataclassInfo, etc.
- Future services: just inherit and define handlers

Architecture benefits:
- Single source of truth for dispatch logic
- No if-elif-else chains
- No manual registry maintenance
- Type-safe (type checker narrows in each handler)
- Adding new ParameterInfo type = add handler method to all services
"""

from typing import Dict, Callable, Any
from abc import ABC, abstractmethod
import logging

from openhcs.ui.shared.parameter_info_types import ParameterInfo

logger = logging.getLogger(__name__)


class ParameterServiceABC(ABC):
    """
    Abstract base for parameter services with auto-discovery dispatch.
    
    Subclasses must:
    1. Implement _get_handler_prefix() to return method prefix (e.g., '_reset_')
    2. Define handler methods following naming convention: {prefix}{ClassName}
    
    The ABC automatically discovers all handler methods and provides
    type-safe dispatch via the dispatch() method.
    
    Examples:
        class ResetService(ParameterServiceABC):
            def _get_handler_prefix(self) -> str:
                return '_reset_'
            
            def reset_parameter(self, manager, param_name: str):
                info = manager.form_structure.get_parameter_info(param_name)
                self.dispatch(info, manager)
            
            def _reset_OptionalDataclassInfo(self, info: OptionalDataclassInfo, manager):
                # Handler for Optional[Dataclass] parameters
                ...
            
            def _reset_DirectDataclassInfo(self, info: DirectDataclassInfo, manager):
                # Handler for direct Dataclass parameters
                ...
            
            def _reset_GenericInfo(self, info: GenericInfo, manager):
                # Handler for generic parameters
                ...
    """
    
    def __init__(self):
        """
        Initialize service and auto-discover handler methods.
        
        Discovers all methods matching the pattern: {prefix}{ClassName}
        where prefix is returned by _get_handler_prefix().
        """
        self._handlers: Dict[str, Callable] = {}
        prefix = self._get_handler_prefix()
        
        # Auto-discover handlers by introspecting methods
        for attr_name in dir(self):
            if attr_name.startswith(prefix):
                # Extract class name from method name
                # e.g., '_reset_OptionalDataclassInfo' -> 'OptionalDataclassInfo'
                class_name = attr_name.replace(prefix, '')
                handler = getattr(self, attr_name)
                
                # Verify it's callable
                if callable(handler):
                    self._handlers[class_name] = handler
        
        # Log discovered handlers for debugging
        if self._handlers:
            logger.debug(
                f"{self.__class__.__name__} auto-discovered handlers: "
                f"{list(self._handlers.keys())}"
            )
        else:
            logger.warning(
                f"{self.__class__.__name__} found no handlers with prefix '{prefix}'. "
                f"Did you forget to define handler methods?"
            )
    
    @abstractmethod
    def _get_handler_prefix(self) -> str:
        """
        Return the method prefix for this service's handlers.
        
        Examples:
            - ParameterResetService: '_reset_'
            - NestedValueCollectionService: '_collect_'
            - WidgetUpdateService: '_update_'
        
        Returns:
            Method prefix string (must include leading underscore)
        """
        pass
    
    def dispatch(self, info: ParameterInfo, *args, **kwargs) -> Any:
        """
        Auto-dispatch to handler based on ParameterInfo class name.
        
        This method provides type-safe dispatch without if-elif-else chains.
        The type checker can narrow the type in each handler method.
        
        Args:
            info: ParameterInfo instance (discriminated union)
            *args: Additional positional arguments passed to handler
            **kwargs: Additional keyword arguments passed to handler
        
        Returns:
            Result from handler method
        
        Raises:
            ValueError: If no handler found for ParameterInfo type
        
        Examples:
            >>> service = ResetService()
            >>> info = OptionalDataclassInfo(...)
            >>> service.dispatch(info, manager)  # Calls _reset_OptionalDataclassInfo
        """
        class_name = info.__class__.__name__
        handler = self._handlers.get(class_name)
        
        if handler is None:
            raise ValueError(
                f"No handler for {class_name} in {self.__class__.__name__}. "
                f"Available handlers: {list(self._handlers.keys())}. "
                f"Did you forget to define {self._get_handler_prefix()}{class_name}()?"
            )
        
        # Call handler with info as first argument, followed by additional args
        return handler(info, *args, **kwargs)
    
    def has_handler(self, info: ParameterInfo) -> bool:
        """
        Check if a handler exists for the given ParameterInfo type.
        
        Useful for conditional logic or validation.
        
        Args:
            info: ParameterInfo instance to check
        
        Returns:
            True if handler exists, False otherwise
        """
        class_name = info.__class__.__name__
        return class_name in self._handlers
    
    def get_supported_types(self) -> list[str]:
        """
        Get list of supported ParameterInfo type names.
        
        Useful for debugging and validation.
        
        Returns:
            List of class names that have handlers
        """
        return list(self._handlers.keys())

