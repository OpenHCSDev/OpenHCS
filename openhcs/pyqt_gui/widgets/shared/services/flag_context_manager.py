"""
Metaprogrammed context manager factory for boolean flag management.

This module provides a universal context manager for managing temporary boolean flags
on objects, following the OpenHCS pattern from config_framework/context_manager.py.

Key features:
1. Single implementation handles all flag patterns
2. Automatic save/restore of previous values
3. Enum-based validation for type safety
4. Composable and nestable
5. Guaranteed cleanup even on exception

Pattern:
    Instead of:
        self._in_reset = True
        try:
            # ... logic
        finally:
            self._in_reset = False
    
    Use:
        with FlagContextManager.manage_flags(self, _in_reset=True):
            # ... logic

This eliminates duplicate try/finally patterns and ensures flags are always restored.
"""

from contextlib import contextmanager
from enum import Enum
from typing import Any, Dict, Set
import logging

logger = logging.getLogger(__name__)


class ManagerFlag(Enum):
    """
    Registry of valid ParameterFormManager flags.
    
    This enum serves as:
    1. Documentation of all available flags
    2. Validation for FlagContextManager
    3. Type-safe flag references
    
    Add new flags here as they're introduced to the codebase.
    """
    IN_RESET = '_in_reset'
    BLOCK_CROSS_WINDOW = '_block_cross_window_updates'
    INITIAL_LOAD_COMPLETE = '_initial_load_complete'


class FlagContextManager:
    """
    Metaprogrammed context manager factory for boolean flag management.
    
    This class provides a universal context manager that can manage any combination
    of boolean flags on an object, with automatic save/restore and validation.
    
    Examples:
        # Single flag:
        with FlagContextManager.manage_flags(self, _in_reset=True):
            self._reset_parameter_impl(param_name)
        
        # Multiple flags:
        with FlagContextManager.manage_flags(self, _in_reset=True, _block_cross_window_updates=True):
            for param_name in param_names:
                self._reset_parameter_impl(param_name)
        
        # Convenience method for reset:
        with FlagContextManager.reset_context(self):
            # ... reset logic
    """
    
    # Registry of valid flags (extracted from enum)
    VALID_FLAGS: Set[str] = {flag.value for flag in ManagerFlag}
    
    @staticmethod
    @contextmanager
    def manage_flags(obj: Any, **flags: bool):
        """
        Context manager that sets flags on entry and restores previous values on exit.
        
        This is the core metaprogrammed context manager that handles all flag patterns.
        It saves previous values, sets new values, and guarantees restoration even on exception.
        
        Args:
            obj: Object to set flags on (typically ParameterFormManager instance)
            **flags: Flag names and values to set (e.g., _in_reset=True)
        
        Raises:
            ValueError: If any flag name is not in VALID_FLAGS registry
        
        Example:
            with FlagContextManager.manage_flags(self, _in_reset=True, _block_cross_window_updates=True):
                # Both flags are True here
                # ... logic
            # Both flags restored to previous values here
        """
        # Validate flag names against registry
        invalid_flags = set(flags.keys()) - FlagContextManager.VALID_FLAGS
        if invalid_flags:
            raise ValueError(
                f"Invalid flags: {invalid_flags}. "
                f"Valid flags: {FlagContextManager.VALID_FLAGS}. "
                f"Add new flags to ManagerFlag enum."
            )
        
        # Save previous values
        # ANTI-DUCK-TYPING: Use direct attribute access (fail-loud if flag doesn't exist)
        # All flags must be initialized in ParameterFormManager.__init__
        prev_values: Dict[str, bool] = {}
        for flag_name in flags:
            prev_values[flag_name] = getattr(obj, flag_name)  # No default - fail if missing
            logger.debug(f"Saving flag {flag_name}={prev_values[flag_name]} on {type(obj).__name__}")
        
        # Set new values
        for flag_name, flag_value in flags.items():
            setattr(obj, flag_name, flag_value)
            logger.debug(f"Setting flag {flag_name}={flag_value} on {type(obj).__name__}")
        
        try:
            yield
        finally:
            # Restore previous values (guaranteed even on exception)
            for flag_name, prev_value in prev_values.items():
                setattr(obj, flag_name, prev_value)
                logger.debug(f"Restoring flag {flag_name}={prev_value} on {type(obj).__name__}")
    
    @staticmethod
    @contextmanager
    def reset_context(obj: Any, block_cross_window: bool = True):
        """
        Convenience context manager for reset operations.
        
        This is a specialized version of manage_flags() for the common reset pattern.
        It sets _in_reset=True and optionally _block_cross_window_updates=True.
        
        Args:
            obj: Object to set flags on (typically ParameterFormManager instance)
            block_cross_window: If True, also block cross-window updates (default: True)
        
        Example:
            # Single parameter reset (don't block cross-window):
            with FlagContextManager.reset_context(self, block_cross_window=False):
                self._reset_parameter_impl(param_name)
            
            # Batch reset (block cross-window):
            with FlagContextManager.reset_context(self):
                for param_name in param_names:
                    self._reset_parameter_impl(param_name)
        """
        flags = {ManagerFlag.IN_RESET.value: True}
        if block_cross_window:
            flags[ManagerFlag.BLOCK_CROSS_WINDOW.value] = True
        
        with FlagContextManager.manage_flags(obj, **flags):
            yield
    
    @staticmethod
    @contextmanager
    def initial_load_context(obj: Any):
        """
        Convenience context manager for initial form load.
        
        Sets _initial_load_complete=False during form building, then sets it to True on exit.
        This disables live updates during initial form construction.
        
        Args:
            obj: Object to set flags on (typically ParameterFormManager instance)
        
        Example:
            with FlagContextManager.initial_load_context(self):
                self.build_form()
            # _initial_load_complete is now True
        """
        # Set flag to False during load
        # ANTI-DUCK-TYPING: Use direct attribute access (fail-loud if flag doesn't exist)
        prev_value = getattr(obj, ManagerFlag.INITIAL_LOAD_COMPLETE.value)  # No default - fail if missing
        setattr(obj, ManagerFlag.INITIAL_LOAD_COMPLETE.value, False)
        
        try:
            yield
        finally:
            # Set to True on exit (load complete)
            setattr(obj, ManagerFlag.INITIAL_LOAD_COMPLETE.value, True)
    
    @staticmethod
    def is_flag_set(obj: Any, flag: ManagerFlag) -> bool:
        """
        Check if a flag is currently set to True.

        Args:
            obj: Object to check flag on
            flag: ManagerFlag enum value

        Returns:
            True if flag is set, False otherwise

        Example:
            if FlagContextManager.is_flag_set(self, ManagerFlag.IN_RESET):
                return  # Skip expensive operation during reset
        """
        # ANTI-DUCK-TYPING: Use direct attribute access (fail-loud if flag doesn't exist)
        return getattr(obj, flag.value)  # No default - fail if missing
    
    @staticmethod
    def get_flag_state(obj: Any) -> Dict[str, bool]:
        """
        Get current state of all registered flags.

        Useful for debugging and logging.

        Args:
            obj: Object to get flag state from

        Returns:
            Dict mapping flag names to their current values

        Example:
            state = FlagContextManager.get_flag_state(self)
            logger.debug(f"Flag state: {state}")
        """
        # ANTI-DUCK-TYPING: Use direct attribute access (fail-loud if flag doesn't exist)
        return {
            flag.value: getattr(obj, flag.value)  # No default - fail if missing
            for flag in ManagerFlag
        }

