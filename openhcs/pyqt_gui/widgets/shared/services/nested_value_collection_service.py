"""
Nested value collection service with type-safe discriminated union dispatch.

Uses React-style discriminated unions for type-safe parameter handling.
Eliminates all type-checking smells by using ParameterInfo polymorphism.

Key features:
1. Type-safe dispatch using ParameterInfo discriminated unions
2. Auto-discovery of handlers via ParameterServiceABC
3. Zero boilerplate - just define handler methods
4. Handles optional checkbox state logic
5. Proper dataclass reconstruction

Pattern:
    Instead of:
        if param_type and ParameterTypeUtils.is_optional_dataclass(param_type):
            checkbox = find_checkbox(...)
            if checkbox and not checkbox.isChecked():
                return None
            # ... 10 more lines
        elif param_type and is_dataclass(param_type):
            # ... 5 lines
        else:
            # ... 3 lines

    Use:
        service.collect_nested_value(manager, param_name, nested_manager)
        # Auto-dispatches to correct handler based on ParameterInfo type
"""

from __future__ import annotations
from typing import Any, Optional, Dict, TYPE_CHECKING
import logging

from .parameter_service_abc import ParameterServiceABC
from .widget_finder_service import WidgetFinderService

if TYPE_CHECKING:
    from openhcs.ui.shared.parameter_info_types import (
        OptionalDataclassInfo,
        DirectDataclassInfo,
        GenericInfo
    )

logger = logging.getLogger(__name__)


class NestedValueCollectionService(ParameterServiceABC):
    """
    Service for collecting nested parameter values with type-safe dispatch.

    Uses discriminated unions to eliminate type-checking smells.
    Handlers are auto-discovered based on ParameterInfo class names.

    Examples:
        service = NestedValueCollectionService()
        value = service.collect_nested_value(manager, "some_param", nested_manager)
    """

    def _get_handler_prefix(self) -> str:
        """Return handler method prefix for auto-discovery."""
        return '_collect_'

    def collect_nested_value(
        self,
        manager,
        param_name: str,
        nested_manager
    ) -> Optional[Any]:
        """
        Collect nested value using type-safe dispatch.

        Gets ParameterInfo from form structure and dispatches to
        the appropriate handler based on its type.

        Args:
            manager: Parent ParameterFormManager instance
            param_name: Name of the nested parameter
            nested_manager: Nested ParameterFormManager instance

        Returns:
            Collected value (dataclass instance, dict, or None)
        """
        info = manager.form_structure.get_parameter_info(param_name)
        return self.dispatch(info, manager, nested_manager)

    # ========== TYPE-SAFE COLLECTION HANDLERS ==========

    def _collect_OptionalDataclassInfo(
        self,
        info: 'OptionalDataclassInfo',
        manager,
        nested_manager
    ) -> Optional[Any]:
        """
        Collect value for Optional[Dataclass] parameter.

        Handles checkbox state logic:
        - If checkbox unchecked -> return None
        - If enabled=False in current value -> return None
        - Otherwise -> reconstruct dataclass from nested values

        Type checker knows info is OptionalDataclassInfo!
        """
        from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils

        param_name = info.name
        param_type = info.type
        
        # Check checkbox state
        checkbox = WidgetFinderService.find_nested_checkbox(manager, param_name)
        if checkbox and not checkbox.isChecked():
            return None
        
        # Check if current value has enabled=False
        current_values = manager.get_current_values()
        if current_values.get(param_name) and not current_values[param_name].enabled:
            return None
        
        # Get nested values
        nested_values = nested_manager.get_current_values()
        if not nested_values:
            # Return empty instance
            inner_type = ParameterTypeUtils.get_optional_inner_type(param_type)
            return inner_type()
        
        # Reconstruct dataclass
        inner_type = ParameterTypeUtils.get_optional_inner_type(param_type)
        return inner_type(**nested_values)
    
    def _collect_DirectDataclassInfo(
        self,
        info: 'DirectDataclassInfo',
        manager,
        nested_manager
    ) -> Any:
        """
        Collect value for direct Dataclass parameter.

        Always reconstructs the dataclass from nested values.

        Type checker knows info is DirectDataclassInfo!
        """
        param_type = info.type
        
        # Get nested values
        nested_values = nested_manager.get_current_values()
        if not nested_values:
            # Return empty instance
            return param_type()
        
        # Reconstruct dataclass
        return param_type(**nested_values)
    
    def _collect_GenericInfo(
        self,
        info: 'GenericInfo',
        manager,
        nested_manager
    ) -> Dict[str, Any]:
        """
        Collect value as raw dict (fallback for non-dataclass types).

        Returns the nested values as-is without reconstruction.
        This shouldn't normally be called for GenericInfo since they
        don't have nested managers, but we provide it for completeness.

        Type checker knows info is GenericInfo!
        """
        return nested_manager.get_current_values()

