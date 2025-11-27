"""
Consolidated Value Collection Service.

Merges:
- NestedValueCollectionService: Type-safe discriminated union dispatch for nested values
- DataclassReconstructionUtils: Reconstructing nested dataclasses from tuple format  
- DataclassUnpacker: Auto-unpack dataclass fields to instance attributes

Key features:
1. Type-safe dispatch using ParameterInfo discriminated unions
2. Auto-discovery of handlers via ParameterServiceABC
3. Proper dataclass reconstruction from tuple format
4. Auto-unpacking of dataclass fields
"""

from __future__ import annotations
from typing import Any, Optional, Dict, TYPE_CHECKING
from dataclasses import fields as dataclass_fields, is_dataclass
import dataclasses
import logging

from .parameter_service_abc import ParameterServiceABC
from .widget_service import WidgetService

if TYPE_CHECKING:
    from openhcs.ui.shared.parameter_info_types import (
        OptionalDataclassInfo,
        DirectDataclassInfo,
        GenericInfo
    )

logger = logging.getLogger(__name__)


class ValueCollectionService(ParameterServiceABC):
    """
    Consolidated service for value collection, dataclass reconstruction, and unpacking.

    Examples:
        service = ValueCollectionService()
        
        # Collect nested value with type-safe dispatch:
        value = service.collect_nested_value(manager, "some_param", nested_manager)
        
        # Reconstruct nested dataclasses from tuple format:
        reconstructed = service.reconstruct_nested_dataclasses(live_values, base_instance)
        
        # Unpack dataclass fields to instance attributes:
        service.unpack_to_self(target, source, prefix="config_")
    """

    def _get_handler_prefix(self) -> str:
        """Return handler method prefix for auto-discovery."""
        return '_collect_'

    # ========== NESTED VALUE COLLECTION (from NestedValueCollectionService) ==========

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
        """
        info = manager.form_structure.get_parameter_info(param_name)
        return self.dispatch(info, manager, nested_manager)

    def _collect_OptionalDataclassInfo(
        self,
        info: 'OptionalDataclassInfo',
        manager,
        nested_manager
    ) -> Optional[Any]:
        """Collect value for Optional[Dataclass] parameter."""
        from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils

        param_name = info.name
        param_type = info.type
        
        checkbox = WidgetService.find_nested_checkbox(manager, param_name)
        if checkbox and not checkbox.isChecked():
            return None
        
        nested_values = nested_manager.get_current_values()
        if not nested_values:
            inner_type = ParameterTypeUtils.get_optional_inner_type(param_type)
            return inner_type()
        
        inner_type = ParameterTypeUtils.get_optional_inner_type(param_type)
        return inner_type(**nested_values)
    
    def _collect_DirectDataclassInfo(
        self,
        info: 'DirectDataclassInfo',
        manager,
        nested_manager
    ) -> Any:
        """Collect value for direct Dataclass parameter."""
        param_type = info.type
        
        nested_values = nested_manager.get_current_values()
        if not nested_values:
            return param_type()
        
        return param_type(**nested_values)
    
    def _collect_GenericInfo(
        self,
        info: 'GenericInfo',
        manager,
        nested_manager
    ) -> Dict[str, Any]:
        """Collect value as raw dict (fallback for non-dataclass types)."""
        return nested_manager.get_current_values()

    # ========== DATACLASS RECONSTRUCTION (from DataclassReconstructionUtils) ==========

    @staticmethod
    def reconstruct_nested_dataclasses(live_values: dict, base_instance=None) -> dict:
        """
        Reconstruct nested dataclasses from tuple format (type, dict) to instances.

        get_user_modified_values() returns nested dataclasses as (type, dict) tuples
        to preserve only user-modified fields. This function reconstructs them as instances.
        """
        reconstructed = {}
        for field_name, value in live_values.items():
            if isinstance(value, tuple) and len(value) == 2:
                dataclass_type, field_dict = value
                
                # Separate None and non-None fields
                none_fields = {k for k, v in field_dict.items() if v is None}
                non_none_fields = {k: v for k, v in field_dict.items() if v is not None}
                
                # Merge with base instance if available
                if base_instance and is_dataclass(base_instance):
                    field_names = {f.name for f in dataclasses.fields(base_instance)}
                    if field_name in field_names:
                        base_nested = getattr(base_instance, field_name)
                        if base_nested is not None and is_dataclass(base_nested):
                            instance = dataclasses.replace(base_nested, **non_none_fields) if non_none_fields else base_nested
                        else:
                            instance = dataclass_type(**non_none_fields) if non_none_fields else dataclass_type()
                    else:
                        instance = dataclass_type(**non_none_fields) if non_none_fields else dataclass_type()
                else:
                    instance = dataclass_type(**non_none_fields) if non_none_fields else dataclass_type()
                
                # Preserve None values using object.__setattr__
                for none_field_name in none_fields:
                    object.__setattr__(instance, none_field_name, None)

                reconstructed[field_name] = instance
            else:
                reconstructed[field_name] = value
        return reconstructed

    # ========== DATACLASS UNPACKING (from DataclassUnpacker) ==========

    @staticmethod
    def unpack_to_self(
        target: Any,
        source: Any,
        field_mapping: Optional[Dict[str, str]] = None,
        prefix: str = ""
    ) -> None:
        """
        Auto-unpack dataclass fields to instance attributes with optional renaming/prefix.

        Args:
            target: Target object to set attributes on
            source: Source dataclass to unpack fields from
            field_mapping: Optional {target_name: source_name} mapping
            prefix: Optional prefix for target attribute names
        """
        for field in dataclass_fields(source):
            src_name = field.name
            tgt_name = next(
                (k for k, v in (field_mapping or {}).items() if v == src_name),
                f"{prefix}{src_name}"
            )
            setattr(target, tgt_name, getattr(source, src_name))

