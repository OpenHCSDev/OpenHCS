"""
Consolidated Value Collection Service.

Merges:
- NestedValueCollectionService: Type-safe discriminated union dispatch for nested values
- DataclassUnpacker: Auto-unpack dataclass fields to instance attributes

Key features:
1. Type-safe dispatch using ParameterInfo discriminated unions
2. Auto-discovery of handlers via ParameterServiceABC
3. Auto-unpacking of dataclass fields
"""

from __future__ import annotations
from typing import Any, Optional, Dict, TYPE_CHECKING
from dataclasses import fields as dataclass_fields
import logging

from .parameter_service_abc import ParameterServiceABC
from .widget_service import WidgetService

if TYPE_CHECKING:
    from .parameter_info_types import (
        OptionalDataclassInfo,
        DirectDataclassInfo,
    )

logger = logging.getLogger(__name__)


class ValueCollectionService(ParameterServiceABC):
    """
    Consolidated service for value collection and unpacking.

    Examples:
        service = ValueCollectionService()

        # Collect nested value with type-safe dispatch:
        value = service.collect_nested_value(manager, "some_param", nested_manager)

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
        from .parameter_type_utils import ParameterTypeUtils

        param_name = info.name
        param_type = info.type
        
        checkbox = WidgetService.find_nested_checkbox(manager, param_name)
        if checkbox and not checkbox.isChecked():
            return None

        # Use nested_manager.parameters (scoped and prefix-stripped) NOT state.parameters (all paths)
        # CRITICAL: Do NOT filter out None values!
        # In OpenHCS, None has semantic meaning: "inherit from parent context"
        # When a user explicitly resets a field to None, we MUST include that None
        # so the dataclass can be constructed with the user's explicit None value.
        nested_values = nested_manager.parameters.copy()

        if not nested_values:
            logger.debug(f"[ValueCollection] Optional {param_name}: no nested edits, returning default")
            return manager.param_defaults.get(info.name)

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

        # Use nested_manager.parameters (scoped and prefix-stripped) NOT state.parameters (all paths)
        # CRITICAL: Do NOT filter out None values!
        # In OpenHCS, None has semantic meaning: "inherit from parent context"
        nested_values = nested_manager.parameters.copy()

        if not nested_values:
            logger.debug(f"[ValueCollection] Direct {info.name}: no nested edits, returning default")
            return manager.param_defaults.get(info.name)

        return param_type(**nested_values)
    
    def _collect_GenericInfo(self, info, manager, nested_manager) -> Dict[str, Any]:
        """Collect value as raw dict (fallback for non-dataclass types)."""
        # Uses all 3 params - info/manager kept for interface consistency with other _collect_* methods
        _ = info, manager  # Silence unused warnings - interface requires these params
        return nested_manager.state.get_current_values()

    # ========== DATACLASS RECONSTRUCTION (from DataclassReconstructionUtils) ==========

    @staticmethod
    def reconstruct_nested_dataclasses(live_values: dict) -> dict:
        """Return live values unchanged."""
        return dict(live_values) if live_values else {}

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
