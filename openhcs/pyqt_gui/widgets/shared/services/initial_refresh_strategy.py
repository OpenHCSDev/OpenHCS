"""
Initial refresh strategy for ParameterFormManager initialization.

Determines and executes the appropriate placeholder refresh strategy
based on the manager's configuration type.
"""

from enum import Enum, auto
from typing import Any

from .enum_dispatch_service import EnumDispatchService


class RefreshMode(Enum):
    """Refresh modes for initial placeholder refresh."""
    ROOT_GLOBAL_CONFIG = auto()  # Root GlobalPipelineConfig - sibling inheritance only
    OTHER_WINDOW = auto()  # PipelineConfig, Step - live context from other windows


class InitialRefreshStrategy(EnumDispatchService[RefreshMode]):
    """
    Enum-driven dispatch for initial placeholder refresh.
    
    Eliminates complex boolean logic:
        is_root_global_config = (self.config.is_global_config_editing and
                                 self.global_config_type is not None and
                                 self.context_obj is None)
    
    Replaces with clean enum dispatch:
        mode = InitialRefreshStrategy.determine_mode(...)
        InitialRefreshStrategy.execute(manager, mode)
    """
    
    def __init__(self):
        super().__init__()
        self._register_handlers({
            RefreshMode.ROOT_GLOBAL_CONFIG: self._refresh_root_global_config,
            RefreshMode.OTHER_WINDOW: self._refresh_other_window,
        })
    
    def _determine_strategy(self, manager: Any, mode: RefreshMode = None) -> RefreshMode:
        """
        Determine refresh mode based on manager configuration.

        Args:
            manager: ParameterFormManager instance
            mode: Optional pre-determined mode (for dispatch compatibility)

        Returns:
            RefreshMode enum value
        """
        # If mode is pre-determined, use it
        if mode is not None:
            return mode

        # Check if this is a root GlobalPipelineConfig
        is_root_global_config = (
            manager.config.is_global_config_editing and
            manager.global_config_type is not None and
            manager.context_obj is None
        )

        if is_root_global_config:
            return RefreshMode.ROOT_GLOBAL_CONFIG
        else:
            return RefreshMode.OTHER_WINDOW
    
    def _refresh_root_global_config(self, manager: Any, mode: RefreshMode = None) -> None:
        """
        Refresh root GlobalPipelineConfig with sibling inheritance only.

        No live context from other windows - just resolve placeholders
        using sibling field values within the same config.
        """
        from openhcs.utils.performance_monitor import timer

        with timer("  Root global config sibling inheritance refresh", threshold_ms=10.0):
            # Refresh with None context (sibling inheritance only)
            manager._placeholder_refresh_service.refresh_all_placeholders(manager, None)

            # Refresh nested managers
            manager._apply_to_nested_managers(
                lambda name, mgr: mgr._placeholder_refresh_service.refresh_all_placeholders(mgr, None)
            )
    
    def _refresh_other_window(self, manager: Any, mode: RefreshMode = None) -> None:
        """
        Refresh PipelineConfig/Step with live context from other windows.

        This ensures new windows immediately show live values from other open windows.
        """
        from openhcs.utils.performance_monitor import timer

        with timer("  Initial live context refresh", threshold_ms=10.0):
            manager._refresh_with_live_context()
    
    @classmethod
    def execute(cls, manager: Any) -> None:
        """
        Execute the appropriate refresh strategy for the manager.
        
        Args:
            manager: ParameterFormManager instance
        """
        service = cls()
        mode = service._determine_strategy(manager)
        service.dispatch(manager, mode)

