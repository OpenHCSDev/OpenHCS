"""
Form build orchestration service.

Consolidates the complex async/sync widget creation logic and post-build callback sequences
into a single, parameterized orchestrator.

Key features:
1. Unified async/sync widget creation paths
2. Automatic nested manager tracking
3. Ordered callback execution (styling → placeholders → enabled styling)
4. Root vs nested manager handling
5. Performance monitoring integration

Pattern:
    Instead of:
        if async:
            # ... 50 lines of async logic
            def on_complete():
                # ... 30 lines of callback sequence
        else:
            # ... 30 lines of sync logic (duplicate callback sequence)
    
    Use:
        orchestrator.build_form(manager, content_layout, params, use_async=True/False)
"""

from typing import List, Callable, Optional, Any
from PyQt6.QtWidgets import QVBoxLayout, QWidget
from dataclasses import dataclass
from enum import Enum
import logging

logger = logging.getLogger(__name__)


class BuildPhase(Enum):
    """Phases of form building process."""
    WIDGET_CREATION = "widget_creation"
    STYLING_CALLBACKS = "styling_callbacks"
    PLACEHOLDER_REFRESH = "placeholder_refresh"
    POST_PLACEHOLDER_CALLBACKS = "post_placeholder_callbacks"
    ENABLED_STYLING = "enabled_styling"


@dataclass
class BuildConfig:
    """Configuration for form building."""
    initial_sync_widgets: int = 5  # Number of widgets to create synchronously before going async
    use_async_threshold: int = 5   # Use async if param count > this


class FormBuildOrchestrator:
    """
    Orchestrates form building with unified async/sync paths.
    
    This service eliminates the massive duplication between async and sync widget creation
    by parameterizing the build process and extracting the common callback sequence.
    
    Examples:
        # Async build:
        orchestrator.build_widgets(manager, layout, params, use_async=True)
        
        # Sync build:
        orchestrator.build_widgets(manager, layout, params, use_async=False)
    """
    
    def __init__(self, config: BuildConfig = None):
        self.config = config or BuildConfig()
    
    @staticmethod
    def is_root_manager(manager) -> bool:
        """Check if manager is root (not nested)."""
        return manager._parent_manager is None
    
    @staticmethod
    def is_nested_manager(manager) -> bool:
        """Check if manager is nested."""
        return manager._parent_manager is not None
    
    def build_widgets(self, manager, content_layout: QVBoxLayout, 
                     param_infos: List[Any], use_async: bool) -> None:
        """
        Build widgets using unified async/sync path.
        
        Args:
            manager: ParameterFormManager instance
            content_layout: Layout to add widgets to
            param_infos: List of parameter info objects
            use_async: Whether to use async widget creation
        """
        from openhcs.utils.performance_monitor import timer
        
        if use_async:
            self._build_widgets_async(manager, content_layout, param_infos)
        else:
            self._build_widgets_sync(manager, content_layout, param_infos)
    
    def _build_widgets_sync(self, manager, content_layout: QVBoxLayout,
                           param_infos: List[Any]) -> None:
        """Synchronous widget creation path."""
        from openhcs.utils.performance_monitor import timer
        from openhcs.ui.shared.parameter_info_types import DirectDataclassInfo, OptionalDataclassInfo

        # Create all widgets synchronously
        with timer(f"      Create {len(param_infos)} parameter widgets", threshold_ms=5.0):
            for param_info in param_infos:
                is_nested = isinstance(param_info, (DirectDataclassInfo, OptionalDataclassInfo))
                with timer(f"        Create widget for {param_info.name} ({'nested' if is_nested else 'regular'})", threshold_ms=2.0):
                    widget = manager._create_widget_for_param(param_info)
                    content_layout.addWidget(widget)
        
        # Execute post-build sequence
        self._execute_post_build_sequence(manager)
    
    def _build_widgets_async(self, manager, content_layout: QVBoxLayout, 
                            param_infos: List[Any]) -> None:
        """Asynchronous widget creation path."""
        from openhcs.utils.performance_monitor import timer
        
        # Initialize pending nested managers tracking (root only)
        if self.is_root_manager(manager):
            manager._pending_nested_managers = {}
        
        # Split into sync and async batches
        sync_params = param_infos[:self.config.initial_sync_widgets]
        async_params = param_infos[self.config.initial_sync_widgets:]
        
        # Create initial widgets synchronously
        if sync_params:
            with timer(f"        Create {len(sync_params)} initial widgets (sync)", threshold_ms=5.0):
                for param_info in sync_params:
                    widget = manager._create_widget_for_param(param_info)
                    content_layout.addWidget(widget)
            
            # Initial placeholder refresh for fast visual feedback
            # CRITICAL: Use refresh_with_live_context to collect current form + sibling values
            with timer(f"        Initial placeholder refresh ({len(sync_params)} widgets)", threshold_ms=5.0):
                manager._placeholder_refresh_service.refresh_with_live_context(manager)
        
        # Define completion callback
        def on_async_complete():
            """Called when all async widgets are created."""
            if self.is_nested_manager(manager):
                # Nested manager - notify root
                self._notify_root_of_completion(manager)
            else:
                # Root manager - check if all nested managers done
                if len(manager._pending_nested_managers) == 0:
                    self._execute_post_build_sequence(manager)
        
        # Create remaining widgets asynchronously
        if async_params:
            manager._create_widgets_async(content_layout, async_params, on_complete=on_async_complete)
        else:
            # All widgets were sync, call completion immediately
            on_async_complete()
    
    def _notify_root_of_completion(self, nested_manager) -> None:
        """Notify root manager that nested manager completed async build."""
        # Find root manager
        root_manager = nested_manager._parent_manager
        while root_manager._parent_manager is not None:
            root_manager = root_manager._parent_manager
        
        # Notify root
        root_manager._on_nested_manager_complete(nested_manager)
    
    def _execute_post_build_sequence(self, manager) -> None:
        """
        Execute the standard post-build callback sequence.
        
        This is the SINGLE SOURCE OF TRUTH for the build completion sequence.
        Order matters: styling → placeholders → post-placeholder → enabled styling
        
        Args:
            manager: ParameterFormManager instance
        """
        from openhcs.utils.performance_monitor import timer
        
        # Only root managers execute the full sequence
        if self.is_nested_manager(manager):
            # Nested managers just apply their build callbacks
            for callback in manager._on_build_complete_callbacks:
                callback()
            manager._on_build_complete_callbacks.clear()
            return
        
        # STEP 1: Apply styling callbacks (optional dataclass None-state dimming)
        with timer("  Apply styling callbacks", threshold_ms=5.0):
            self._apply_callbacks(manager._on_build_complete_callbacks)
        
        # STEP 2: Refresh placeholders (resolve inherited values)
        # CRITICAL: Use refresh_with_live_context to collect current form + sibling values
        with timer("  Complete placeholder refresh", threshold_ms=10.0):
            manager._placeholder_refresh_service.refresh_with_live_context(manager)

        # STEP 3: Apply post-placeholder callbacks (enabled styling that needs resolved values)
        with timer("  Apply post-placeholder callbacks", threshold_ms=5.0):
            self._apply_callbacks(manager._on_placeholder_refresh_complete_callbacks)
            for nested_manager in manager.nested_managers.values():
                self._apply_callbacks(nested_manager._on_placeholder_refresh_complete_callbacks)

        # STEP 4: Refresh enabled styling (after placeholders are resolved)
        with timer("  Enabled styling refresh", threshold_ms=5.0):
            manager._apply_to_nested_managers(lambda name, mgr: mgr._enabled_field_styling_service.refresh_enabled_styling(mgr))
    
    @staticmethod
    def _apply_callbacks(callback_list: List[Callable]) -> None:
        """Apply all callbacks in list and clear it."""
        for callback in callback_list:
            callback()
        callback_list.clear()
    
    def should_use_async(self, param_count: int) -> bool:
        """Determine if async widget creation should be used."""
        return param_count > self.config.use_async_threshold

