"""Global window registry for scoped singleton windows with navigation support.

Ensures only one window per scope_id exists at a time and provides navigation
API for inheritance tracking (click field → open window + scroll to source).

Architecture:
- Centralized registry (like ObjectStateRegistry pattern)
- Singleton windows per scope_id
- Extensible navigation protocol
- Auto-cleanup on window close
- Fail-loud if window deleted but still in registry

Example Usage:

    # Basic: Show or focus existing window
    WindowManager.show_or_focus(
        scope_id="plate1",
        window_factory=lambda: ConfigWindow(...)
    )

    # Future: Navigate to specific field for inheritance tracking
    WindowManager.focus_and_navigate(
        scope_id="plate1",
        field_path="well_filter_config.well_filter"  # Scroll to this field
    )
"""

import logging
from typing import Dict, Callable, Optional, Protocol
from PyQt6.QtWidgets import QWidget

from openhcs.config_framework.object_state import ObjectStateRegistry

logger = logging.getLogger(__name__)


class NavigableWindow(Protocol):
    """Protocol for windows that support navigation to items/fields.

    Windows can optionally implement these methods to support navigation.
    """

    def select_and_scroll_to_item(self, item_id: str) -> None:
        """Select and scroll to item (e.g., list item, tab).

        Args:
            item_id: Identifier for the item to navigate to
        """
        ...

    def select_and_scroll_to_field(self, field_path: str) -> None:
        """Select and scroll to field (e.g., tree node, form widget).

        Args:
            field_path: Dotted path to field (e.g., "well_filter_config.well_filter")
        """
        ...


class WindowManager:
    """Global registry for scoped windows with navigation support.

    Ensures only one window per scope_id exists at a time.
    Provides navigation API for focusing windows and scrolling to items/fields.

    Patterns:
    - Singleton windows per scope (like ObjectStateRegistry for states)
    - Navigation protocol (optional methods, duck typing)
    - Auto-cleanup on close (no manual unregistration needed)
    - Fail-loud on stale references
    """

    # Global registry of open windows by scope_id
    _scoped_windows: Dict[str, QWidget] = {}

    @classmethod
    def show_or_focus(cls, scope_id: str, window_factory: Callable[[], QWidget]) -> QWidget:
        """Show window for scope_id. Reuse existing or create new.

        If window already exists for this scope_id, brings it to front.
        Otherwise, creates new window using factory and registers it.

        Auto-cleanup: Window is automatically unregistered when closed.

        Args:
            scope_id: Unique identifier for the window (e.g., plate path, step scope)
            window_factory: Callable that creates the window if needed

        Returns:
            The window (existing or newly created)

        Example:
            def create_config_window():
                return ConfigWindow(
                    config_class=PipelineConfig,
                    initial_config=current_config,
                    scope_id="plate1"
                )

            window = WindowManager.show_or_focus("plate1", create_config_window)
        """
        # Check if window exists and is still valid
        if scope_id in cls._scoped_windows:
            window = cls._scoped_windows[scope_id]
            try:
                # Test if window still exists (Qt doesn't auto-cleanup deleted widgets)
                # Note: Just accessing any property will raise RuntimeError if deleted
                _ = window.windowTitle()

                # Window exists - bring to front regardless of visibility
                # (window may be hidden, minimized, or still initializing - all valid states)
                if not window.isVisible():
                    window.show()

                window.raise_()
                window.activateWindow()

                # Restore if minimized
                if window.isMinimized():
                    window.showNormal()

                logger.debug(f"[WINDOW_MGR] Focused existing window for scope: {scope_id}")
                return window

            except RuntimeError:
                # Window was deleted but not cleaned from registry - fail loud
                logger.warning(f"[WINDOW_MGR] Stale window reference detected for scope: {scope_id}")
                del cls._scoped_windows[scope_id]

        # Create new window
        logger.debug(f"[WINDOW_MGR] Creating new window for scope: {scope_id}")
        window = window_factory()
        cls._scoped_windows[scope_id] = window

        # Auto-cleanup on close (hook into closeEvent)
        original_close = window.closeEvent if hasattr(window, 'closeEvent') else None

        def close_wrapper(event):
            # Unregister window before closing
            if scope_id in cls._scoped_windows:
                del cls._scoped_windows[scope_id]
                logger.debug(f"[WINDOW_MGR] Unregistered window on close: {scope_id}")

            # Call original closeEvent
            if original_close:
                original_close(event)

        window.closeEvent = close_wrapper

        # Show window
        window.show()
        logger.debug(f"[WINDOW_MGR] Registered and showed new window for scope: {scope_id}")
        return window

    @classmethod
    def focus_and_navigate(
        cls,
        scope_id: str,
        item_id: Optional[str] = None,
        field_path: Optional[str] = None
    ) -> bool:
        """Focus window and navigate to specific item/field.

        Brings window to front and optionally navigates to item/field.
        Navigation only works if window implements the navigation protocol.

        Args:
            scope_id: Window to focus
            item_id: Optional item to select (e.g., list index, tab name)
            field_path: Optional field to highlight (e.g., "well_filter_config.well_filter")

        Returns:
            True if window was found and focused, False otherwise

        Example:
            # Focus window and scroll to field (for inheritance tracking)
            WindowManager.focus_and_navigate(
                scope_id="plate1",
                field_path="well_filter_config.well_filter"
            )

            # Focus window and select item
            WindowManager.focus_and_navigate(
                scope_id="plate1::step_3",
                item_id="3"  # Select step 3 in list
            )
        """
        window = cls._scoped_windows.get(scope_id)
        if not window:
            logger.debug(f"[WINDOW_MGR] Cannot navigate - window not open for scope: {scope_id}")
            return False

        try:
            # Test if window still exists by accessing any property
            _ = window.windowTitle()

            # Ensure window is visible (may be hidden or still initializing)
            if not window.isVisible():
                window.show()

            # Bring window to front
            window.raise_()
            window.activateWindow()

            # Restore if minimized
            if window.isMinimized():
                window.showNormal()

            logger.debug(f"[WINDOW_MGR] Focused window for scope: {scope_id}")

            # Navigate to item if window supports it (duck typing)
            if item_id and hasattr(window, 'select_and_scroll_to_item'):
                logger.debug(f"[WINDOW_MGR] Navigating to item: {item_id}")
                window.select_and_scroll_to_item(item_id)

            # Navigate to field if window supports it (duck typing)
            if field_path and hasattr(window, 'select_and_scroll_to_field'):
                logger.debug(f"[WINDOW_MGR] Navigating to field: {field_path}")
                window.select_and_scroll_to_field(field_path)

            return True

        except RuntimeError:
            # Window was deleted - cleanup stale reference
            logger.warning(f"[WINDOW_MGR] Window deleted during navigation for scope: {scope_id}")
            del cls._scoped_windows[scope_id]
            return False

    @classmethod
    def register(cls, scope_id: str, window: QWidget) -> None:
        """Register a window for singleton tracking.

        Used by windows that manage their own show() behavior (e.g., BaseFormDialog).
        The window is responsible for calling this from its show() method.

        IMPORTANT: The window must call unregister() in its closeEvent to allow reopening.
        BaseFormDialog does this automatically.

        Args:
            scope_id: Unique identifier for the window
            window: The window to register

        Example:
            class MyWindow(QDialog):
                def show(self):
                    scope_key = f"{self.scope_id}::{self.__class__.__name__}"
                    if WindowManager.is_open(scope_key):
                        WindowManager.focus_and_navigate(scope_key)
                        return  # Don't show duplicate
                    WindowManager.register(scope_key, self)
                    super().show()

                def closeEvent(self, event):
                    WindowManager.unregister(scope_key)
                    super().closeEvent(event)
        """
        if scope_id in cls._scoped_windows:
            logger.warning(f"[WINDOW_MGR] Overwriting existing window for scope: {scope_id}")

        cls._scoped_windows[scope_id] = window

        # Eagerly create flash overlay so OpenGL context is ready before any flashes
        # This prevents first-paint glitches when GL initializes mid-render
        from pyqt_formgen.animation import WindowFlashOverlay
        WindowFlashOverlay.get_for_window(window)

        logger.debug(f"[WINDOW_MGR] Registered window for scope: {scope_id}")

    @classmethod
    def unregister(cls, scope_id: str) -> None:
        """Unregister a window from singleton tracking.

        Called by windows in their closeEvent to allow reopening.

        Args:
            scope_id: Scope to unregister
        """
        if scope_id in cls._scoped_windows:
            del cls._scoped_windows[scope_id]
            logger.debug(f"[WINDOW_MGR] Unregistered window: {scope_id}")

    @classmethod
    def is_open(cls, scope_id: str) -> bool:
        """Check if window is currently open and visible for scope_id.

        Args:
            scope_id: Scope to check

        Returns:
            True if window exists, is valid, AND is visible, False otherwise
        """
        if scope_id not in cls._scoped_windows:
            return False

        try:
            window = cls._scoped_windows[scope_id]
            is_visible = window.isVisible()
            if not is_visible:
                # Window was closed/hidden but not unregistered - clean up
                del cls._scoped_windows[scope_id]
                logger.debug(f"[WINDOW_MGR] Cleaned up closed window: {scope_id}")
                return False
            return True
        except RuntimeError:
            # Stale reference (C++ object deleted)
            del cls._scoped_windows[scope_id]
            return False

    @classmethod
    def close_window(cls, scope_id: str) -> bool:
        """Programmatically close window for scope_id.

        Args:
            scope_id: Scope to close

        Returns:
            True if window was found and closed, False otherwise
        """
        if scope_id not in cls._scoped_windows:
            return False

        try:
            window = cls._scoped_windows[scope_id]
            window.close()  # Triggers closeEvent → auto-cleanup
            return True
        except RuntimeError:
            # Already deleted
            del cls._scoped_windows[scope_id]
            return False

    @classmethod
    def get_open_scopes(cls) -> list[str]:
        """Get list of all currently open window scopes.

        Cleans up stale references as side effect.

        Returns:
            List of scope_ids for open windows
        """
        valid_scopes = []
        stale_scopes = []

        for scope_id, window in cls._scoped_windows.items():
            try:
                window.isVisible()
                valid_scopes.append(scope_id)
            except RuntimeError:
                stale_scopes.append(scope_id)

        # Cleanup stale references
        for scope_id in stale_scopes:
            del cls._scoped_windows[scope_id]
            logger.debug(f"[WINDOW_MGR] Cleaned up stale reference: {scope_id}")

        return valid_scopes

    # ========== Window Creation for Scope (Shared Infrastructure) ==========

    @classmethod
    def create_window_for_scope(cls, scope_id: str, object_state: Optional['ObjectState'] = None) -> Optional[QWidget]:
        """Create and show a window for the given scope_id.

        This is the single source of truth for scope→window creation.
        Used by both provenance navigation and time-travel restore.

        Scope ID format:
        - "" (empty string): GlobalPipelineConfig
        - "/path/to/plate": PipelineConfig for that plate
        - "/path/to/plate::step_N": DualEditorWindow → Step Settings tab
        - "/path/to/plate::step_N::func_M": DualEditorWindow → Function Pattern tab

        Args:
            scope_id: Scope identifier
            object_state: Optional ObjectState (used for time-travel to get object_instance)

        Returns:
            The created window, or None if creation failed
        """
        if scope_id == "":
            return cls._create_global_config_window()
        elif "::" not in scope_id:
            return cls._create_plate_config_window(scope_id)
        else:
            return cls._create_step_editor_window(scope_id, object_state)

    @classmethod
    def _create_global_config_window(cls) -> Optional[QWidget]:
        """Create GlobalPipelineConfig editor window."""
        from openhcs.pyqt_gui.windows.config_window import ConfigWindow
        from openhcs.core.config import GlobalPipelineConfig
        from openhcs.config_framework.global_config import get_current_global_config, set_global_config_for_editing

        current_config = get_current_global_config(GlobalPipelineConfig) or GlobalPipelineConfig()

        def handle_save(new_config):
            set_global_config_for_editing(GlobalPipelineConfig, new_config)
            logger.info("Global config saved via window")

        window = ConfigWindow(
            config_class=GlobalPipelineConfig,
            current_config=current_config,
            on_save_callback=handle_save,
            scope_id=""
        )
        window.show()
        window.raise_()
        window.activateWindow()
        return window

    @classmethod
    def _create_plate_config_window(cls, scope_id: str) -> Optional[QWidget]:
        """Create PipelineConfig editor window for a plate."""
        from openhcs.pyqt_gui.windows.config_window import ConfigWindow
        from openhcs.core.config import PipelineConfig

        plate_manager = cls._find_plate_manager()
        if not plate_manager:
            logger.warning("Could not find PlateManager for plate config window")
            return None

        orchestrator = plate_manager.orchestrators.get(scope_id)
        if not orchestrator:
            logger.warning(f"No orchestrator found for scope: {scope_id}")
            return None

        window = ConfigWindow(
            config_class=PipelineConfig,
            current_config=orchestrator.pipeline_config,
            on_save_callback=None,  # ObjectState handles save
            scope_id=scope_id
        )
        window.show()
        window.raise_()
        window.activateWindow()
        return window

    @classmethod
    def _create_step_editor_window(cls, scope_id: str, object_state: Optional['ObjectState'] = None) -> Optional[QWidget]:
        """Create DualEditorWindow for step or function scope.

        Args:
            scope_id: Step or function scope
            object_state: If provided, get step from object_instance (for time-travel)
        """
        from openhcs.pyqt_gui.windows.dual_editor_window import DualEditorWindow

        parts = scope_id.split("::")
        if len(parts) < 2:
            logger.warning(f"Invalid step scope_id format: {scope_id}")
            return None

        plate_path = parts[0]
        step_token = parts[1]
        is_function_scope = len(parts) >= 3
        step_scope_id = f"{parts[0]}::{parts[1]}"

        plate_manager = cls._find_plate_manager()
        if not plate_manager:
            logger.warning("Could not find PlateManager for step editor")
            return None

        orchestrator = plate_manager.orchestrators.get(plate_path)
        if not orchestrator:
            logger.warning(f"No orchestrator found for plate: {plate_path}")
            return None

        # Get step: from ObjectState if provided, else find by token
        step = None
        if object_state:
            # Time-travel: use object_instance directly
            if is_function_scope:
                # Function scope - get parent step's ObjectState
                from openhcs.config_framework.object_state import ObjectStateRegistry
                step_state = ObjectStateRegistry.get_by_scope(step_scope_id)
                step = step_state.object_instance if step_state else None
            else:
                step = object_state.object_instance

        if not step:
            # Provenance navigation: find by token
            step = cls._find_step_by_token(plate_manager, plate_path, step_token)

        if not step:
            logger.warning(f"Could not find step for scope: {scope_id}")
            return None

        window = DualEditorWindow(
            step_data=step,
            is_new=False,
            on_save_callback=None,  # ObjectState handles save
            orchestrator=orchestrator,
            parent=None
        )
        if is_function_scope and window.tab_widget:
            window.tab_widget.setCurrentIndex(1)

        window.show()
        window.raise_()
        window.activateWindow()
        return window

    @classmethod
    def _find_plate_manager(cls):
        """Find PlateManagerWidget from main window."""
        from PyQt6.QtWidgets import QApplication
        from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget

        for widget in QApplication.topLevelWidgets():
            if hasattr(widget, 'floating_windows'):
                plate_dialog = widget.floating_windows.get("plate_manager")
                if plate_dialog:
                    return plate_dialog.findChild(PlateManagerWidget)
        return None

    @classmethod
    def _find_step_by_token(cls, plate_manager, plate_path: str, step_token: str):
        """Find a step in the pipeline by its scope token."""
        # Get steps from Pipeline ObjectState instead of deprecated plate_pipelines
        pipeline_scope = f"{plate_path}::pipeline"
        pipeline_state = ObjectStateRegistry.get_by_scope(pipeline_scope)

        if not pipeline_state:
            logger.debug(f"No pipeline state for {plate_path}")
            return None

        step_scope_ids = pipeline_state.parameters.get("step_scope_ids") or []

        for scope_id in step_scope_ids:
            step_state = ObjectStateRegistry.get_by_scope(scope_id)
            if step_state:
                step = step_state.object_instance
                token = getattr(step, '_scope_token', None)
                if token == step_token:
                    return step
                token2 = getattr(step, '_pipeline_scope_token', None)
                if token2 == step_token:
                    return step

        logger.debug(f"Step token '{step_token}' not found in {len(step_scope_ids)} steps")
        return None
