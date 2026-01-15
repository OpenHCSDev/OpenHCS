"""OpenHCS-specific window factory for scope-aware window creation.

Implements WindowFactoryABC to provide openhcs-specific window creation logic
for global config, plate config, and step/function editor windows.
"""

import logging
from typing import Optional, Any

from PyQt6.QtWidgets import QWidget, QApplication

from pyqt_reactor.protocols import WindowFactoryABC
from objectstate import ObjectStateRegistry

logger = logging.getLogger(__name__)


class OpenHCSWindowFactory(WindowFactoryABC):
    """OpenHCS implementation of window factory.
    
    Handles scope_id formats:
    - "" (empty string): GlobalPipelineConfig
    - "__plates__": Root plate list state (no window)
    - "/path/to/plate": PipelineConfig for that plate
    - "/path/to/plate::step_N": DualEditorWindow → Step Settings tab
    - "/path/to/plate::step_N::func_M": DualEditorWindow → Function Pattern tab
    """

    def create_window_for_scope(self, scope_id: str, object_state: Optional[Any] = None) -> Optional[QWidget]:
        """Create and show a window for the given scope_id."""
        if scope_id == "":
            return self._create_global_config_window()
        elif scope_id == "__plates__":
            # __plates__ is the root plate list state - no window to create for it
            # Time-travel changes to the plate list are reflected in PlateManager automatically
            logger.debug(f"[WINDOW_FACTORY] Skipping window creation for __plates__ scope")
            return None
        elif "::" not in scope_id:
            return self._create_plate_config_window(scope_id)
        else:
            return self._create_step_editor_window(scope_id, object_state)

    def _create_global_config_window(self) -> Optional[QWidget]:
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

    def _create_plate_config_window(self, scope_id: str) -> Optional[QWidget]:
        """Create PipelineConfig editor window for a plate."""
        from openhcs.pyqt_gui.windows.config_window import ConfigWindow
        from openhcs.core.config import PipelineConfig

        plate_manager = self._find_plate_manager()
        if not plate_manager:
            logger.warning("Could not find PlateManager for plate config window")
            return None

        orchestrator = ObjectStateRegistry.get_object(scope_id)
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

    def _create_step_editor_window(self, scope_id: str, object_state: Optional[Any] = None) -> Optional[QWidget]:
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

        plate_manager = self._find_plate_manager()
        if not plate_manager:
            logger.warning("Could not find PlateManager for step editor")
            return None

        orchestrator = ObjectStateRegistry.get_object(plate_path)
        if not orchestrator:
            logger.warning(f"No orchestrator found for plate: {plate_path}")
            return None

        # Get step: from ObjectState if provided, else find by token
        step = None
        if object_state:
            # Time-travel: use object_instance directly
            if is_function_scope:
                # Function scope - get parent step's ObjectState
                step_state = ObjectStateRegistry.get_by_scope(step_scope_id)
                step = step_state.object_instance if step_state else None
            else:
                step = object_state.object_instance

        if not step:
            # Provenance navigation: find by token
            step = self._find_step_by_token(plate_manager, plate_path, step_token)

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

    def _find_plate_manager(self):
        """Find PlateManagerWidget from main window."""
        from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget

        for widget in QApplication.topLevelWidgets():
            if hasattr(widget, 'floating_windows'):
                plate_dialog = widget.floating_windows.get("plate_manager")
                if plate_dialog:
                    return plate_dialog.findChild(PlateManagerWidget)
        return None

    def _find_step_by_token(self, plate_manager, plate_path: str, step_token: str):
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

