"""OpenHCS adapters for pyqt-formgen provider protocols."""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Optional, Callable, Iterable, List, Dict

from PyQt6.QtWidgets import QWidget

from pyqt_formgen.protocols import (
    FormGenConfig,
    set_form_config,
    register_llm_service,
    register_codegen_provider,
    register_function_registry,
    register_preview_formatter,
    register_log_discovery_provider,
    register_server_scan_provider,
    register_window_factory,
    register_component_selection_provider,
    register_function_selection_provider,
)


@dataclass
class OpenHCSFormGenConfig(FormGenConfig):
    """OpenHCS-specific overrides for pyqt-formgen config."""

    log_dir: Optional[str] = None
    log_prefixes: List[str] = field(default_factory=lambda: ["openhcs_"])
    log_root_logger_name: Optional[str] = "openhcs"
    performance_logger_name: str = "openhcs.performance"
    performance_log_filename: str = "performance.log"
    path_cache_file: Optional[str] = None


class OpenHCSCodegenProvider:
    """Codegen provider backed by openhcs.debug.pickle_to_python."""

    def generate_complete_orchestrator_code(self, plate_paths, pipeline_data, global_config=None,
                                            per_plate_configs=None, pipeline_config=None, clean_mode=True) -> str:
        from openhcs.debug.pickle_to_python import generate_complete_orchestrator_code
        return generate_complete_orchestrator_code(
            plate_paths=plate_paths,
            pipeline_data=pipeline_data,
            global_config=global_config,
            pipeline_config=pipeline_config,
            per_plate_configs=per_plate_configs,
            clean_mode=clean_mode,
        )

    def generate_complete_pipeline_steps_code(self, pipeline_steps, clean_mode=True) -> str:
        from openhcs.debug.pickle_to_python import generate_complete_pipeline_steps_code
        return generate_complete_pipeline_steps_code(pipeline_steps, clean_mode=clean_mode)

    def generate_complete_function_pattern_code(self, func_obj, clean_mode=False) -> str:
        from openhcs.debug.pickle_to_python import generate_complete_function_pattern_code
        return generate_complete_function_pattern_code(func_obj, clean_mode=clean_mode)

    def generate_step_code(self, step_obj, clean_mode=True) -> str:
        from openhcs.debug.pickle_to_python import generate_step_code
        return generate_step_code(step_obj, clean_mode=clean_mode)

    def generate_config_code(self, config_obj, clean_mode=True, config_class: Optional[type] = None) -> str:
        from openhcs.debug.pickle_to_python import generate_config_code
        if config_class is None:
            config_class = type(config_obj)
        return generate_config_code(config_obj, config_class, clean_mode=clean_mode)


class OpenHCSFunctionRegistry:
    """Adapter for OpenHCS RegistryService."""

    def _get_metadata(self) -> Dict[str, Any]:
        from openhcs.processing.backends.lib_registry.registry_service import RegistryService
        return RegistryService.get_all_functions_with_metadata()

    def get_function_by_name(self, name: str) -> Optional[Callable]:
        metadata = self._get_metadata()
        if name in metadata:
            return metadata[name].func
        # Fallback: match by bare function name
        for meta in metadata.values():
            if meta.name == name or meta.original_name == name:
                return meta.func
        return None

    def get_all_functions(self) -> Dict[str, Callable]:
        return {key: meta.func for key, meta in self._get_metadata().items()}

    def get_function_metadata(self, name: str) -> Optional[Dict[str, Any]]:
        metadata = self._get_metadata()
        meta = metadata.get(name)
        if meta is None:
            # Try bare name match
            for m in metadata.values():
                if m.name == name or m.original_name == name:
                    meta = m
                    break
        if meta is None:
            return None
        return {
            "name": meta.name,
            "module": meta.module,
            "doc": meta.doc,
            "tags": list(meta.tags) if meta.tags else [],
            "registry_name": meta.get_registry_name(),
            "memory_type": meta.get_memory_type(),
        }


class OpenHCSLogDiscoveryProvider:
    """Adapter for OpenHCS log discovery utilities."""

    def get_current_log_path(self) -> Path:
        from openhcs.core.log_utils import get_current_log_file_path
        return Path(get_current_log_file_path())

    def discover_logs(self, base_log_path: Optional[str] = None, include_main_log: bool = True,
                      log_directory: Optional[Path] = None):
        from openhcs.core.log_utils import discover_logs
        from pyqt_formgen.core.log_utils import LogFileInfo

        logs = discover_logs(base_log_path=base_log_path, include_main_log=include_main_log,
                             log_directory=log_directory)
        # Convert to pyqt_formgen LogFileInfo for consistency
        converted = [
            LogFileInfo(path=l.path, log_type=l.log_type, worker_id=l.worker_id, display_name=l.display_name)
            for l in logs
        ]
        return converted


class OpenHCSServerScanProvider:
    """Scan OpenHCS ZMQ servers for log paths."""

    def scan_for_server_logs(self):
        from pathlib import Path
        import zmq
        import pickle

        from openhcs.core.config import get_all_streaming_ports
        from openhcs.constants.constants import CONTROL_PORT_OFFSET
        from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
        from zmqruntime.transport import get_zmq_transport_url, get_default_transport_mode
        from openhcs.core.log_utils import classify_log_file
        from pyqt_formgen.core.log_utils import LogFileInfo

        discovered = []
        ports_to_scan = get_all_streaming_ports(num_ports_per_type=10)

        def ping_server(port: int) -> dict:
            control_port = port + CONTROL_PORT_OFFSET
            try:
                context = zmq.Context()
                socket = context.socket(zmq.REQ)
                socket.setsockopt(zmq.LINGER, 0)
                socket.setsockopt(zmq.RCVTIMEO, 1000)

                transport_mode = get_default_transport_mode()
                control_url = get_zmq_transport_url(
                    control_port,
                    host="localhost",
                    mode=transport_mode,
                    config=OPENHCS_ZMQ_CONFIG,
                )
                socket.connect(control_url)

                socket.send(pickle.dumps({'type': 'ping'}))
                response = socket.recv()
                pong = pickle.loads(response)

                socket.close()
                context.term()
                return pong
            except Exception:
                return None

        for port in ports_to_scan:
            pong = ping_server(port)
            if pong and pong.get('log_file_path'):
                log_path = Path(pong['log_file_path'])
                if log_path.exists():
                    log_info = classify_log_file(log_path, None, False)
                    discovered.append(
                        LogFileInfo(path=log_info.path, log_type=log_info.log_type,
                                    worker_id=log_info.worker_id, display_name=log_info.display_name)
                    )
        return discovered


class OpenHCSComponentSelectionProvider:
    """Component selection provider backed by OpenHCS orchestrator metadata."""

    def get_groupby_enum(self) -> Any:
        from openhcs.constants.constants import GroupBy
        return GroupBy

    def _get_plate_manager(self):
        from PyQt6.QtWidgets import QApplication
        from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget

        for widget in QApplication.topLevelWidgets():
            if hasattr(widget, 'floating_windows'):
                plate_dialog = widget.floating_windows.get("plate_manager")
                if plate_dialog:
                    return plate_dialog.findChild(PlateManagerWidget)
        return None

    def _get_current_orchestrator(self):
        plate_manager = self._get_plate_manager()
        if not plate_manager:
            return None
        current_plate = plate_manager.selected_plate_path
        from objectstate import ObjectStateRegistry
        orchestrator = ObjectStateRegistry.get_object(current_plate)
        if orchestrator and orchestrator.is_initialized():
            return orchestrator
        return None

    def get_component_keys(self, group_by: Any) -> List[str]:
        orchestrator = self._get_current_orchestrator()
        if not orchestrator:
            return []
        return orchestrator.get_component_keys(group_by)

    def get_component_display_name(self, group_by: Any, component_key: str) -> Optional[str]:
        orchestrator = self._get_current_orchestrator()
        if not orchestrator:
            return None
        return orchestrator.metadata_cache.get_component_metadata(group_by, component_key)

    def select_components(self, available_components: Iterable[str], selected_components: Iterable[str],
                          group_by: Any, parent: Optional[Any] = None, **context: Any) -> Optional[List[str]]:
        from openhcs.pyqt_gui.dialogs.group_by_selector_dialog import GroupBySelectorDialog
        orchestrator = self._get_current_orchestrator()
        return GroupBySelectorDialog.select_components(
            available_components=list(available_components),
            selected_components=list(selected_components),
            group_by=group_by,
            orchestrator=orchestrator,
            parent=parent,
        )


class OpenHCSFunctionSelectionProvider:
    """Function selection provider backed by OpenHCS dialogs."""

    def select_function(self, parent: Optional[Any] = None, **context: Any) -> Optional[Callable]:
        from openhcs.pyqt_gui.dialogs.function_selector_dialog import FunctionSelectorDialog
        return FunctionSelectorDialog.select_function(parent=parent)


class OpenHCSWindowFactory:
    """Window factory for OpenHCS scope navigation."""

    def create_window_for_scope(self, scope_id: str, object_state: Optional[Any] = None) -> Optional[QWidget]:
        if scope_id == "":
            return self._create_global_config_window()
        if "::" not in scope_id:
            return self._create_plate_config_window(scope_id)
        return self._create_step_editor_window(scope_id, object_state)

    def _create_global_config_window(self) -> Optional[QWidget]:
        from openhcs.pyqt_gui.windows.config_window import ConfigWindow
        from openhcs.core.config import GlobalPipelineConfig
        from openhcs.config_framework.global_config import get_current_global_config, set_global_config_for_editing

        current_config = get_current_global_config(GlobalPipelineConfig) or GlobalPipelineConfig()

        def handle_save(new_config):
            set_global_config_for_editing(GlobalPipelineConfig, new_config)

        window = ConfigWindow(
            config_class=GlobalPipelineConfig,
            current_config=current_config,
            on_save_callback=handle_save,
            scope_id="",
        )
        window.show(); window.raise_(); window.activateWindow()
        return window

    def _create_plate_config_window(self, scope_id: str) -> Optional[QWidget]:
        from openhcs.pyqt_gui.windows.config_window import ConfigWindow
        from openhcs.core.config import PipelineConfig
        orchestrator = self._get_orchestrator(scope_id)
        if not orchestrator:
            return None
        window = ConfigWindow(
            config_class=PipelineConfig,
            current_config=orchestrator.pipeline_config,
            on_save_callback=None,
            scope_id=scope_id,
        )
        window.show(); window.raise_(); window.activateWindow()
        return window

    def _create_step_editor_window(self, scope_id: str, object_state: Optional[Any] = None) -> Optional[QWidget]:
        from openhcs.pyqt_gui.windows.dual_editor_window import DualEditorWindow
        from objectstate import ObjectStateRegistry

        parts = scope_id.split("::")
        if len(parts) < 2:
            return None

        plate_path = parts[0]
        step_token = parts[1]
        is_function_scope = len(parts) >= 3
        step_scope_id = f"{parts[0]}::{parts[1]}"

        orchestrator = self._get_orchestrator(plate_path)
        if not orchestrator:
            return None

        step = None
        if object_state:
            if is_function_scope:
                step_state = ObjectStateRegistry.get_by_scope(step_scope_id)
                step = step_state.object_instance if step_state else None
            else:
                step = object_state.object_instance

        if not step:
            step = self._find_step_by_token(plate_path, step_token)

        if not step:
            return None

        window = DualEditorWindow(
            step_data=step,
            is_new=False,
            on_save_callback=None,
            orchestrator=orchestrator,
            parent=None,
        )
        if is_function_scope and window.tab_widget:
            window.tab_widget.setCurrentIndex(1)

        window.show(); window.raise_(); window.activateWindow()
        return window

    def _get_orchestrator(self, plate_path: str):
        from objectstate import ObjectStateRegistry
        return ObjectStateRegistry.get_object(plate_path)

    def _get_plate_manager(self):
        from PyQt6.QtWidgets import QApplication
        from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget

        for widget in QApplication.topLevelWidgets():
            if hasattr(widget, 'floating_windows'):
                plate_dialog = widget.floating_windows.get("plate_manager")
                if plate_dialog:
                    return plate_dialog.findChild(PlateManagerWidget)
        return None

    def _find_step_by_token(self, plate_path: str, step_token: str):
        from objectstate import ObjectStateRegistry
        pipeline_scope = f"{plate_path}::pipeline"
        pipeline_state = ObjectStateRegistry.get_by_scope(pipeline_scope)
        if not pipeline_state:
            return None
        step_scope_ids = pipeline_state.parameters.get("step_scope_ids") or []
        for scope_id in step_scope_ids:
            step_state = ObjectStateRegistry.get_by_scope(scope_id)
            if step_state:
                step = step_state.object_instance
                if getattr(step, '_scope_token', None) == step_token:
                    return step
                if getattr(step, '_pipeline_scope_token', None) == step_token:
                    return step
        return None


def register_formgen_providers() -> None:
    """Register all OpenHCS providers with pyqt-formgen."""
    # FormGenConfig with OpenHCS paths
    config = OpenHCSFormGenConfig()
    try:
        from openhcs.core.xdg_paths import get_data_file_path
        config.path_cache_file = str(get_data_file_path("path_cache.json"))
    except Exception:
        config.path_cache_file = None

    # Log directory
    config.log_dir = str(Path.home() / ".local" / "share" / "openhcs" / "logs")

    # Jedi project paths (openhcs package + repo root if available)
    pkg_root = Path(__file__).resolve().parents[2]
    repo_root = pkg_root.parent if pkg_root.name == "openhcs" else pkg_root
    config.jedi_project_paths = [str(pkg_root), str(repo_root)]

    set_form_config(config)

    # Providers
    from openhcs.pyqt_gui.services.llm_pipeline_service import LLMPipelineService
    register_llm_service(LLMPipelineService())
    register_codegen_provider(OpenHCSCodegenProvider())
    register_function_registry(OpenHCSFunctionRegistry())
    register_log_discovery_provider(OpenHCSLogDiscoveryProvider())
    register_server_scan_provider(OpenHCSServerScanProvider())
    register_component_selection_provider(OpenHCSComponentSelectionProvider())
    register_function_selection_provider(OpenHCSFunctionSelectionProvider())
    register_window_factory(OpenHCSWindowFactory())

    # Preview formatters (OpenHCS-specific)
    try:
        from openhcs.core.config import WellFilterConfig
        from openhcs.pyqt_gui.widgets.config_preview_formatters import format_config_indicator

        def _format_config(config_obj, field_name: str) -> Optional[str]:
            return format_config_indicator(field_name, config_obj)

        register_preview_formatter(WellFilterConfig, _format_config)
    except Exception:
        pass
