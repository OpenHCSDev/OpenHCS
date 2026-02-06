"""OpenHCS thin wrapper over generic ZMQ server browser widget."""

from __future__ import annotations

import logging
from pathlib import Path
from typing import Any, Dict, List, Optional

from PyQt6.QtCore import QTimer, Qt, pyqtSlot
from PyQt6.QtWidgets import QTreeWidgetItem

from pyqt_reactive.services import (
    BaseServerInfo,
    DefaultServerInfoParser,
    ExecutionServerInfo,
    ServerInfoParserABC,
    ZMQServerScanService,
)
from pyqt_reactive.theming import StyleSheetGenerator
from pyqt_reactive.widgets.shared import (
    KillOperationPlan,
    TreeSyncAdapter,
    ZMQServerBrowserWidgetABC,
)
from zmqruntime.viewer_state import ViewerStateManager

from openhcs.core.progress import ProgressEvent, registry
from openhcs.pyqt_gui.widgets.shared.server_browser import (
    ProgressNode,
    ProgressTopologyState,
    ProgressTreeBuilder,
    ServerKillService,
    ServerRowPresenter,
    ServerTreePopulation,
    summarize_execution_server,
)

logger = logging.getLogger(__name__)


class ZMQServerManagerWidget(ZMQServerBrowserWidgetABC):
    """OpenHCS adapter for generic ZMQ browser UI + OpenHCS progress semantics."""

    def __init__(
        self,
        ports_to_scan: List[int],
        title: str = "ZMQ Servers",
        style_generator: Optional[StyleSheetGenerator] = None,
        server_info_parser: Optional[ServerInfoParserABC] = None,
        parent=None,
    ):
        if style_generator is None:
            raise RuntimeError("style_generator is required for ZMQServerManagerWidget")

        from openhcs.constants.constants import CONTROL_PORT_OFFSET
        from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

        parser = server_info_parser or DefaultServerInfoParser()
        scan_service = ZMQServerScanService(
            control_port_offset=CONTROL_PORT_OFFSET,
            config=OPENHCS_ZMQ_CONFIG,
            host="localhost",
        )
        super().__init__(
            ports_to_scan=ports_to_scan,
            title=title,
            style_generator=style_generator,
            scan_service=scan_service,
            server_info_parser=parser,
            parent=parent,
        )

        def _manager_callback(_instance) -> None:
            try:
                from PyQt6.QtCore import QMetaObject, Qt

                QMetaObject.invokeMethod(
                    self,
                    "_refresh_launching_viewers_only",
                    Qt.ConnectionType.QueuedConnection,
                )
            except Exception as error:
                logger.debug("Viewer state callback invocation failed: %s", error)

        mgr = ViewerStateManager.get_instance()
        mgr.register_state_callback(_manager_callback)
        self._viewer_state_callback = _manager_callback
        self._viewer_state_callback_registered = True

        self._progress_tracker = registry()
        self._registry_listener = self._on_registry_event
        self._progress_tracker.add_listener(self._registry_listener)
        self._registry_listener_registered = True
        self._topology_state = ProgressTopologyState()
        self._known_wells = self._topology_state.known_wells
        self._worker_assignments = self._topology_state.worker_assignments
        self._seen_execution_ids = self._topology_state.seen_execution_ids

        self._zmq_client = None
        self._progress_dirty = False
        from openhcs.pyqt_gui.config import ProgressUIConfig

        self._progress_coalesce_timer = QTimer()
        self._progress_coalesce_timer.timeout.connect(self._coalesced_progress_update)
        self._progress_coalesce_timer.start(ProgressUIConfig().update_interval_ms)

        self._tree_sync_adapter = TreeSyncAdapter()
        self._progress_tree_builder = ProgressTreeBuilder()
        self._server_kill_service = ServerKillService()
        self._server_row_presenter = ServerRowPresenter(
            create_tree_item=self._create_tree_item,
            update_execution_server_item=self._update_execution_server_item,
            log_warning=logger.warning,
        )
        self._server_tree_population = ServerTreePopulation(
            create_tree_item=self._create_tree_item,
            render_server=self._server_row_presenter.render_server,
            populate_server_children=self._server_row_presenter.populate_server_children,
            server_info_parser=self._server_info_parser,
            ping_server=self._ping_server,
            progress_tracker=self._progress_tracker,
            ports_to_scan=self.ports_to_scan,
            last_known_servers=self._last_known_servers,
            log_info=logger.info,
            log_debug=logger.debug,
        )

    def _populate_tree(self, parsed_servers: List[BaseServerInfo]) -> None:
        self._server_tree_population.populate_tree(
            tree=self.server_tree,
            parsed_servers=parsed_servers,
        )

    def _periodic_domain_cleanup(self) -> None:
        removed = self._progress_tracker.cleanup_old_executions()
        if removed > 0:
            logger.info(f"Periodic cleanup: removed {removed} old completed executions")

    def _kill_ports_with_plan(
        self,
        *,
        ports: List[int],
        plan: KillOperationPlan,
        on_server_killed,
    ) -> tuple[bool, str]:
        return self._server_kill_service.kill_ports(
            ports=ports,
            plan=plan,
            on_server_killed=on_server_killed,
            log_info=logger.info,
            log_warning=logger.warning,
            log_error=logger.error,
        )

    def _on_browser_shown(self) -> None:
        self._setup_progress_client()

    def _on_browser_hidden(self) -> None:
        if self._zmq_client is not None:
            self._zmq_client.disconnect()
            self._zmq_client = None

    def _on_browser_cleanup(self) -> None:
        if self._progress_coalesce_timer is not None:
            self._progress_coalesce_timer.stop()
            self._progress_coalesce_timer.deleteLater()
            self._progress_coalesce_timer = None

        if self._zmq_client is not None:
            try:
                self._zmq_client.disconnect()
            except Exception as error:
                logger.warning("Failed to disconnect ZMQ client during cleanup: %s", error)
            self._zmq_client = None

        if self._viewer_state_callback_registered:
            mgr = ViewerStateManager.get_instance()
            if self._viewer_state_callback:
                mgr.unregister_state_callback(self._viewer_state_callback)
            self._viewer_state_callback_registered = False

        if self._registry_listener_registered:
            removed = self._progress_tracker.remove_listener(self._registry_listener)
            if not removed:
                raise RuntimeError(
                    "ZMQServerManagerWidget listener removal failed: listener not registered"
                )
            self._registry_listener_registered = False

        for execution_id in list(self._seen_execution_ids):
            self._progress_tracker.clear_execution(execution_id)
            self._topology_state.clear_execution(execution_id)
        self._topology_state.clear_all()

    def _setup_progress_client(self) -> None:
        from openhcs.runtime.zmq_execution_client import ZMQExecutionClient

        if self._zmq_client is not None:
            try:
                self._zmq_client.disconnect()
            except Exception as error:
                logger.warning("Failed to disconnect existing ZMQ client: %s", error)
            self._zmq_client = None

        try:
            self._zmq_client = ZMQExecutionClient(
                port=7777,
                persistent=True,
                progress_callback=self._on_progress,
            )
            connected = self._zmq_client.connect(timeout=1)
            if not connected:
                self._zmq_client = None
                return
            self._zmq_client._start_progress_listener()
        except Exception as error:
            logger.warning("Failed to connect to execution server: %s", error)
            self._zmq_client = None

    def _on_progress(self, message: dict) -> None:
        event = ProgressEvent.from_dict(message)
        self._topology_state.register_event(event)
        self._progress_tracker.register_event(event.execution_id, event)
        self._progress_dirty = True

    def _on_registry_event(self, _execution_id: str, _event: ProgressEvent) -> None:
        """Refresh from shared registry updates, regardless of producer client."""
        self._progress_dirty = True

    @pyqtSlot()
    def _coalesced_progress_update(self) -> None:
        if not self._progress_dirty:
            return
        self._progress_dirty = False
        self._update_tree_with_progress()

    @pyqtSlot()
    def _update_tree_with_progress(self) -> None:
        try:
            for index in range(self.server_tree.topLevelItemCount()):
                item = self.server_tree.topLevelItem(index)
                if item is None:
                    continue
                data = item.data(0, Qt.ItemDataRole.UserRole)
                if not data:
                    continue
                server_name = data.get("server", "")
                if server_name.endswith("ExecutionServer"):
                    self._update_execution_server_item(item, data)
                    return
        except Exception as error:
            logger.exception("Error updating tree with progress: %s", error)

    def _get_plate_name(self, plate_id: str, exec_id: str | None = None) -> str:
        plate_leaf = Path(plate_id).name
        if exec_id:
            return f"{plate_leaf} ({exec_id[:8]})"
        return plate_leaf

    def _build_progress_tree(self, executions: Dict[str, list]) -> List[ProgressNode]:
        return self._progress_tree_builder.build_progress_tree(
            executions=executions,
            worker_assignments=self._worker_assignments,
            known_wells=self._known_wells,
            get_plate_name=self._get_plate_name,
        )

    def _update_execution_server_item(
        self, server_item: QTreeWidgetItem, server_data: dict
    ) -> None:
        try:
            executions = {
                execution_id: self._progress_tracker.get_events(execution_id)
                for execution_id in self._progress_tracker.get_execution_ids()
            }

            parsed_server_info = self._server_info_parser.parse(server_data)
            if not isinstance(parsed_server_info, ExecutionServerInfo):
                raise ValueError(
                    "Expected ExecutionServerInfo for execution subtree update, "
                    f"got {type(parsed_server_info).__name__}"
                )

            nodes = self._build_progress_tree(executions) if executions else []
            nodes = self._merge_server_snapshot_nodes(nodes, parsed_server_info)
            if not nodes:
                server_item.setText(1, "✅ Idle")
                server_item.setText(2, "")
                self._tree_sync_adapter.sync_children(server_item, [])
                return

            summary = summarize_execution_server(nodes)
            server_item.setText(1, summary.status_text)
            server_item.setText(2, summary.info_text)
            self._tree_sync_adapter.sync_children(
                server_item,
                self._progress_tree_builder.to_tree_nodes(nodes),
            )
        except Exception as error:
            logger.exception("Error updating execution server item: %s", error)

    def _merge_server_snapshot_nodes(
        self, nodes: List[ProgressNode], server_info: ExecutionServerInfo
    ) -> List[ProgressNode]:
        by_plate_id: Dict[str, ProgressNode] = {node.node_id: node for node in nodes}
        compile_status = server_info.compile_status
        is_compile_active = (
            compile_status is not None
            and not compile_status.is_success
            and not compile_status.is_failed
        )
        running_status = "⏳ Compiling" if is_compile_active else "⚙️ Executing"

        for running in server_info.running_execution_entries:
            plate_id = running.plate_id
            execution_id = running.execution_id
            existing = by_plate_id.get(plate_id)

            if existing is None:
                plate_name = self._get_plate_name(plate_id, execution_id)
                node = ProgressNode(
                    node_id=plate_id,
                    node_type="plate",
                    label=f"📋 {plate_name}",
                    status=running_status,
                    info="0.0%",
                    percent=0.0,
                    children=[],
                )
                nodes.append(node)
                by_plate_id[plate_id] = node
                continue

            # Progress-derived nodes are authoritative when present.
            if not existing.children:
                existing.status = running_status
                if existing.percent <= 0.0:
                    existing.info = "0.0%"

        for queued in server_info.queued_execution_entries:
            plate_id = queued.plate_id
            execution_id = queued.execution_id
            queue_suffix = f" (q#{queued.queue_position})"
            existing = by_plate_id.get(plate_id)

            if existing is None:
                plate_name = self._get_plate_name(plate_id, execution_id)
                node = ProgressNode(
                    node_id=plate_id,
                    node_type="plate",
                    label=f"📋 {plate_name}",
                    status="⏳ Queued",
                    info=f"0.0%{queue_suffix}",
                    percent=0.0,
                    children=[],
                )
                nodes.append(node)
                by_plate_id[plate_id] = node
                continue

            if existing.status in {"✅ Compiled", "⏳ Compiling", "⏳ Queued"}:
                existing.status = "⏳ Queued"
                existing.percent = 0.0
                existing.info = f"0.0%{queue_suffix}"
                existing.children = []

        return nodes

    def _create_tree_item(
        self, display: str, status: str, info: str, data: dict
    ) -> QTreeWidgetItem:
        item = QTreeWidgetItem([display, status, info])
        item.setData(0, Qt.ItemDataRole.UserRole, data)
        return item

    @pyqtSlot()
    def _refresh_launching_viewers_only(self) -> None:
        if self._is_cleaning_up:
            return
        self._update_server_list(self.servers)
