"""
Generic ZMQ Server Manager Widget for PyQt6.

Provides a reusable UI component for managing any ZMQ server (execution servers,
Napari viewers, future servers) using the ZMQServer/ZMQClient ABC interface.

Features:
- Auto-discovery of running servers via port scanning
- Display server info (port, type, status, log file)
- Graceful shutdown and force kill
- Double-click to open log files
- Works with ANY ZMQServer subclass
- Tracks launching viewers with queued image counts
- Real-time pipeline progress updates for execution servers
"""

import logging
from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum, auto
from functools import singledispatchmethod
from pathlib import Path
from typing import List, Dict, Any, Optional, Union, Protocol
from PyQt6.QtWidgets import (
    QWidget,
    QVBoxLayout,
    QHBoxLayout,
    QTreeWidget,
    QTreeWidgetItem,
    QPushButton,
    QGroupBox,
    QMessageBox,
    QAbstractItemView,
    QLabel,
    QSplitter,
    QFrame,
)
from PyQt6.QtCore import Qt, pyqtSignal, pyqtSlot, QTimer
from PyQt6.QtGui import QFont
import time
from pyqt_reactive.theming import StyleSheetGenerator
import threading
from objectstate import spawn_thread_with_context
from zmqruntime.viewer_state import ViewerStateManager, ViewerState
from zmqruntime.messages import WorkerState

from openhcs.pyqt_gui.widgets.shared.progress_state import (
    ExecutionProgressTracker,
    AxisPhase,
)

logger = logging.getLogger(__name__)


# Application-specific types (OpenHCS compilation status)
@dataclass(frozen=True)
class CompileStatus:
    """OpenHCS compilation status - application specific."""

    is_success: bool
    is_failed: bool
    message: str

    @classmethod
    def from_response(
        cls, compile_status_str: str, compile_message: str
    ) -> "CompileStatus":
        status_str = compile_status_str.lower()
        return cls(
            is_success="success" in status_str,
            is_failed="failed" in status_str,
            message=compile_message,
        )

    @classmethod
    def from_dict(cls, data: dict) -> Optional["CompileStatus"]:
        compile_status_str = data.get("compile_status", "")
        compile_message = data.get("compile_message", "")
        # Return None if no compile status present
        if not compile_status_str:
            return None
        return cls.from_response(compile_status_str, compile_message)


# ============================================================================
# Typed Server Data Structures - Proper Type Safety
# ============================================================================


class ServerKind(Enum):
    """Server kind enum for type-safe dispatch."""

    EXECUTION = auto()
    NAPARI = auto()
    FIJI = auto()
    GENERIC = auto()


@dataclass(frozen=True)
class BaseServerInfo(ABC):
    """Base class for server information."""

    raw: dict
    port: int
    ready: bool
    log_file: Optional[str]

    @classmethod
    @abstractmethod
    def from_dict(cls, data: dict) -> "BaseServerInfo":
        """Parse from ping response dict."""
        pass

    @property
    @abstractmethod
    def kind(self) -> ServerKind:
        """Server kind for dispatch."""
        pass


@dataclass(frozen=True)
class ExecutionServerInfo(BaseServerInfo):
    """Execution server specific information."""

    workers: tuple[WorkerState, ...] = ()
    compile_status: Optional[CompileStatus] = None
    running_executions: tuple[str, ...] = ()

    @classmethod
    def from_dict(cls, data: dict) -> "ExecutionServerInfo":
        # Extract execution IDs from running_executions list of dicts
        running_execs = data.get("running_executions", [])
        execution_ids = tuple(exec_info["execution_id"] for exec_info in running_execs)

        return cls(
            raw=data,
            port=data["port"],
            ready=data["ready"],
            log_file=data.get("log_file_path"),
            workers=tuple(WorkerState.from_dict(w) for w in data.get("workers", [])),
            compile_status=CompileStatus.from_dict(data),
            running_executions=execution_ids,
        )

    @property
    def kind(self) -> ServerKind:
        return ServerKind.EXECUTION


@dataclass(frozen=True)
class ViewerServerInfo(BaseServerInfo):
    """Viewer server (Napari/Fiji) information."""

    server_kind: ServerKind
    memory_mb: Optional[float] = None
    cpu_percent: Optional[float] = None

    @classmethod
    def from_dict(cls, data: dict, kind: ServerKind) -> "ViewerServerInfo":
        return cls(
            raw=data,
            port=data["port"],
            ready=data["ready"],
            server_kind=kind,
            log_file=data.get("log_file_path"),
            memory_mb=data.get("memory_mb"),
            cpu_percent=data.get("cpu_percent"),
        )

    @property
    def kind(self) -> ServerKind:
        return self.server_kind


@dataclass(frozen=True)
class GenericServerInfo(BaseServerInfo):
    """Fallback for unknown server types."""

    server_name: str

    @classmethod
    def from_dict(cls, data: dict) -> "GenericServerInfo":
        return cls(
            raw=data,
            port=data["port"],
            ready=data["ready"],
            server_name=data.get("server", "Unknown"),
            log_file=data.get("log_file_path"),
        )

    @property
    def kind(self) -> ServerKind:
        return ServerKind.GENERIC


def parse_server_info(data: dict) -> BaseServerInfo:
    """Parse server ping response into typed server info."""
    server_name = data.get("server", "")

    # Dispatch based on actual server class/type
    if server_name.endswith("ExecutionServer"):
        return ExecutionServerInfo.from_dict(data)
    elif "Napari" in server_name:
        return ViewerServerInfo.from_dict(data, ServerKind.NAPARI)
    elif "Fiji" in server_name:
        return ViewerServerInfo.from_dict(data, ServerKind.FIJI)
    else:
        return GenericServerInfo.from_dict(data)


# Global reference to active ZMQ server manager widgets (for triggering refreshes)
_active_managers_lock = threading.Lock()
_active_managers: List["ZMQServerManagerWidget"] = []


class ZMQServerManagerWidget(QWidget):
    """
    Generic ZMQ server manager widget.

    Works with any ZMQServer subclass via the ABC interface.
    Displays running servers and provides management controls.
    """

    # Signals
    server_killed = pyqtSignal(int)  # Emitted when server is killed (port)
    log_file_opened = pyqtSignal(str)  # Emitted when log file is opened (path)
    _scan_complete = pyqtSignal(list)  # Internal signal for async scan completion
    _kill_complete = pyqtSignal(
        bool, str
    )  # Internal signal for async kill completion (success, message)
    _progress_update = (
        pyqtSignal()
    )  # Internal signal for progress updates (thread-safe)

    def __init__(
        self,
        ports_to_scan: List[int],
        title: str = "ZMQ Servers",
        style_generator: Optional[StyleSheetGenerator] = None,
        parent: Optional[QWidget] = None,
    ):
        """
        Initialize ZMQ server manager widget.

        Args:
            ports_to_scan: List of ports to scan for servers
            title: Title for the group box
            style_generator: Style generator for consistent styling
            parent: Parent widget
        """
        super().__init__(parent)

        self.ports_to_scan = ports_to_scan
        self.title = title
        self.style_generator = style_generator

        # Server tracking
        self.servers: List[Dict[str, Any]] = []
        self._last_known_servers: Dict[int, Dict[str, Any]] = {}  # {port: server_info}

        # Register this manager for launching viewer updates
        with _active_managers_lock:
            _active_managers.append(self)

        # Register a ViewerStateManager callback so the UI updates immediately
        # when viewer state changes. This is required for the hard migration.
        def _manager_callback(instance):
            # Forward to the UI thread using invokeMethod
            try:
                from PyQt6.QtCore import QMetaObject, Qt

                QMetaObject.invokeMethod(
                    self,
                    "_refresh_launching_viewers_only",
                    Qt.ConnectionType.QueuedConnection,
                )
            except Exception:
                pass

        mgr = ViewerStateManager.get_instance()
        mgr.register_state_callback(_manager_callback)
        self._viewer_state_callback = _manager_callback

        # Connect internal signal for async scanning
        self._scan_complete.connect(self._update_server_list)
        self._progress_update.connect(self._update_tree_with_progress)

        # Auto-refresh timer (async scanning won't block UI)
        self.refresh_timer = QTimer()
        self.refresh_timer.timeout.connect(self.refresh_servers)

        # Cleanup timer (remove completed executions every 1 second)
        self._cleanup_timer = QTimer()
        self._cleanup_timer.timeout.connect(self._periodic_cleanup)
        self._cleanup_timer.start(1000)  # Check every second

        # Use shared ExecutionProgressTracker singleton (shared with Plate Manager)
        self._progress_tracker = ExecutionProgressTracker.get_instance()

        # Linger tracking: keep completed plates visible for delay before removal
        self._linger_seconds = 5  # Keep completed items for 5 seconds
        self._lingered_plates: Dict[
            str, tuple
        ] = {}  # plate_id -> (plate_data, timestamp)
        self._spawned_plates: Dict[str, float] = {}  # plate_id -> spawn_timestamp
        self._last_seen_plate_data: Dict[
            str, dict
        ] = {}  # plate_id -> last_seen_plate_data (cache for display)

        # Linger cleanup timer
        self._linger_cleanup_timer = QTimer()
        self._linger_cleanup_timer.timeout.connect(self._cleanup_lingered_plates)
        self._linger_cleanup_timer.start(1000)  # Check every second

        # ZMQ Execution Client (like Plate Manager)
        self._zmq_client = None

        # Cleanup flag to prevent operations after cleanup
        self._is_cleaning_up = False

        self.setup_ui()

    def cleanup(self):
        """Cleanup resources before widget destruction."""
        if self._is_cleaning_up:
            return

        self._is_cleaning_up = True

        # Stop refresh timer first to prevent new refresh calls
        if hasattr(self, "refresh_timer") and self.refresh_timer:
            self.refresh_timer.stop()
            self.refresh_timer.deleteLater()
            self.refresh_timer = None

        # Stop cleanup timer
        if hasattr(self, "_cleanup_timer") and self._cleanup_timer:
            self._cleanup_timer.stop()
            self._cleanup_timer.deleteLater()
            self._cleanup_timer = None

        # Stop linger cleanup timer
        if hasattr(self, "_linger_cleanup_timer") and self._linger_cleanup_timer:
            self._linger_cleanup_timer.stop()
            self._linger_cleanup_timer.deleteLater()
            self._linger_cleanup_timer = None

        # Disconnect ZMQ client (this will stop the progress listener thread automatically)
        if self._zmq_client:
            try:
                self._zmq_client.disconnect()
            except:
                pass
            self._zmq_client = None

        # Unregister this manager from global list
        with _active_managers_lock:
            if self in _active_managers:
                _active_managers.remove(self)

        # Unregister viewer state callback
        try:
            mgr = ViewerStateManager.get_instance()
            if getattr(self, "_viewer_state_callback", None):
                mgr.unregister_state_callback(self._viewer_state_callback)
        except Exception:
            # Hard migration: ViewerStateManager should be present; ignore failures
            pass

        # Clear progress tracking (using shared tracker)
        self._progress_tracker.clear()

        logger.debug("ZMQServerManagerWidget cleanup completed")

    def __del__(self):
        """Cleanup when widget is destroyed."""
        self.cleanup()

    def showEvent(self, a0):
        """Auto-scan for servers when widget is shown."""
        super().showEvent(a0)
        if not self._is_cleaning_up:
            # Scan for servers on first show
            self.refresh_servers()
            # Start auto-refresh (1 second interval - async scanning won't block UI)
            if self.refresh_timer:
                self.refresh_timer.start(1000)
            # Setup progress client (like Plate Manager)
            self._setup_progress_client()

    def hideEvent(self, a0):
        """Stop auto-refresh when widget is hidden."""
        super().hideEvent(a0)
        # Stop timers to prevent unnecessary background work
        if hasattr(self, "refresh_timer") and self.refresh_timer:
            self.refresh_timer.stop()
        # Disconnect ZMQ client
        if self._zmq_client:
            self._zmq_client.disconnect()
            self._zmq_client = None

    def setup_ui(self):
        """Setup the user interface with AbstractManagerWidget-like styling."""
        main_layout = QVBoxLayout(self)
        main_layout.setContentsMargins(2, 2, 2, 2)
        main_layout.setSpacing(2)

        # Header (title + status) - similar to AbstractManagerWidget
        header = self._create_header()
        main_layout.addWidget(header)

        # QSplitter: tree widget ABOVE buttons (VERTICAL orientation)
        splitter = QSplitter(Qt.Orientation.Vertical)

        # Top: server tree
        self.server_tree = QTreeWidget()
        self.server_tree.setHeaderLabels(["Server / Worker", "Status", "Info"])
        self.server_tree.setSelectionMode(
            QAbstractItemView.SelectionMode.ExtendedSelection
        )
        self.server_tree.itemDoubleClicked.connect(self._on_item_double_clicked)
        self.server_tree.setColumnWidth(0, 250)
        self.server_tree.setColumnWidth(1, 100)
        self.server_tree.setIndentation(20)  # 20px = 2 spaces at typical font size
        splitter.addWidget(self.server_tree)

        # Bottom: button panel
        button_panel = self._create_button_panel()
        splitter.addWidget(button_panel)

        # Set initial sizes: tree takes all space, buttons collapse to minimum height
        splitter.setSizes([1000, 1])
        splitter.setStretchFactor(0, 1)  # Tree widget expands
        splitter.setStretchFactor(1, 0)  # Button panel stays at minimum height

        main_layout.addWidget(splitter)

        # Apply styling
        if self.style_generator:
            cs = self.style_generator.color_scheme

            # Apply tree widget style
            self.server_tree.setStyleSheet(
                self.style_generator.generate_tree_widget_style()
            )

        # Connect internal signals
        self._scan_complete.connect(self._update_server_list)
        self._kill_complete.connect(self._on_kill_complete)
        self.server_killed.connect(self._on_server_killed)

    def _create_header(self) -> QWidget:
        """Create header with title and status label (similar to AbstractManagerWidget)."""
        header = QWidget()
        header_layout = QHBoxLayout(header)
        header_layout.setContentsMargins(5, 5, 5, 5)

        # Title label
        title_label = QLabel(self.title)
        title_label.setFont(QFont("Arial", 12, QFont.Weight.Bold))
        if self.style_generator:
            title_label.setStyleSheet(
                f"color: {self.style_generator.color_scheme.to_hex(self.style_generator.color_scheme.text_accent)};"
            )
        header_layout.addWidget(title_label)

        header_layout.addStretch()

        # Status label
        self.status_label = QLabel("Ready")
        if self.style_generator:
            self.status_label.setStyleSheet(
                f"color: {self.style_generator.color_scheme.to_hex(self.style_generator.color_scheme.status_success)}; "
                f"font-weight: bold;"
            )
        header_layout.addWidget(self.status_label)

        return header

    def _create_button_panel(self) -> QWidget:
        """Create button panel with consistent styling."""
        panel = QWidget()
        layout = QHBoxLayout(panel)
        layout.setContentsMargins(5, 5, 5, 5)
        layout.setSpacing(5)

        self.refresh_btn = QPushButton("Refresh")
        self.refresh_btn.setToolTip("Refresh server list")
        self.refresh_btn.clicked.connect(self.refresh_servers)
        layout.addWidget(self.refresh_btn)

        self.quit_btn = QPushButton("Quit")
        self.quit_btn.setToolTip("Gracefully quit selected servers")
        self.quit_btn.clicked.connect(self.quit_selected_servers)
        layout.addWidget(self.quit_btn)

        self.force_kill_btn = QPushButton("Force Kill")
        self.force_kill_btn.setToolTip("Force kill selected servers")
        self.force_kill_btn.clicked.connect(self.force_kill_selected_servers)
        layout.addWidget(self.force_kill_btn)

        # Apply button styles
        if self.style_generator:
            button_style = self.style_generator.generate_button_style()
            self.refresh_btn.setStyleSheet(button_style)
            self.quit_btn.setStyleSheet(button_style)
            self.force_kill_btn.setStyleSheet(button_style)

        return panel

    def refresh_servers(self):
        """Scan ports and refresh server list (async in background)."""
        # Guard against calls after cleanup
        if self._is_cleaning_up:
            return

        def scan_and_update():
            """Background thread to scan ports without blocking UI."""
            import concurrent.futures

            # Scan ports in parallel using thread pool (like Napari implementation)
            servers = []

            with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
                # Submit all ping tasks
                future_to_port = {
                    executor.submit(self._ping_server, port): port
                    for port in self.ports_to_scan
                }

                # Collect results as they complete
                for future in concurrent.futures.as_completed(future_to_port):
                    port = future_to_port[future]
                    try:
                        server_info = future.result()
                        if server_info:
                            servers.append(server_info)
                    except Exception as e:
                        logger.debug(f"Error scanning port {port}: {e}")

            # Update UI on main thread via signal
            self._scan_complete.emit(servers)

        # Start scan in background thread
        spawn_thread_with_context(scan_and_update, name="scan_servers")

    def _ping_server(self, port: int) -> Optional[Dict[str, Any]]:
        """
        Ping a server on the given port and return its info.

        Returns server info dict if responsive, None otherwise.
        """
        import zmq
        import pickle
        from openhcs.constants.constants import CONTROL_PORT_OFFSET
        from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
        from zmqruntime.transport import (
            get_zmq_transport_url,
            get_default_transport_mode,
        )

        control_port = port + CONTROL_PORT_OFFSET
        control_context = None
        control_socket = None

        try:
            control_context = zmq.Context()
            control_socket = control_context.socket(zmq.REQ)
            control_socket.setsockopt(zmq.LINGER, 0)
            control_socket.setsockopt(
                zmq.RCVTIMEO, 300
            )  # 300ms timeout for fast scanning

            # Use transport mode-aware URL (IPC or TCP)
            transport_mode = get_default_transport_mode()

            # Use transport mode-aware URL (IPC or TCP)
            transport_mode = get_default_transport_mode()
            control_url = get_zmq_transport_url(
                control_port,
                host="localhost",
                mode=transport_mode,
                config=OPENHCS_ZMQ_CONFIG,
            )
            control_socket.connect(control_url)

            # Send ping
            ping_message = {"type": "ping"}
            control_socket.send(pickle.dumps(ping_message))

            # Wait for pong
            response = control_socket.recv()
            response_data = pickle.loads(response)

            # Return server info if valid pong
            if response_data.get("type") == "pong":
                return response_data

            return None

        except Exception:
            return None
        finally:
            if control_socket:
                try:
                    control_socket.close()
                except:
                    pass
            if control_context:
                try:
                    control_context.term()
                except:
                    pass

    def _setup_progress_client(self):
        """Setup ZMQ Execution Client for receiving progress messages (like Plate Manager)."""
        from openhcs.runtime.zmq_execution_client import ZMQExecutionClient

        logger.info("ZMQ server manager: _setup_progress_client() called")

        # Disconnect existing client if any
        if self._zmq_client:
            try:
                logger.info("ZMQ server manager: Disconnecting existing client")
                self._zmq_client.disconnect()
            except Exception as e:
                logger.warning(f"ZMQ server manager: Failed to disconnect: {e}")
            self._zmq_client = None

        try:
            # Create ZMQ Execution Client with progress callback (like Plate Manager)
            self._zmq_client = ZMQExecutionClient(
                port=7777,  # Execution server port
                persistent=True,
                progress_callback=self._on_progress,  # Like Plate Manager
            )

            # Connect to server
            logger.info("ZMQ server manager: Attempting to connect...")
            connected = self._zmq_client.connect(timeout=1)
            if connected:
                logger.info(
                    f"ZMQ server manager: Connected to execution server via ZMQExecutionClient, "
                    f"data_socket={self._zmq_client.data_socket is not None}"
                )
                # IMPORTANT: Start progress listener explicitly (only auto-starts in submit_execution)
                self._zmq_client._start_progress_listener()
            else:
                logger.info("ZMQ server manager: No execution server running yet")
                self._zmq_client = None
        except Exception as e:
            logger.warning(f"Failed to connect to execution server: {e}")
            self._zmq_client = None

    def _on_progress(self, message: dict) -> None:
        """Handle progress updates from ZMQ execution server.

        Uses ExecutionProgressTracker (shared abstraction with plate manager).
        """
        try:
            execution_id = message.get("execution_id") or message.get("task_id")
            axis_id = message["axis_id"]
            step = message["step"]
            percent = message.get("percent", 0)
            plate_id = message.get("plate_id", "")

            # Only track messages with meaningful step values OR total_wells info
            # Empty step = pipeline execution (not compilation, not tracked)
            # EXCEPTION: total_wells messages have step='' but must be tracked
            total_wells = message.get("total_wells")

            if step or total_wells:
                self._progress_tracker.add_message(message)

                # NOTE: cleanup_old_executions() is handled by _periodic_cleanup() every 1 second
                # No need to call it on every progress message (redundant)

            # Update tree widget via signal (thread-safe, called from background thread)
            # This ensures tree updates happen on the UI thread, avoiding crashes
            self._progress_update.emit()
        except Exception as e:
            logger.exception(f"Error in _on_progress: {e}")
            # Don't re-raise - just log and continue

    @pyqtSlot()
    def _update_tree_with_progress(self):
        """Update tree widget in-place with current progress (no port scan).

        Called via signal from background progress thread, runs on UI thread.
        """
        try:
            # Find execution server item and update it
            for i in range(self.server_tree.topLevelItemCount()):
                item = self.server_tree.topLevelItem(i)
                if not item:
                    continue
                data = item.data(0, Qt.ItemDataRole.UserRole)
                if not data:
                    continue
                # Check if this is an execution server
                server_name = data.get("server", "")
                if server_name.endswith("ExecutionServer"):
                    self._update_execution_server_item(item, data)
                    return
        except Exception as e:
            logger.exception(f"Error updating tree with progress: {e}")
            # Don't re-raise - just log and continue

    def _get_plate_name(self, plate_id: str, exec_id: str = None) -> str:
        """Extract plate name (leaf) from full path.

        For multi-execution scenarios (same plate run multiple times), use exec_id
        to make plate names unique in the tree.
        """
        plate_leaf = Path(plate_id).name
        # If exec_id provided and there might be duplicates, include it for uniqueness
        # Use last 8 chars of exec_id for brevity
        if exec_id:
            return f"{plate_leaf} ({exec_id[:8]})"
        return plate_leaf

    def _cleanup_lingered_plates(self):
        """Remove plates that have lingered long enough."""
        current_time = time.time()
        to_remove = []

        # Use spawned plates instead of lingered - plates stay for linger_seconds after first appearing
        for plate_id, spawn_timestamp in self._spawned_plates.items():
            if current_time - spawn_timestamp > self._linger_seconds:
                to_remove.append(plate_id)

        for plate_id in to_remove:
            del self._spawned_plates[plate_id]

        # Find and remove plate items from tree (search by both plate_id and exec_id)
        if to_remove:
            for i in range(self.server_tree.topLevelItemCount()):
                root_item = self.server_tree.topLevelItem(i)
                if not root_item:
                    continue

                # Search children recursively for plate items
                self._remove_spawned_plate_by_id(root_item, to_remove)

            logger.debug(f"Cleaned up {len(to_remove)} spawned plates")

    def _remove_spawned_plate_by_id(
        self, parent: QTreeWidgetItem, plate_ids_to_remove: list[str]
    ):
        """Recursively find and remove spawned plate items by plate_id.

        Note: This only removes spawned plates (from _spawned_plates), not active plates.
        """
        for i in range(parent.childCount() - 1, -1, -1):
            child = parent.child(i)
            child_data = child.data(0, Qt.ItemDataRole.UserRole)
            if (
                child_data
                and child_data.get("type") == "plate"
                and child_data.get("plate_id") in plate_ids_to_remove
            ):
                parent.removeChild(child)

    def _update_execution_server_item(
        self, server_item: QTreeWidgetItem, server_data: dict
    ):
        """Update execution server item and its children with current progress.

        Execution server shows the average of all plates' % completion.
        Each plate is shown as a subtree item.
        """
        import logging

        logger = logging.getLogger(__name__)

        try:
            executions = self._progress_tracker.executions

            # Collect active plate IDs from executions
            active_plate_ids = set()
            if executions:
                for exec_obj in executions.values():
                    for plate_id in exec_obj.plates.keys():
                        active_plate_ids.add(plate_id)

            # Track newly spawned plates (first time we see them)
            current_time = time.time()
            for plate_id in active_plate_ids:
                if plate_id not in self._spawned_plates:
                    self._spawned_plates[plate_id] = current_time

            # DO NOT remove from _spawned_plates when plate is active
            # Plates should linger for linger_seconds even if they complete
            # The linger cleanup timer will remove them after linger_seconds

            if not executions and not self._spawned_plates:
                # No executions - show idle
                server_item.setText(1, "✅ Idle")
                server_item.setText(2, "")
                return

            # Collect plate items with their % completion
            plate_items = []

            if executions:
                for exec_id, exec_obj in executions.items():
                    for plate_id, plate_obj in exec_obj.plates.items():
                        plate_name = self._get_plate_name(plate_id, exec_id)

                        # Determine if compiling (no PIDs) or executing (has PIDs)
                        # We need to check ALL axes (including compilation) to determine phase
                        all_axes_including_compilation = plate_obj.get_sorted_axes(
                            include_compilation=True
                        )

                        if not all_axes_including_compilation:
                            continue

                        has_workers = any(
                            ax.pid is not None for ax in all_axes_including_compilation
                        )
                        status = "⏳ Compiling" if not has_workers else "⚙️ Executing"

                        # Clear compilation axes when transitioning to execution
                        # This must happen here (GUI process) not in runtime (separate process)
                        if has_workers:
                            plate_obj.clear_compilation_axes()
                            # Refresh axes after clearing compilation axes
                            all_axes_including_compilation = plate_obj.get_sorted_axes(
                                include_compilation=True
                            )

                        # Calculate plate % completion differently for compilation vs execution
                        if not has_workers:
                            # Compilation: average of step percent (include compilation axes!)
                            total_percent = sum(
                                ax.percent for ax in all_axes_including_compilation
                            )
                            plate_percent = (
                                total_percent / len(all_axes_including_compilation)
                                if all_axes_including_compilation
                                else 0
                            )
                            logger.info(
                                f"DEBUG COMPILATION PLATE PERCENT: {plate_percent:.1f}% from axes: {[ax.percent for ax in all_axes_including_compilation]}"
                            )
                        else:
                            # Execution: average of all axes' percent values
                            # (compilation axes already cleared above)
                            plate_percent = (
                                sum(ax.percent for ax in all_axes_including_compilation)
                                / len(all_axes_including_compilation)
                                if all_axes_including_compilation
                                else 0
                            )
                            logger.info(
                                f"DEBUG EXECUTION PLATE PERCENT: {plate_percent:.1f}% from axes: {[ax.percent for ax in all_axes_including_compilation]}"
                            )

                        plate_items.append(
                            {
                                "plate_id": plate_id,
                                "plate_name": plate_name,
                                "plate_percent": plate_percent,
                                "status": status,
                                "has_workers": has_workers,
                                "axes": all_axes_including_compilation,
                                "exec_id": exec_id,
                            }
                        )
                        plate_items.append(
                            {
                                "plate_id": plate_id,
                                "plate_name": plate_name,
                                "plate_percent": plate_percent,
                                "status": status,
                                "has_workers": has_workers,
                                "axes": all_axes_including_compilation,
                                "exec_id": exec_id,
                            }
                        )

            # Only show idle if no executions and no spawned plates to linger
            if not executions and not self._spawned_plates:
                server_item.setText(1, "✅ Idle")
                server_item.setText(2, "")
                return

            # Calculate overall average across all plates
            overall_percent = (
                sum(p["plate_percent"] for p in plate_items) / len(plate_items)
                if plate_items
                else 0
            )

            compiling_count = sum(1 for p in plate_items if not p["has_workers"])
            executing_count = sum(1 for p in plate_items if p["has_workers"])

            status_text = ""
            if compiling_count > 0 and executing_count > 0:
                status_text = (
                    f"⏳ {compiling_count} compiling, ⚙️ {executing_count} executing"
                )
            elif compiling_count > 0:
                status_text = f"⏳ {compiling_count} compiling"
            else:
                status_text = f"⚙️ {executing_count} executing"

            logger.info(
                f"DEBUG SERVER ITEM: status_text='{status_text}', "
                f"overall_percent={overall_percent:.1f}%, "
                f"num_plates={len(plate_items)}"
            )
            for p in plate_items:
                logger.info(
                    f"DEBUG PLATE: name={p['plate_name']}, percent={p['plate_percent']:.1f}%"
                )

            server_item.setText(1, status_text)
            server_item.setText(
                2, f"Avg: {overall_percent:.1f}% | {len(plate_items)} plates"
            )

            # Auto-expand execution server when it has subtree items
            if plate_items or self._spawned_plates:
                server_item.setExpanded(True)

            # Update plate child items (include spawned plates)
            self._update_plate_children(server_item, plate_items)

        except Exception as e:
            logger.exception(f"Error updating execution server item: {e}")

    def _update_plate_children(self, server_item: QTreeWidgetItem, plate_items: list):
        """Update child items for plate progress (both compilation and execution)."""
        import logging

        logger = logging.getLogger(__name__)

        current_time = time.time()

        for plate_data in plate_items:
            plate_id = plate_data["plate_id"]
            plate_name = plate_data["plate_name"]
            plate_percent = plate_data["plate_percent"]
            status = plate_data["status"]
            has_workers = plate_data["has_workers"]
            axes = plate_data["axes"]
            exec_id = plate_data.get("exec_id", "")

            # Cache last seen plate data for lingered display (key by plate_id only)
            if plate_id not in self._last_seen_plate_data:
                self._last_seen_plate_data[plate_id] = plate_data

            # Track newly spawned plates for lingering (key by plate_id only)
            if plate_id not in self._spawned_plates:
                self._spawned_plates[plate_id] = current_time

            # Find or create plate item - use (plate_id, exec_id) for uniqueness
            plate_item = None
            for i in range(server_item.childCount()):
                child = server_item.child(i)
                child_data = child.data(0, Qt.ItemDataRole.UserRole)
                if (
                    child_data
                    and child_data.get("type") == "plate"
                    and child_data.get("plate_id") == plate_id
                    and child_data.get("exec_id") == exec_id
                ):
                    plate_item = child
                    break

            if plate_item:
                # Update existing plate item
                plate_item.setText(1, status)
                plate_item.setText(2, f"{plate_percent:.1f}%")
                logger.info(
                    f"PLATE UPDATE: id={plate_id[:8]}, name={plate_name}, percent={plate_percent:.1f}%, status={status}"
                )
            else:
                # Create new plate item
                new_item = QTreeWidgetItem(
                    [f"  📋 {plate_name}", status, f"{plate_percent:.1f}%"]
                )
                new_item.setData(
                    0,
                    Qt.ItemDataRole.UserRole,
                    {
                        "type": "plate",
                        "plate_id": plate_id,
                        "exec_id": exec_id,
                    },
                )
                server_item.addChild(new_item)
                plate_item = new_item

            # ALWAYS track plate spawn time for linger (even if already exists)
            if plate_id not in self._spawned_plates:
                self._spawned_plates[plate_id] = current_time

            # Update plate's children (axes or workers)
            logger.debug(
                f"Updating plate {plate_name}: has_workers={has_workers}, axes_count={len(axes)}, axes={[ax.axis_id for ax in axes]}"
            )
            if has_workers:
                self._update_plate_worker_children(plate_item, axes)
            else:
                self._update_plate_compilation_children(plate_item, axes)

        # Add/Update spawned plates that are not in plate_items (completed but not cleaned up)
        for plate_id, spawn_timestamp in self._spawned_plates.items():
            # Skip if this plate is already in plate_items (active)
            if plate_id in [p["plate_id"] for p in plate_items]:
                continue

            # This plate is spawned but no longer in active executions
            # It should be shown until spawn_timestamp + linger_seconds expires
            elapsed = current_time - spawn_timestamp
            if elapsed > self._linger_seconds:
                continue  # Skip plates that have already expired

            # Get the plate data from last seen cache
            cached_data = self._last_seen_plate_data.get(plate_id)
            if cached_data:
                plate_name = cached_data["plate_name"]
                status = "✅ Complete"
                plate_percent = 100.0
                has_workers = cached_data["has_workers"]
                axes = cached_data["axes"]
            else:
                # Fallback if not cached (shouldn't happen normally)
                plate_name = self._get_plate_name(plate_id)
                status = "✅ Complete"
                plate_percent = 100.0
                has_workers = False
                axes = []

            # Find existing plate item
            plate_item = None
            for i in range(server_item.childCount()):
                child = server_item.child(i)
                child_data = child.data(0, Qt.ItemDataRole.UserRole)
                if (
                    child_data
                    and child_data.get("type") == "plate"
                    and child_data.get("plate_id") == plate_id
                ):
                    plate_item = child
                    break

            if not plate_item:
                # Create spawned plate item
                new_item = QTreeWidgetItem(
                    [f"  📋 {plate_name}", status, f"{plate_percent:.1f}%"]
                )
                new_item.setData(
                    0,
                    Qt.ItemDataRole.UserRole,
                    {
                        "type": "plate",
                        "plate_id": plate_id,
                    },
                )
                server_item.addChild(new_item)
                plate_item = new_item

                # Update lingered plate's children
                if has_workers:
                    self._update_plate_worker_children(plate_item, axes)
                else:
                    self._update_plate_compilation_children(plate_item, axes)

        # Remove plate items that are neither active nor spawned
        active_plate_ids = set(p["plate_id"] for p in plate_items)
        spawned_plate_ids = set(self._spawned_plates.keys())
        all_valid_ids = active_plate_ids | spawned_plate_ids

        for i in range(server_item.childCount() - 1, -1, -1):
            child = server_item.child(i)
            child_data = child.data(0, Qt.ItemDataRole.UserRole)
            if child_data and child_data.get("type") == "plate":
                if child_data.get("plate_id") not in all_valid_ids:
                    server_item.removeChild(child)

    def _update_plate_compilation_children(
        self, plate_item: QTreeWidgetItem, axes: list
    ):
        """Update compilation children (axes without workers) for a plate."""
        # Track current axis IDs to remove stale items when new ones added
        active_axis_ids = set()

        for axis in axes:
            axis_id = axis.axis_id
            active_axis_ids.add(axis_id)

            # Find existing compilation item
            child_item = None
            for i in range(plate_item.childCount()):
                child = plate_item.child(i)
                child_data = child.data(0, Qt.ItemDataRole.UserRole)
                if (
                    child_data
                    and child_data.get("type") == "compilation"
                    and child_data.get("axis_id") == axis_id
                ):
                    child_item = child
                    break

            # Display format for compilation axis
            display_text = f"    [{axis_id}] {axis.step_name} {axis.percent:.1f}%"
            status_text = f"{axis.phase.value}"

            if child_item:
                # Update existing item
                child_item.setText(1, status_text)
                child_item.setText(2, display_text)
            else:
                # Create new compilation item
                new_item = QTreeWidgetItem(
                    [f"    [{axis_id}]", status_text, display_text]
                )
                new_item.setData(
                    0,
                    Qt.ItemDataRole.UserRole,
                    {
                        "type": "compilation",
                        "axis_id": axis_id,
                    },
                )
                plate_item.addChild(new_item)

        # Remove compilation items that are no longer in active_axis_ids
        for i in range(plate_item.childCount() - 1, -1, -1):
            child = plate_item.child(i)
            child_data = child.data(0, Qt.ItemDataRole.UserRole)
            if child_data and child_data.get("type") == "compilation":
                axis_id = child_data.get("axis_id")
                if axis_id not in active_axis_ids:
                    logger.debug(
                        f"Removing stale compilation item: {axis_id} (childCount before: {plate_item.childCount()})"
                    )
                    plate_item.removeChild(child)
        logger.debug(
            f"_update_plate_compilation_children: Updated {len(axes)} compilation axes, final childCount: {plate_item.childCount()}"
        )

    def _update_plate_worker_children(self, plate_item: QTreeWidgetItem, axes: list):
        """Update worker children for a plate - shows ALL axes individually."""
        # Show all axes as individual items (not grouped by worker PID)
        # Create or update axis items
        for axis in axes:
            axis_id = axis.axis_id

            # Display format for axis item
            display_text = f"[{axis_id}] {axis.step_name} {axis.percent:.1f}%"

            # Find existing axis item
            child_item = None
            for i in range(plate_item.childCount()):
                child = plate_item.child(i)
                child_data = child.data(0, Qt.ItemDataRole.UserRole)
                if (
                    child_data
                    and child_data.get("type") == "axis"
                    and child_data.get("axis_id") == axis_id
                ):
                    child_item = child
                    break

            # Remove any old axis items that are not in the current axes list
            # This handles phase transitions (compilation -> execution)
            for i in range(plate_item.childCount() - 1, -1, -1):
                child = plate_item.child(i)
                child_data = child.data(0, Qt.ItemDataRole.UserRole)
                if child_data and child_data.get("type") == "axis":
                    axis_id = child_data.get("axis_id")
                    if axis_id not in [ax.axis_id for ax in axes]:
                        logger.debug(
                            f"Removing stale axis item: {axis_id} (childCount before: {plate_item.childCount()})"
                        )
                        plate_item.removeChild(child)
                        logger.debug(
                            f"Child count after removal: {plate_item.childCount()}"
                        )
            logger.debug(
                f"_update_plate_worker_children: Updated {len(axes)} axes, final childCount: {plate_item.childCount()}"
            )

            if child_item:
                # Update existing item
                child_item.setText(2, display_text)
                # Add completion check to child data
                child_item.setData(
                    0,
                    Qt.ItemDataRole.UserRole,
                    {
                        **child_data.data(0, Qt.ItemDataRole.UserRole),
                        "is_complete": axis.is_complete(),
                    },
                )
            else:
                # Create new axis item
                new_item = QTreeWidgetItem(
                    [
                        f"    [{axis_id}]",
                        "⚙️ running" if not axis.is_complete() else "✅ Complete",
                        display_text,
                    ]
                )
                new_item.setData(
                    0,
                    Qt.ItemDataRole.UserRole,
                    {
                        "type": "axis",
                        "axis_id": axis_id,
                        "is_complete": axis.is_complete(),
                    },
                )
                plate_item.addChild(new_item)

        # Old worker grouping (removed - now showing all axes individually)
        # for worker_pid, worker_axes in workers_by_pid.items():
        #     # Calculate worker's overall progress
        #     worker_percent = (
        #         sum(ax.percent for ax in worker_axes) / len(worker_axes)
        #         if worker_axes
        #         else 0
        #     )
        #
        #     # Get current active well (first non-complete well, or first axis if all complete)
        #     active_wells = [w for w in worker_axes if not w.is_complete()]
        #     if active_wells:
        #         current_well = active_wells[0]
        #         # Get step info from context
        #         step_index = current_well.completed
        #         total_steps = current_well.total
        #         step_percent = current_well.percent
        #         step_part = f"Step {step_index}/{total_steps} ({step_percent:.1f}%) {current_well.step_name}"
        #         well_part = f"Well {worker_percent:.1f}% {current_well.axis_id}"
        #         worker_info = f"{step_part}, {well_part}"
        #     else:
        #         # All wells complete
        #         current_well = worker_axes[0]
        #         worker_info = f"✅ Complete {worker_percent:.1f}%"
        #
        #     # Find existing worker item
        #     worker_item = None
        #     for i in range(plate_item.childCount()):
        #         child = plate_item.child(i)
        #         child_data = child.data(0, Qt.ItemDataRole.UserRole)
        #         if (
        #             child_data
        #             and child_data.get("type") == "worker"
        #             and child_data.get("pid") == worker_pid
        #         ):
        #             worker_item = child
        #             break
        #
        #     if worker_item:
        #         # Update existing item
        #         worker_item.setText(2, worker_info)
        #         if not active_wells:
        #             worker_item.setText(1, "✅ Complete")
        #     else:
        #         # Create new worker item
        #         worker_text = f"    Worker PID {worker_pid}"
        #         worker_status = "⚙️ running" if active_wells else "✅ Complete"
        #         new_item = QTreeWidgetItem([worker_text, worker_status, worker_info])
        #         new_item.setData(
        #             0, Qt.ItemDataRole.UserRole, {"type": "worker", "pid": worker_pid}
        #         )
        #         plate_item.addChild(new_item)
        #
        #     # Remove workers that are no longer active
        #     active_pids = set(workers_by_pid.keys())
        #     for i in range(plate_item.childCount() - 1, -1, -1):
        #         child = plate_item.child(i)
        #         child_data = child.data(0, Qt.ItemDataRole.UserRole)
        #         if child_data and child_data.get("type") == "worker":
        #             if child_data.get("pid") not in active_pids:
        #                 plate_item.removeChild(child)

    def _create_tree_item(
        self, display: str, status: str, info: str, data: dict
    ) -> QTreeWidgetItem:
        """Create a tree widget item with consistent data storage.

        Reduces boilerplate from repeated item creation patterns.
        """
        item = QTreeWidgetItem([display, status, info])
        item.setData(0, Qt.ItemDataRole.UserRole, data)
        return item

    def _create_worker_item(
        self, worker: WorkerState, server_raw: dict
    ) -> QTreeWidgetItem:
        """Create a tree widget item for a worker process.

        Uses shared ExecutionProgressTracker for progress lookup.
        """
        import logging

        logger = logging.getLogger(__name__)

        worker_text = f"  Worker PID {worker.pid}"
        worker_status = f"⚙️ {worker.status}"

        # Look up progress from tracker (by PID via axis_id)
        all_progress = self._progress_tracker.get_all_progress()
        progress = None
        worker_metadata = worker.metadata or {}
        worker_axis = worker_metadata.get("axis_id", "")

        logger.debug(
            f"Worker PID {worker.pid} has axis_id='{worker_axis}', metadata keys={list(worker_metadata.keys())}"
        )

        for axis_progress in all_progress:
            # Find progress for this worker's axis
            if axis_progress.axis_id == worker_axis:
                progress = axis_progress
                break

        # Show progress if available (like PlateManager status format)
        if progress:
            worker_info = f"[{progress.axis_id}] {progress.step_name} {progress.percent:.1f}% {progress.phase.value}"
        else:
            # No progress found - show what we know
            if worker_axis:
                worker_info = f"[{worker_axis}] Waiting for progress..."
            else:
                worker_info = f"Waiting for axis_id assignment..."

        return self._create_tree_item(
            worker_text,
            worker_status,
            worker_info,
            {"type": "worker", "pid": worker.pid, "server": server_raw},
        )

    @singledispatchmethod
    def _render_server(self, info: BaseServerInfo, status_icon: str) -> QTreeWidgetItem:
        """Render server item - dispatched based on server type."""
        raise NotImplementedError(f"No render for {type(info).__name__}")

    @_render_server.register
    def _(self, info: ExecutionServerInfo, status_icon: str) -> QTreeWidgetItem:
        """Render ExecutionServer.

        Source of truth: ping response (info.compile_status).
        This aligns with plate manager's local state tracking.
        """
        port = info.port
        server_text = f"Port {port} - Execution Server"

        # Priority 1: Compile status from ping (matches plate manager)
        if info.compile_status:
            cs = info.compile_status
            if cs.is_success:
                status_text = "✅ Compiled"
                info_text = cs.message
            elif cs.is_failed:
                status_text = "❌ Compile failed"
                info_text = cs.message
            else:
                # Currently compiling (cs.is_success=False, cs.is_failed=False)
                status_text = "⏳ Compiling"
                info_text = cs.message or "Compiling pipeline..."

            return self._create_tree_item(server_text, status_text, info_text, info.raw)

        # Priority 2: Running executions
        if info.running_executions:
            all_progress = self._progress_tracker.get_all_progress()
            active_progress = [p for p in all_progress if not p.is_complete()]

            logger.info(
                f"Execution server port {port}: running_executions={len(info.running_executions)}, "
                f"all_progress={len(all_progress)}, active_progress={len(active_progress)}, "
                f"workers={len(info.workers)}"
            )

            if active_progress:
                percentages = [p.percent for p in active_progress]
                avg_percent = sum(percentages) / len(percentages)
                status_text = f"{status_icon} {len(info.running_executions)} exec"
                first_plate = active_progress[0].plate_id if active_progress else ""
                info_text = f"Avg: {avg_percent:.1f}% | {first_plate}"

                logger.info(
                    f"Execution server port {port}: avg_percent={avg_percent:.1f}, "
                    f"first_plate={first_plate}, "
                    f"sample_progress: axis={active_progress[0].axis_id}, step={active_progress[0].step_name}, percent={active_progress[0].percent}"
                )
            else:
                status_text = f"{status_icon} {len(info.running_executions)} exec"
                info_text = f"{len(info.workers)} workers"

            return self._create_tree_item(server_text, status_text, info_text, info.raw)

        # Priority 3: Idle
        status_text = f"{status_icon} Idle"
        info_text = f"{len(info.workers)} workers" if info.workers else ""
        return self._create_tree_item(server_text, status_text, info_text, info.raw)

    @_render_server.register
    def _(self, info: ViewerServerInfo, status_icon: str) -> QTreeWidgetItem:
        """Render ViewerServer (Napari/Fiji)."""
        kind_name = info.server_kind.name.title()
        display_text = f"Port {info.port} - {kind_name} Viewer"
        status_text = status_icon
        info_text = ""

        if info.memory_mb is not None:
            info_text = f"Mem: {info.memory_mb:.0f}MB"
            if info.cpu_percent is not None:
                info_text += f" | CPU: {info.cpu_percent:.1f}%"

        return self._create_tree_item(display_text, status_text, info_text, info.raw)

    @_render_server.register
    def _(self, info: GenericServerInfo, status_icon: str) -> QTreeWidgetItem:
        """Render generic/unknown server."""
        display_text = f"Port {info.port} - {info.server_name}"
        return self._create_tree_item(display_text, status_icon, "", info.raw)

    @singledispatchmethod
    def _populate_server_children(
        self, info: BaseServerInfo, server_item: QTreeWidgetItem
    ) -> bool:
        """Populate server with children - dispatched based on server type."""
        logger.warning(
            f"_populate_server_children: No handler for type {type(info).__name__}, using default (no children)"
        )
        return False  # Default: no children

    @_populate_server_children.register
    def _(self, info: ExecutionServerInfo, server_item: QTreeWidgetItem) -> bool:
        """Populate ExecutionServer children.

        Progress children (compilation axes and workers) are now driven by
        progress tracker updates via _update_tree_with_progress().

        We return True to ensure the server item expands and shows progress
        during initial population.
        """
        return True  # True so server expands and allows progress updates

    @_populate_server_children.register
    def _(self, info: ViewerServerInfo, server_item: QTreeWidgetItem) -> bool:
        """Populate ViewerServer - no children."""
        return False

    @_populate_server_children.register
    def _(self, info: GenericServerInfo, server_item: QTreeWidgetItem) -> bool:
        """Populate GenericServer - no children."""
        return False

    @pyqtSlot()
    def _refresh_launching_viewers_only(self):
        """Fast refresh: Update UI with launching viewers only (no port scan).

        This is called when launching viewer state changes and provides instant feedback.
        """
        # Guard against calls after cleanup
        if self._is_cleaning_up:
            return

        # Keep existing scanned servers, just update the tree display
        self._update_server_list(self.servers)

    @pyqtSlot(list)
    def _update_server_list(self, servers: List[Dict[str, Any]]):
        """Update server tree on UI thread (called via signal)."""
        from zmqruntime.queue_tracker import GlobalQueueTrackerRegistry

        self.servers = servers

        # Update cache of last known servers
        for server in servers:
            port = server.get("port")
            if port:
                self._last_known_servers[port] = server

        # Save current selection (by port) before clearing
        selected_ports = set()
        for item in self.server_tree.selectedItems():
            server_data = item.data(0, Qt.ItemDataRole.UserRole)
            if server_data and "port" in server_data:
                selected_ports.add(server_data["port"])

        self.server_tree.clear()

        # Get queue tracker registry for progress info
        registry = GlobalQueueTrackerRegistry()

        # First, add launching viewers
        mgr = ViewerStateManager.get_instance()
        launching_viewers = {
            v.port: {"type": v.viewer_type, "queued_images": v.queued_images}
            for v in mgr.list_viewers()
            if v.state == ViewerState.LAUNCHING
        }

        for port, info in launching_viewers.items():
            viewer_type = info["type"].capitalize()
            queued_images = info["queued_images"]

            display_text = f"Port {port} - {viewer_type} Viewer"
            status_text = "🚀 Launching"
            info_text = (
                f"{queued_images} images queued" if queued_images > 0 else "Starting..."
            )

            item = self._create_tree_item(
                display_text, status_text, info_text, {"port": port, "launching": True}
            )
            self.server_tree.addTopLevelItem(item)

        # Add servers that are processing images (even if they didn't respond to ping)
        # This prevents busy servers from disappearing during image processing
        scanned_ports = {parse_server_info(s).port for s in servers}
        for tracker_port, tracker in registry.get_all_trackers().items():
            if tracker_port in scanned_ports or tracker_port in launching_viewers:
                continue  # Already in the list

            # Check if this tracker has pending images (server is busy processing)
            pending = tracker.get_pending_count()
            if pending > 0:
                # Server is busy processing - add it even though it didn't respond to ping
                processed, total = tracker.get_progress()
                viewer_type = tracker.viewer_type.capitalize()

                display_text = f"Port {tracker_port} - {viewer_type}ViewerServer"
                status_text = "⚙️"  # Busy icon
                info_text = f"Processing: {processed}/{total} images"

                # Check for stuck images
                if tracker.has_stuck_images():
                    status_text = "⚠️"
                    stuck_images = tracker.get_stuck_images()
                    info_text += f" (⚠️ {len(stuck_images)} stuck)"

                # Create pseudo-server dict for consistency
                pseudo_server = {
                    "port": tracker_port,
                    "server": f"{viewer_type}ViewerServer",
                    "ready": True,
                    "busy": True,  # Mark as busy
                }

                item = self._create_tree_item(
                    display_text, status_text, info_text, pseudo_server
                )
                self.server_tree.addTopLevelItem(item)

        # Add execution servers that have active progress (even if they didn't respond to ping)
        # This prevents busy execution servers from disappearing during pipeline execution
        if self._progress_tracker.get_all_progress():
            # Check each port we scan for execution servers
            for port in self.ports_to_scan:
                if port in scanned_ports or port in launching_viewers:
                    continue  # Already in the list

                # Check if we have a cached server info for this port
                if port in self._last_known_servers:
                    cached_server = self._last_known_servers[port]
                    server_name = cached_server.get("server", "")

                    # Only add if it was an execution server
                    if server_name.endswith("ExecutionServer"):
                        # Create pseudo-server with busy indicator
                        display_text = f"Port {port} - Execution Server"
                        status_text = "⚙️ Busy"
                        info_text = "Executing pipeline..."

                        # Use cached server data but mark as busy
                        busy_server = cached_server.copy()
                        busy_server["busy"] = True

                        item = self._create_tree_item(
                            display_text, status_text, info_text, busy_server
                        )
                        self.server_tree.addTopLevelItem(item)

        # Then add running servers - use typed dispatch
        for server in servers:
            server_info = parse_server_info(server)

            # Skip if this port is in launching registry (shouldn't happen, but be safe)
            if server_info.port in launching_viewers:
                continue

            # Determine status icon
            status_icon = "✅" if server_info.ready else "🚀"

            # Dispatch to appropriate renderer based on actual type
            server_item = self._render_server(server_info, status_icon)
            self.server_tree.addTopLevelItem(server_item)

            # Dispatch to appropriate children populator
            logger.info(
                f"About to populate children for server type {type(server_info).__name__} on port {server_info.port}"
            )
            has_children = self._populate_server_children(server_info, server_item)
            logger.info(
                f"Populate children returned {has_children} for port {server_info.port}"
            )
            if has_children:
                server_item.setExpanded(True)

        # Restore selection after refresh
        if selected_ports:
            for i in range(self.server_tree.topLevelItemCount()):
                item = self.server_tree.topLevelItem(i)
                server_data = item.data(0, Qt.ItemDataRole.UserRole)
                if server_data and server_data.get("port") in selected_ports:
                    item.setSelected(True)

        logger.debug(f"Found {len(servers)} ZMQ servers")

    @pyqtSlot(bool, str)
    def _on_kill_complete(self, success: bool, message: str):
        """Handle kill operation completion on UI thread."""
        if not success:
            QMessageBox.warning(self, "Kill Failed", message)
        # Refresh list after kill (quick refresh for better UX)
        QTimer.singleShot(200, self.refresh_servers)

    def _periodic_cleanup(self):
        """Periodic cleanup of completed executions from tracker.

        Runs every 1 second to remove executions that have been complete for >5 seconds.
        This ensures cleanup happens even if no new progress messages arrive.
        """
        import logging
        import time

        logger = logging.getLogger(__name__)

        logger.info("Periodic cleanup: checking for old executions...")

        # Log all executions before cleanup
        for exec_id, execution in self._progress_tracker.executions.items():
            is_complete = execution.is_complete()
            completed_at = execution.completed_at
            if completed_at:
                elapsed = time.time() - completed_at
                logger.info(
                    f"  Execution {exec_id[:8]}: complete={is_complete}, elapsed={elapsed:.1f}s, should_cleanup={execution.should_cleanup(5.0)}"
                )
            else:
                logger.info(
                    f"  Execution {exec_id[:8]}: complete={is_complete}, completed_at=None"
                )

        self._progress_tracker.cleanup_old_executions(retention_seconds=5.0)

        # NOTE: Do NOT emit _progress_update here!
        # Cleanup should not trigger UI updates - only actual progress messages should.
        # This prevents the loop where cleanup → UI update → populate children → get_all_progress every second

    @pyqtSlot(int)
    def _on_server_killed(self, port: int):
        """Handle server killed event - remove from cache to prevent it from reappearing."""
        if port in self._last_known_servers:
            logger.debug(f"Removing port {port} from server cache after kill")
            del self._last_known_servers[port]

    def quit_selected_servers(self):
        """Gracefully quit selected servers (async to avoid blocking UI)."""
        selected_items = self.server_tree.selectedItems()
        if not selected_items:
            QMessageBox.warning(self, "No Selection", "Please select servers to quit.")
            return

        # Collect ports to kill BEFORE showing dialog (items may be deleted by auto-refresh)
        ports_to_kill = []
        for item in selected_items:
            data = item.data(0, Qt.ItemDataRole.UserRole)
            # Skip worker items (they don't have ports)
            if data and data.get("type") == "worker":
                continue
            port = data.get("port") if data else None
            if port:
                ports_to_kill.append(port)

        if not ports_to_kill:
            QMessageBox.warning(
                self, "No Servers", "No servers selected (only workers selected)."
            )
            return

        # Confirm with user
        reply = QMessageBox.question(
            self,
            "Quit Confirmation",
            f"Gracefully quit {len(ports_to_kill)} server(s)?\n\n"
            "For execution servers: kills workers only, server stays alive.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.Yes,
        )

        if reply != QMessageBox.StandardButton.Yes:
            return

        # Kill in background thread to avoid blocking UI
        def kill_servers():
            from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
            from zmqruntime.client import ZMQClient
            from zmqruntime.queue_tracker import GlobalQueueTrackerRegistry

            failed_ports = []
            registry = GlobalQueueTrackerRegistry()

            for port in ports_to_kill:
                try:
                    logger.info(f"Attempting to quit server on port {port}...")
                    success = ZMQClient.kill_server_on_port(
                        port, graceful=True, config=OPENHCS_ZMQ_CONFIG
                    )
                    if success:
                        logger.info(f"✅ Successfully quit server on port {port}")
                        # Clear queue tracker for this viewer
                        registry.remove_tracker(port)
                        self.server_killed.emit(port)
                    else:
                        failed_ports.append(port)
                        logger.warning(
                            f"❌ Failed to quit server on port {port} (kill_server_on_port returned False)"
                        )
                except Exception as e:
                    failed_ports.append(port)
                    logger.error(f"❌ Error quitting server on port {port}: {e}")

            # Emit completion signal
            if failed_ports:
                self._kill_complete.emit(
                    False, f"Failed to quit servers on ports: {failed_ports}"
                )
            else:
                self._kill_complete.emit(True, "All servers quit successfully")

        spawn_thread_with_context(kill_servers, name="kill_servers")

    def force_kill_selected_servers(self):
        """Force kill selected servers (async to avoid blocking UI)."""
        selected_items = self.server_tree.selectedItems()
        if not selected_items:
            QMessageBox.warning(
                self, "No Selection", "Please select servers to force kill."
            )
            return

        # Collect ports to kill BEFORE showing dialog (items may be deleted by auto-refresh)
        ports_to_kill = []
        for item in selected_items:
            data = item.data(0, Qt.ItemDataRole.UserRole)
            # Skip worker items (they don't have ports)
            if data and data.get("type") == "worker":
                continue
            port = data.get("port") if data else None
            if port:
                ports_to_kill.append(port)

        if not ports_to_kill:
            QMessageBox.warning(
                self, "No Servers", "No servers selected (only workers selected)."
            )
            return

        # Confirm with user
        reply = QMessageBox.question(
            self,
            "Force Kill Confirmation",
            f"Force kill {len(ports_to_kill)} server(s)?\n\n"
            "For execution servers: kills workers AND server.\n"
            "For Napari viewers: kills the viewer process.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        )

        if reply != QMessageBox.StandardButton.Yes:
            return

        def kill_servers():
            """Kill selected servers gracefully or forcefully."""
            from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
            from zmqruntime.client import ZMQClient
            from zmqruntime.queue_tracker import GlobalQueueTrackerRegistry

            failed_ports = []
            registry = GlobalQueueTrackerRegistry()

            for port in ports_to_kill:
                try:
                    logger.info(
                        f"🔥 FORCE KILL: Force killing server on port {port} (kills workers AND server)"
                    )
                    # Use kill_server_on_port with graceful=False
                    # This handles both IPC and TCP modes correctly
                    success = ZMQClient.kill_server_on_port(
                        port, graceful=False, config=OPENHCS_ZMQ_CONFIG
                    )

                    if success:
                        logger.info(
                            f"✅ Successfully force killed server on port {port}"
                        )
                    else:
                        logger.warning(
                            f"⚠️ Force kill returned False for port {port}, but continuing cleanup"
                        )

                    # Clear queue tracker for this viewer (always, regardless of kill result)
                    registry.remove_tracker(port)
                    self.server_killed.emit(port)

                except Exception as e:
                    logger.error(f"❌ Error force killing server on port {port}: {e}")
                    # Still emit signal to trigger refresh and cleanup, even on error
                    registry.remove_tracker(port)
                    self.server_killed.emit(port)

            # Always emit success - we've done our best to kill the processes
            # The refresh will remove any dead entries from the list
            self._kill_complete.emit(
                True, "Force kill operation completed (list will refresh)"
            )

        spawn_thread_with_context(kill_servers, name="force_kill_servers")

    def _on_item_double_clicked(self, item: QTreeWidgetItem):
        """Handle double-click on tree item - open log file."""
        data = item.data(0, Qt.ItemDataRole.UserRole)

        # For worker items, get the server from parent
        if data and data.get("type") == "worker":
            data = data.get("server", {})

        log_file = data.get("log_file_path") if data else None

        if log_file and Path(log_file).exists():
            # Emit signal for parent to handle (e.g., open in log viewer)
            self.log_file_opened.emit(log_file)
            logger.info(f"Opened log file: {log_file}")
        else:
            QMessageBox.information(
                self,
                "No Log File",
                f"No log file available for this item.\n\nPort: {data.get('port', 'unknown') if data else 'unknown'}",
            )
