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
"""

import logging
from pathlib import Path
from typing import List, Dict, Any, Optional
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QListWidget, QListWidgetItem,
    QPushButton, QGroupBox, QMessageBox, QAbstractItemView
)
from PyQt6.QtCore import Qt, pyqtSignal, pyqtSlot, QTimer, QThread
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator

logger = logging.getLogger(__name__)


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
    _kill_complete = pyqtSignal(bool, str)  # Internal signal for async kill completion (success, message)

    def __init__(
        self,
        ports_to_scan: List[int],
        title: str = "ZMQ Servers",
        style_generator: Optional[StyleSheetGenerator] = None,
        parent: Optional[QWidget] = None
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

        # Connect internal signal for async scanning
        self._scan_complete.connect(self._update_server_list)

        # Auto-refresh timer (async scanning won't block UI)
        self.refresh_timer = QTimer()
        self.refresh_timer.timeout.connect(self.refresh_servers)

        self.setup_ui()

    def showEvent(self, event):
        """Auto-scan for servers when widget is shown."""
        super().showEvent(event)
        # Scan for servers on first show
        self.refresh_servers()
        # Start auto-refresh (10 second interval - async won't block UI)
        self.refresh_timer.start(10000)

    def setup_ui(self):
        """Setup the user interface."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        
        # Group box
        group_box = QGroupBox(self.title)
        group_layout = QVBoxLayout(group_box)
        group_layout.setContentsMargins(5, 5, 5, 5)
        
        # Server list
        self.server_list = QListWidget()
        self.server_list.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.server_list.itemDoubleClicked.connect(self._on_item_double_clicked)
        group_layout.addWidget(self.server_list)
        
        # Buttons
        button_layout = QHBoxLayout()
        
        self.refresh_btn = QPushButton("Refresh")
        self.refresh_btn.clicked.connect(self.refresh_servers)
        button_layout.addWidget(self.refresh_btn)
        
        self.quit_btn = QPushButton("Quit")
        self.quit_btn.clicked.connect(self.quit_selected_servers)
        button_layout.addWidget(self.quit_btn)
        
        self.force_kill_btn = QPushButton("Force Kill")
        self.force_kill_btn.clicked.connect(self.force_kill_selected_servers)
        button_layout.addWidget(self.force_kill_btn)
        
        group_layout.addLayout(button_layout)
        
        layout.addWidget(group_box)
        
        # Apply styling
        if self.style_generator:
            self.setStyleSheet(self.style_generator.generate_plate_manager_style())
            self.refresh_btn.setStyleSheet(self.style_generator.generate_button_style())
            self.quit_btn.setStyleSheet(self.style_generator.generate_button_style())
            self.force_kill_btn.setStyleSheet(self.style_generator.generate_button_style())

        # Connect internal signals
        self._scan_complete.connect(self._update_server_list)
        self._kill_complete.connect(self._on_kill_complete)
    
    def refresh_servers(self):
        """Scan ports and refresh server list (async in background)."""
        import threading

        def scan_and_update():
            """Background thread to scan ports without blocking UI."""
            from openhcs.runtime.zmq_base import ZMQClient
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
        thread = threading.Thread(target=scan_and_update, daemon=True)
        thread.start()

    def _ping_server(self, port: int) -> Optional[Dict[str, Any]]:
        """
        Ping a server on the given port and return its info.

        Returns server info dict if responsive, None otherwise.
        """
        import zmq
        import pickle

        control_port = port + 1000
        control_context = None
        control_socket = None

        try:
            control_context = zmq.Context()
            control_socket = control_context.socket(zmq.REQ)
            control_socket.setsockopt(zmq.LINGER, 0)
            control_socket.setsockopt(zmq.RCVTIMEO, 1000)  # 1 second timeout (servers may be busy)
            control_socket.connect(f"tcp://localhost:{control_port}")

            # Send ping
            ping_message = {'type': 'ping'}
            control_socket.send(pickle.dumps(ping_message))

            # Wait for pong
            response = control_socket.recv()
            response_data = pickle.loads(response)

            # Return server info if valid pong
            if response_data.get('type') == 'pong':
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

    @pyqtSlot(list)
    def _update_server_list(self, servers: List[Dict[str, Any]]):
        """Update server list on UI thread (called via signal)."""
        self.servers = servers
        self.server_list.clear()

        for server in servers:
            port = server.get('port', 'unknown')
            server_type = server.get('server', 'Unknown')
            ready = server.get('ready', False)

            # Determine status icon
            if ready:
                status_icon = "✅ Ready"
            else:
                status_icon = "🚀 Starting"

            # Build display text
            display_text = f"Port {port} - {status_icon}"

            # Handle execution servers specially - show each running execution
            if server_type == 'ZMQExecutionServer':
                running_executions = server.get('running_executions', [])

                if running_executions:
                    # Show server entry
                    server_text = f"Port {port} - Execution Server ({len(running_executions)} running)"
                    server_item = QListWidgetItem(server_text)
                    server_item.setData(Qt.ItemDataRole.UserRole, server)
                    self.server_list.addItem(server_item)

                    # Show each running execution as indented sub-item
                    for exec_info in running_executions:
                        exec_id = exec_info.get('execution_id', 'unknown')[:8]  # Short ID
                        plate_id = exec_info.get('plate_id', 'unknown')
                        elapsed = exec_info.get('elapsed', 0)

                        # Format elapsed time
                        if elapsed < 60:
                            time_str = f"{elapsed:.0f}s"
                        elif elapsed < 3600:
                            time_str = f"{elapsed/60:.1f}m"
                        else:
                            time_str = f"{elapsed/3600:.1f}h"

                        exec_text = f"  ⏳ {exec_id} - {plate_id} ({time_str})"
                        exec_item = QListWidgetItem(exec_text)
                        # Store execution info with server context
                        exec_data = server.copy()
                        exec_data['execution_id'] = exec_info.get('execution_id')
                        exec_item.setData(Qt.ItemDataRole.UserRole, exec_data)
                        self.server_list.addItem(exec_item)
                else:
                    # No running executions - show idle server
                    display_text = f"Port {port} - Execution Server (idle)"
                    item = QListWidgetItem(display_text)
                    item.setData(Qt.ItemDataRole.UserRole, server)
                    self.server_list.addItem(item)
            else:
                # Other server types (Napari, etc.) - show normally
                item = QListWidgetItem(display_text)
                item.setData(Qt.ItemDataRole.UserRole, server)
                self.server_list.addItem(item)

        logger.debug(f"Found {len(servers)} ZMQ servers")

    @pyqtSlot(bool, str)
    def _on_kill_complete(self, success: bool, message: str):
        """Handle kill operation completion on UI thread."""
        if not success:
            QMessageBox.warning(self, "Kill Failed", message)
        # Refresh list after kill
        QTimer.singleShot(1000, self.refresh_servers)
    
    def quit_selected_servers(self):
        """Gracefully quit selected servers (async to avoid blocking UI)."""
        selected_items = self.server_list.selectedItems()
        if not selected_items:
            QMessageBox.warning(self, "No Selection", "Please select servers to quit.")
            return

        # Confirm with user
        reply = QMessageBox.question(
            self,
            "Quit Confirmation",
            f"Gracefully quit {len(selected_items)} server(s)?\n\n"
            "For execution servers: kills workers only, server stays alive.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.Yes
        )

        if reply != QMessageBox.StandardButton.Yes:
            return

        # Collect ports to kill
        ports_to_kill = []
        for item in selected_items:
            server = item.data(Qt.ItemDataRole.UserRole)
            port = server.get('port')
            if port:
                ports_to_kill.append(port)

        # Kill in background thread to avoid blocking UI
        import threading

        def kill_servers():
            from openhcs.runtime.zmq_base import ZMQClient
            failed_ports = []

            for port in ports_to_kill:
                try:
                    success = ZMQClient.kill_server_on_port(port, graceful=True)
                    if success:
                        logger.info(f"Quit server on port {port}")
                        self.server_killed.emit(port)
                    else:
                        failed_ports.append(port)
                        logger.warning(f"Failed to quit server on port {port}")
                except Exception as e:
                    failed_ports.append(port)
                    logger.error(f"Error quitting server on port {port}: {e}")

            # Emit completion signal
            if failed_ports:
                self._kill_complete.emit(False, f"Failed to quit servers on ports: {failed_ports}")
            else:
                self._kill_complete.emit(True, "All servers quit successfully")

        thread = threading.Thread(target=kill_servers, daemon=True)
        thread.start()
    
    def force_kill_selected_servers(self):
        """Force kill selected servers (async to avoid blocking UI)."""
        selected_items = self.server_list.selectedItems()
        if not selected_items:
            QMessageBox.warning(self, "No Selection", "Please select servers to force kill.")
            return

        # Confirm with user
        reply = QMessageBox.question(
            self,
            "Force Kill Confirmation",
            f"Force kill {len(selected_items)} server(s)?\n\n"
            "For execution servers: kills workers AND server.\n"
            "For Napari viewers: kills the viewer process.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No
        )

        if reply != QMessageBox.StandardButton.Yes:
            return

        # Collect ports to kill
        ports_to_kill = []
        for item in selected_items:
            server = item.data(Qt.ItemDataRole.UserRole)
            port = server.get('port')
            if port:
                ports_to_kill.append(port)

        # Kill in background thread to avoid blocking UI
        import threading

        def kill_servers():
            from openhcs.runtime.zmq_base import ZMQClient
            failed_ports = []

            for port in ports_to_kill:
                try:
                    success = ZMQClient.kill_server_on_port(port, graceful=False)
                    if success:
                        logger.info(f"Force killed server on port {port}")
                        self.server_killed.emit(port)
                    else:
                        failed_ports.append(port)
                        logger.warning(f"Failed to force kill server on port {port}")
                except Exception as e:
                    failed_ports.append(port)
                    logger.error(f"Error force killing server on port {port}: {e}")

            # Emit completion signal
            if failed_ports:
                self._kill_complete.emit(False, f"Failed to force kill servers on ports: {failed_ports}")
            else:
                self._kill_complete.emit(True, "All servers force killed successfully")

        thread = threading.Thread(target=kill_servers, daemon=True)
        thread.start()
    
    def _on_item_double_clicked(self, item: QListWidgetItem):
        """Handle double-click on server item - open log file."""
        server = item.data(Qt.ItemDataRole.UserRole)
        log_file = server.get('log_file_path')

        if log_file and Path(log_file).exists():
            # Emit signal for parent to handle (e.g., open in log viewer)
            self.log_file_opened.emit(log_file)
            logger.info(f"Opened log file: {log_file}")
        else:
            QMessageBox.information(
                self,
                "No Log File",
                f"No log file available for this server.\n\nPort: {server.get('port', 'unknown')}"
            )

