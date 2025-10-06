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
from PyQt6.QtCore import Qt, pyqtSignal, QTimer
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
        
        # Auto-refresh timer
        self.refresh_timer = QTimer()
        self.refresh_timer.timeout.connect(self.refresh_servers)
        
        self.setup_ui()
        
        # Initial scan
        self.refresh_servers()
    
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
    
    def refresh_servers(self):
        """Scan ports and refresh server list."""
        from openhcs.runtime.zmq_base import ZMQClient
        
        # Scan for servers
        self.servers = ZMQClient.scan_servers(self.ports_to_scan)
        
        # Update list
        self.server_list.clear()
        
        for server in self.servers:
            port = server.get('port', 'unknown')
            server_type = server.get('server', 'Unknown')
            ready = server.get('ready', False)
            log_file = server.get('log_file_path', None)
            
            # Determine status icon
            if ready:
                status_icon = "✅"
            else:
                status_icon = "🚀"
            
            # Build display text
            display_text = f"{status_icon} Port {port} - {server_type}"
            
            # Add extra info for execution servers
            if server_type == 'ZMQExecutionServer':
                active_execs = server.get('active_executions', 0)
                if active_execs > 0:
                    display_text += f" ({active_execs} active)"
            
            # Create list item
            item = QListWidgetItem(display_text)
            item.setData(Qt.ItemDataRole.UserRole, server)
            self.server_list.addItem(item)
        
        logger.debug(f"Found {len(self.servers)} ZMQ servers")
    
    def quit_selected_servers(self):
        """Gracefully quit selected servers."""
        selected_items = self.server_list.selectedItems()
        if not selected_items:
            QMessageBox.warning(self, "No Selection", "Please select servers to quit.")
            return
        
        # Confirm with user
        reply = QMessageBox.question(
            self,
            "Quit Confirmation",
            f"Gracefully quit {len(selected_items)} server(s)?\n\n"
            "Servers with active executions will reject the shutdown request.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.Yes
        )
        
        if reply != QMessageBox.StandardButton.Yes:
            return
        
        # Kill each selected server
        from openhcs.runtime.zmq_base import ZMQClient
        
        for item in selected_items:
            server = item.data(Qt.ItemDataRole.UserRole)
            port = server.get('port')
            
            if port:
                success = ZMQClient.kill_server_on_port(port, graceful=True)
                if success:
                    logger.info(f"Quit server on port {port}")
                    self.server_killed.emit(port)
                else:
                    logger.warning(f"Failed to quit server on port {port}")
        
        # Refresh list after a delay
        QTimer.singleShot(1000, self.refresh_servers)
    
    def force_kill_selected_servers(self):
        """Force kill selected servers without verification."""
        selected_items = self.server_list.selectedItems()
        if not selected_items:
            QMessageBox.warning(self, "No Selection", "Please select servers to force kill.")
            return
        
        # Confirm with user
        reply = QMessageBox.question(
            self,
            "Force Kill Confirmation",
            f"Force kill {len(selected_items)} server(s) without verification?\n\n"
            "This will immediately kill any process listening on the selected ports.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No
        )
        
        if reply != QMessageBox.StandardButton.Yes:
            return
        
        # Kill each selected server
        from openhcs.runtime.zmq_base import ZMQClient
        
        for item in selected_items:
            server = item.data(Qt.ItemDataRole.UserRole)
            port = server.get('port')
            
            if port:
                success = ZMQClient.kill_server_on_port(port, graceful=False)
                if success:
                    logger.info(f"Force killed server on port {port}")
                    self.server_killed.emit(port)
                else:
                    logger.warning(f"Failed to force kill server on port {port}")
        
        # Refresh list after a delay
        QTimer.singleShot(1000, self.refresh_servers)
    
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
    
    def start_auto_refresh(self, interval_ms: int = 5000):
        """
        Start automatic refresh timer.
        
        Args:
            interval_ms: Refresh interval in milliseconds (default: 5 seconds)
        """
        self.refresh_timer.start(interval_ms)
        logger.debug(f"Auto-refresh started ({interval_ms}ms interval)")
    
    def stop_auto_refresh(self):
        """Stop automatic refresh timer."""
        self.refresh_timer.stop()
        logger.debug("Auto-refresh stopped")

