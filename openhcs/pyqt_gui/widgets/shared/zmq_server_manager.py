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
"""

import logging
from pathlib import Path
from typing import List, Dict, Any, Optional
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QTreeWidget, QTreeWidgetItem,
    QPushButton, QGroupBox, QMessageBox, QAbstractItemView
)
from PyQt6.QtCore import Qt, pyqtSignal, pyqtSlot, QTimer
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
import threading

logger = logging.getLogger(__name__)


# Global registry for launching viewers
# Format: {port: {'type': 'napari'|'fiji', 'queued_images': int, 'start_time': float}}
_launching_viewers_lock = threading.Lock()
_launching_viewers: Dict[int, Dict[str, Any]] = {}


# Global reference to active ZMQ server manager widgets (for triggering refreshes)
_active_managers_lock = threading.Lock()
_active_managers: List['ZMQServerManagerWidget'] = []


def register_launching_viewer(port: int, viewer_type: str, queued_images: int = 0):
    """Register a viewer that is launching and trigger UI refresh.

    If the viewer is already launching, accumulates the queue count instead of replacing it.
    """
    import time
    with _launching_viewers_lock:
        if port in _launching_viewers:
            # Already launching - accumulate queue count
            _launching_viewers[port]['queued_images'] += queued_images
            logger.info(f"Updated launching {viewer_type} viewer on port {port}: added {queued_images} images (total: {_launching_viewers[port]['queued_images']})")
        else:
            # New launching viewer
            _launching_viewers[port] = {
                'type': viewer_type,
                'queued_images': queued_images,
                'start_time': time.time()
            }
            logger.info(f"Registered launching {viewer_type} viewer on port {port} with {queued_images} queued images")

    # Trigger immediate refresh on all active managers (fast path - no port scan)
    _trigger_manager_refresh_fast()


def update_launching_viewer_queue(port: int, queued_images: int):
    """Update the queued image count for a launching viewer and trigger UI refresh.

    This SETS the queue count (doesn't accumulate). Use register_launching_viewer() to add images.
    """
    with _launching_viewers_lock:
        if port in _launching_viewers:
            _launching_viewers[port]['queued_images'] = queued_images
            logger.debug(f"Updated launching viewer on port {port}: {queued_images} queued images")

    # Trigger immediate refresh on all active managers (fast path - no port scan)
    _trigger_manager_refresh_fast()


def unregister_launching_viewer(port: int):
    """Remove a viewer from the launching registry (it's now ready) and trigger UI refresh."""
    with _launching_viewers_lock:
        if port in _launching_viewers:
            del _launching_viewers[port]
            logger.info(f"Unregistered launching viewer on port {port} (now ready)")

    # Trigger full refresh to pick up the now-ready viewer via port scan
    _trigger_manager_refresh_full()


def _trigger_manager_refresh_fast():
    """Trigger fast refresh (launching viewers only, no port scan) on all active managers."""
    with _active_managers_lock:
        for manager in _active_managers:
            try:
                # Use QMetaObject to safely call from any thread
                from PyQt6.QtCore import QMetaObject, Qt
                QMetaObject.invokeMethod(
                    manager,
                    "_refresh_launching_viewers_only",
                    Qt.ConnectionType.QueuedConnection
                )
            except Exception as e:
                logger.debug(f"Failed to trigger fast refresh on manager: {e}")


def _trigger_manager_refresh_full():
    """Trigger full refresh (port scan + launching viewers) on all active managers."""
    with _active_managers_lock:
        for manager in _active_managers:
            try:
                # Use QMetaObject to safely call from any thread
                from PyQt6.QtCore import QMetaObject, Qt
                QMetaObject.invokeMethod(
                    manager,
                    "refresh_servers",
                    Qt.ConnectionType.QueuedConnection
                )
            except Exception as e:
                logger.debug(f"Failed to trigger full refresh on manager: {e}")


def get_launching_viewers() -> Dict[int, Dict[str, Any]]:
    """Get a copy of the launching viewers registry."""
    with _launching_viewers_lock:
        return dict(_launching_viewers)


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

        # Register this manager for launching viewer updates
        with _active_managers_lock:
            _active_managers.append(self)

        # Connect internal signal for async scanning
        self._scan_complete.connect(self._update_server_list)

        # Auto-refresh timer (async scanning won't block UI)
        self.refresh_timer = QTimer()
        self.refresh_timer.timeout.connect(self.refresh_servers)

        # Cleanup flag to prevent operations after cleanup
        self._is_cleaning_up = False

        self.setup_ui()

    def cleanup(self):
        """Cleanup resources before widget destruction."""
        if self._is_cleaning_up:
            return

        self._is_cleaning_up = True

        # Stop refresh timer first to prevent new refresh calls
        if hasattr(self, 'refresh_timer') and self.refresh_timer:
            self.refresh_timer.stop()
            self.refresh_timer.deleteLater()
            self.refresh_timer = None

        # Unregister this manager from global list
        with _active_managers_lock:
            if self in _active_managers:
                _active_managers.remove(self)

        logger.debug("ZMQServerManagerWidget cleanup completed")

    def __del__(self):
        """Cleanup when widget is destroyed."""
        self.cleanup()

    def showEvent(self, event):
        """Auto-scan for servers when widget is shown."""
        super().showEvent(event)
        if not self._is_cleaning_up:
            # Scan for servers on first show
            self.refresh_servers()
            # Start auto-refresh (1 second interval - async scanning won't block UI)
            if self.refresh_timer:
                self.refresh_timer.start(1000)

    def hideEvent(self, event):
        """Stop auto-refresh when widget is hidden."""
        super().hideEvent(event)
        # Stop timer to prevent unnecessary background work
        if hasattr(self, 'refresh_timer') and self.refresh_timer:
            self.refresh_timer.stop()

    def setup_ui(self):
        """Setup the user interface."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        
        # Group box
        group_box = QGroupBox(self.title)
        group_layout = QVBoxLayout(group_box)
        group_layout.setContentsMargins(5, 5, 5, 5)

        # Server tree (hierarchical display with workers as children)
        self.server_tree = QTreeWidget()
        self.server_tree.setHeaderLabels(["Server / Worker", "Status", "Info"])
        self.server_tree.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.server_tree.itemDoubleClicked.connect(self._on_item_double_clicked)
        self.server_tree.setColumnWidth(0, 250)
        self.server_tree.setColumnWidth(1, 100)
        group_layout.addWidget(self.server_tree)
        
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
            # Apply button styles
            self.refresh_btn.setStyleSheet(self.style_generator.generate_button_style())
            self.quit_btn.setStyleSheet(self.style_generator.generate_button_style())
            self.force_kill_btn.setStyleSheet(self.style_generator.generate_button_style())

            # Apply tree widget style (uses existing method)
            self.server_tree.setStyleSheet(self.style_generator.generate_tree_widget_style())

            # Apply group box style
            cs = self.style_generator.color_scheme
            group_box.setStyleSheet(f"""
                QGroupBox {{
                    background-color: {cs.to_hex(cs.panel_bg)};
                    border: 1px solid {cs.to_hex(cs.border_color)};
                    border-radius: 4px;
                    margin-top: 8px;
                    padding-top: 8px;
                    font-weight: bold;
                    color: {cs.to_hex(cs.text_accent)};
                }}
                QGroupBox::title {{
                    subcontrol-origin: margin;
                    subcontrol-position: top left;
                    padding: 2px 5px;
                    color: {cs.to_hex(cs.text_accent)};
                }}
            """)

        # Connect internal signals
        self._scan_complete.connect(self._update_server_list)
        self._kill_complete.connect(self._on_kill_complete)
    
    def refresh_servers(self):
        """Scan ports and refresh server list (async in background)."""
        # Guard against calls after cleanup
        if self._is_cleaning_up:
            return

        import threading

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
            control_socket.setsockopt(zmq.RCVTIMEO, 300)  # 300ms timeout for fast scanning
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
        from openhcs.runtime.queue_tracker import GlobalQueueTrackerRegistry

        self.servers = servers

        # Save current selection (by port) before clearing
        selected_ports = set()
        for item in self.server_tree.selectedItems():
            server_data = item.data(0, Qt.ItemDataRole.UserRole)
            if server_data and 'port' in server_data:
                selected_ports.add(server_data['port'])

        self.server_tree.clear()

        # Get queue tracker registry for progress info
        registry = GlobalQueueTrackerRegistry()

        # First, add launching viewers
        launching_viewers = get_launching_viewers()
        for port, info in launching_viewers.items():
            viewer_type = info['type'].capitalize()
            queued_images = info['queued_images']

            display_text = f"Port {port} - {viewer_type} Viewer"
            status_text = "🚀 Launching"
            info_text = f"{queued_images} images queued" if queued_images > 0 else "Starting..."

            item = QTreeWidgetItem([display_text, status_text, info_text])
            item.setData(0, Qt.ItemDataRole.UserRole, {'port': port, 'launching': True})
            self.server_tree.addTopLevelItem(item)

        # Add servers that are processing images (even if they didn't respond to ping)
        # This prevents busy servers from disappearing during image processing
        scanned_ports = {server.get('port') for server in servers}
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
                    'port': tracker_port,
                    'server': f'{viewer_type}ViewerServer',
                    'ready': True,
                    'busy': True  # Mark as busy
                }

                item = QTreeWidgetItem([display_text, status_text, info_text])
                item.setData(0, Qt.ItemDataRole.UserRole, pseudo_server)
                self.server_tree.addTopLevelItem(item)

        # Then add running servers
        for server in servers:
            port = server.get('port', 'unknown')

            # Skip if this port is in launching registry (shouldn't happen, but be safe)
            if port in launching_viewers:
                continue

            server_type = server.get('server', 'Unknown')
            ready = server.get('ready', False)

            # Determine status icon
            if ready:
                status_icon = "✅"
            else:
                status_icon = "🚀"

            # Handle execution servers specially - show workers as children
            if server_type == 'ZMQExecutionServer':
                running_executions = server.get('running_executions', [])
                workers = server.get('workers', [])

                # Create server item
                if running_executions:
                    server_text = f"Port {port} - Execution Server"
                    status_text = f"{status_icon} {len(running_executions)} exec"
                    info_text = f"{len(workers)} workers"
                else:
                    server_text = f"Port {port} - Execution Server"
                    status_text = f"{status_icon} Idle"
                    info_text = f"{len(workers)} workers" if workers else ""

                server_item = QTreeWidgetItem([server_text, status_text, info_text])
                server_item.setData(0, Qt.ItemDataRole.UserRole, server)
                self.server_tree.addTopLevelItem(server_item)

                # Add worker processes as children
                for worker in workers:
                    pid = worker.get('pid', 'unknown')
                    status = worker.get('status', 'unknown')
                    cpu = worker.get('cpu_percent', 0)
                    mem_mb = worker.get('memory_mb', 0)

                    worker_text = f"  Worker PID {pid}"
                    worker_status = f"⚙️ {status}"
                    worker_info = f"CPU: {cpu:.1f}% | Mem: {mem_mb:.0f}MB"

                    worker_item = QTreeWidgetItem([worker_text, worker_status, worker_info])
                    worker_item.setData(0, Qt.ItemDataRole.UserRole, {'type': 'worker', 'pid': pid, 'server': server})
                    server_item.addChild(worker_item)

                # Expand server item if it has workers
                if workers:
                    server_item.setExpanded(True)

            else:
                # Other server types (Napari, Fiji viewers) - show with progress if available
                display_text = f"Port {port} - {server_type}"
                status_text = status_icon
                info_text = ""

                # Check if this is a viewer with pending images
                tracker = registry.get_tracker(port)
                if tracker:
                    processed, total = tracker.get_progress()
                    pending = tracker.get_pending_count()

                    if pending > 0:
                        # Still processing images
                        info_text = f"Processing: {processed}/{total} images"

                        # Check for stuck images
                        if tracker.has_stuck_images():
                            status_text = "⚠️"  # Warning icon for stuck
                            stuck_images = tracker.get_stuck_images()
                            info_text += f" (⚠️ {len(stuck_images)} stuck)"
                    elif total > 0:
                        # All images processed
                        info_text = f"✅ Processed {total} images"

                # If no processing info, show memory usage
                if not info_text:
                    mem_mb = server.get('memory_mb')
                    cpu_percent = server.get('cpu_percent')
                    if mem_mb is not None:
                        info_text = f"Mem: {mem_mb:.0f}MB"
                        if cpu_percent is not None:
                            info_text += f" | CPU: {cpu_percent:.1f}%"

                item = QTreeWidgetItem([display_text, status_text, info_text])
                item.setData(0, Qt.ItemDataRole.UserRole, server)
                self.server_tree.addTopLevelItem(item)

        # Restore selection after refresh
        if selected_ports:
            for i in range(self.server_tree.topLevelItemCount()):
                item = self.server_tree.topLevelItem(i)
                server_data = item.data(0, Qt.ItemDataRole.UserRole)
                if server_data and server_data.get('port') in selected_ports:
                    item.setSelected(True)

        logger.debug(f"Found {len(servers)} ZMQ servers")

    @pyqtSlot(bool, str)
    def _on_kill_complete(self, success: bool, message: str):
        """Handle kill operation completion on UI thread."""
        if not success:
            QMessageBox.warning(self, "Kill Failed", message)
        # Refresh list after kill (quick refresh for better UX)
        QTimer.singleShot(200, self.refresh_servers)
    
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
            if data and data.get('type') == 'worker':
                continue
            port = data.get('port') if data else None
            if port:
                ports_to_kill.append(port)

        if not ports_to_kill:
            QMessageBox.warning(self, "No Servers", "No servers selected (only workers selected).")
            return

        # Confirm with user
        reply = QMessageBox.question(
            self,
            "Quit Confirmation",
            f"Gracefully quit {len(ports_to_kill)} server(s)?\n\n"
            "For execution servers: kills workers only, server stays alive.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.Yes
        )

        if reply != QMessageBox.StandardButton.Yes:
            return

        # Kill in background thread to avoid blocking UI
        import threading

        def kill_servers():
            from openhcs.runtime.zmq_base import ZMQClient
            from openhcs.runtime.queue_tracker import GlobalQueueTrackerRegistry
            failed_ports = []
            registry = GlobalQueueTrackerRegistry()

            for port in ports_to_kill:
                try:
                    logger.info(f"Attempting to quit server on port {port}...")
                    success = ZMQClient.kill_server_on_port(port, graceful=True)
                    if success:
                        logger.info(f"✅ Successfully quit server on port {port}")
                        # Clear queue tracker for this viewer
                        registry.remove_tracker(port)
                        self.server_killed.emit(port)
                    else:
                        failed_ports.append(port)
                        logger.warning(f"❌ Failed to quit server on port {port} (kill_server_on_port returned False)")
                except Exception as e:
                    failed_ports.append(port)
                    logger.error(f"❌ Error quitting server on port {port}: {e}")

            # Emit completion signal
            if failed_ports:
                self._kill_complete.emit(False, f"Failed to quit servers on ports: {failed_ports}")
            else:
                self._kill_complete.emit(True, "All servers quit successfully")

        thread = threading.Thread(target=kill_servers, daemon=True)
        thread.start()
    
    def force_kill_selected_servers(self):
        """Force kill selected servers (async to avoid blocking UI)."""
        selected_items = self.server_tree.selectedItems()
        if not selected_items:
            QMessageBox.warning(self, "No Selection", "Please select servers to force kill.")
            return

        # Collect ports to kill BEFORE showing dialog (items may be deleted by auto-refresh)
        ports_to_kill = []
        for item in selected_items:
            data = item.data(0, Qt.ItemDataRole.UserRole)
            # Skip worker items (they don't have ports)
            if data and data.get('type') == 'worker':
                continue
            port = data.get('port') if data else None
            if port:
                ports_to_kill.append(port)

        if not ports_to_kill:
            QMessageBox.warning(self, "No Servers", "No servers selected (only workers selected).")
            return

        # Confirm with user
        reply = QMessageBox.question(
            self,
            "Force Kill Confirmation",
            f"Force kill {len(ports_to_kill)} server(s)?\n\n"
            "For execution servers: kills workers AND server.\n"
            "For Napari viewers: kills the viewer process.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No
        )

        if reply != QMessageBox.StandardButton.Yes:
            return

        # Kill in background thread to avoid blocking UI
        import threading

        def kill_servers():
            from openhcs.runtime.zmq_base import ZMQServer
            from openhcs.runtime.queue_tracker import GlobalQueueTrackerRegistry
            registry = GlobalQueueTrackerRegistry()

            for port in ports_to_kill:
                try:
                    logger.info(f"🔥 FORCE KILL: Killing processes on port {port} (nuclear option - no ZMQ, direct process kill)")
                    # Force kill: Skip ZMQ entirely, go straight to process killing
                    # This is the nuclear option - it ALWAYS works
                    killed = ZMQServer.kill_processes_on_port(port)
                    # Also try port+1000 (data port for execution servers)
                    killed += ZMQServer.kill_processes_on_port(port + 1000)

                    if killed > 0:
                        logger.info(f"✅ Force killed {killed} process(es) on port {port}")
                    else:
                        # No processes found on port - this is SUCCESS, not failure!
                        # The goal is to ensure no process is running, and that's achieved.
                        logger.info(f"✅ No processes found on port {port} (already dead or never existed)")

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
            self._kill_complete.emit(True, "Force kill operation completed (list will refresh)")

        thread = threading.Thread(target=kill_servers, daemon=True)
        thread.start()
    
    def _on_item_double_clicked(self, item: QTreeWidgetItem):
        """Handle double-click on tree item - open log file."""
        data = item.data(0, Qt.ItemDataRole.UserRole)

        # For worker items, get the server from parent
        if data and data.get('type') == 'worker':
            data = data.get('server', {})

        log_file = data.get('log_file_path') if data else None

        if log_file and Path(log_file).exists():
            # Emit signal for parent to handle (e.g., open in log viewer)
            self.log_file_opened.emit(log_file)
            logger.info(f"Opened log file: {log_file}")
        else:
            QMessageBox.information(
                self,
                "No Log File",
                f"No log file available for this item.\n\nPort: {data.get('port', 'unknown') if data else 'unknown'}"
            )

