"""
Image Browser Widget for PyQt6 GUI.

Displays a table of all image files from plate metadata and allows users to
view them in Napari with configurable display settings.
"""

import logging
from pathlib import Path
from typing import Optional, List, Dict, Any, Set

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QTableWidget, QTableWidgetItem,
    QPushButton, QLabel, QHeaderView, QAbstractItemView, QMessageBox,
    QSplitter, QGroupBox, QTreeWidget, QTreeWidgetItem, QScrollArea,
    QLineEdit, QListWidget, QListWidgetItem
)
from PyQt6.QtCore import Qt, pyqtSignal, pyqtSlot
from PyQt6.QtGui import QFont

from openhcs.constants.constants import Backend
from openhcs.io.filemanager import FileManager
from openhcs.io.base import storage_registry
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator

logger = logging.getLogger(__name__)


class ImageBrowserWidget(QWidget):
    """
    Image browser widget that displays all image files from plate metadata.
    
    Users can click on files to view them in Napari with configurable settings
    from the current PipelineConfig.
    """
    
    # Signals
    image_selected = pyqtSignal(str)  # Emitted when an image is selected
    _instance_scan_complete = pyqtSignal(object)  # Internal signal for async scan completion
    
    def __init__(self, orchestrator=None, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        super().__init__(parent)
        
        self.orchestrator = orchestrator
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.style_gen = StyleSheetGenerator(self.color_scheme)
        self.filemanager = FileManager(storage_registry)

        # Napari viewer tracking
        self.napari_viewers = {}  # port -> NapariStreamVisualizer instance

        # Image queue for pending napari streams
        self.pending_napari_queue = []  # List of (filename, image_data, config) tuples

        # Lazy Napari config widget (will be created in init_ui)
        self.napari_config_form = None
        self.lazy_napari_config = None

        # Image data tracking
        self.all_images = {}  # filename -> metadata dict
        self.filtered_images = {}  # filename -> metadata dict (after search/filter)

        # Connect internal signal for async instance scanning
        self._instance_scan_complete.connect(self._update_instance_list)

        self.init_ui()

        # Load images if orchestrator is provided
        if self.orchestrator:
            self.load_images()

    def showEvent(self, event):
        """Auto-scan for Napari instances when window is shown."""
        super().showEvent(event)
        # Scan for instances on first show
        self.refresh_napari_instances()

    def init_ui(self):
        """Initialize the user interface."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(10)

        # Header
        header_layout = QHBoxLayout()

        title_label = QLabel("Image Browser")
        title_label.setFont(QFont("Arial", 14, QFont.Weight.Bold))
        title_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};")
        header_layout.addWidget(title_label)

        header_layout.addStretch()

        # Refresh button
        self.refresh_btn = QPushButton("Refresh")
        self.refresh_btn.clicked.connect(self.load_images)
        self.refresh_btn.setStyleSheet(self.style_gen.generate_button_style())
        header_layout.addWidget(self.refresh_btn)

        layout.addLayout(header_layout)

        # Search input row (separate from header, matches function selector)
        search_layout = QHBoxLayout()

        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("Search images by filename or metadata...")
        self.search_input.textChanged.connect(self.filter_images)
        # Apply same styling as function selector
        self.search_input.setStyleSheet(f"""
            QLineEdit {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.input_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.input_text)};
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.input_border)};
                border-radius: 3px;
                padding: 5px;
            }}
            QLineEdit:focus {{
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.input_focus_border)};
            }}
        """)
        search_layout.addWidget(self.search_input)

        layout.addLayout(search_layout)

        # Image count label (below search)
        self.image_count_label = QLabel("Images: 0")
        self.image_count_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_secondary)};")
        layout.addWidget(self.image_count_label)

        # Create main splitter (tree | table | config)
        main_splitter = QSplitter(Qt.Orientation.Horizontal)

        # Left: Folder tree
        tree_widget = self._create_folder_tree()
        main_splitter.addWidget(tree_widget)

        # Middle: Image table
        table_widget = self._create_table_widget()
        main_splitter.addWidget(table_widget)

        # Right: Napari config panel + instance manager
        right_panel = self._create_right_panel()
        main_splitter.addWidget(right_panel)

        # Set initial splitter sizes (20% tree, 50% table, 30% config)
        main_splitter.setSizes([200, 500, 300])

        # Add splitter with stretch factor to fill vertical space
        layout.addWidget(main_splitter, 1)

        # Action buttons
        button_layout = QHBoxLayout()
        
        self.view_napari_btn = QPushButton("View in Napari")
        self.view_napari_btn.clicked.connect(self.view_selected_in_napari)
        self.view_napari_btn.setStyleSheet(self.style_gen.generate_button_style())
        self.view_napari_btn.setEnabled(False)
        button_layout.addWidget(self.view_napari_btn)
        
        button_layout.addStretch()
        
        # Info label
        self.info_label = QLabel("No images loaded")
        self.info_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_disabled)};")
        button_layout.addWidget(self.info_label)
        
        layout.addLayout(button_layout)
        
        # Connect selection change
        self.image_table.itemSelectionChanged.connect(self.on_selection_changed)

    def _create_folder_tree(self):
        """Create folder tree widget for filtering images by directory."""
        tree = QTreeWidget()
        tree.setHeaderLabel("Folders")
        tree.setMinimumWidth(150)

        # Apply styling
        tree.setStyleSheet(self.style_gen.generate_tree_widget_style())

        # Connect selection to filter table
        tree.itemSelectionChanged.connect(self.on_folder_selection_changed)

        # Store reference
        self.folder_tree = tree

        return tree

    def _create_table_widget(self):
        """Create and configure the image table widget."""
        table_container = QWidget()
        layout = QVBoxLayout(table_container)
        layout.setContentsMargins(0, 0, 0, 0)

        # Image table (columns will be set dynamically based on parser metadata)
        self.image_table = QTableWidget()
        self.image_table.setColumnCount(1)  # Start with just filename
        self.image_table.setHorizontalHeaderLabels(["Filename"])

        # Configure table
        self.image_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.image_table.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)  # Enable multi-selection
        self.image_table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.image_table.setSortingEnabled(True)

        # Configure header - make all columns resizable and movable (like function selector)
        header = self.image_table.horizontalHeader()
        header.setSectionsMovable(True)  # Allow column reordering
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.Interactive)  # Filename - resizable

        # Apply styling
        self.image_table.setStyleSheet(self.style_gen.generate_table_widget_style())

        # Connect double-click to view in Napari
        self.image_table.cellDoubleClicked.connect(self.on_image_double_clicked)

        layout.addWidget(self.image_table)
        return table_container

    def _create_right_panel(self):
        """Create the right panel with config and instance manager."""
        container = QWidget()
        layout = QVBoxLayout(container)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(5)

        # Napari config panel
        config_panel = self._create_napari_config_panel()
        layout.addWidget(config_panel, 3)  # 60% of space

        # Instance manager panel
        instance_panel = self._create_instance_manager_panel()
        layout.addWidget(instance_panel, 2)  # 40% of space

        return container

    def _create_napari_config_panel(self):
        """Create the Napari configuration panel with lazy config widget."""
        panel = QGroupBox("Napari Display Settings")
        layout = QVBoxLayout(panel)
        layout.setContentsMargins(5, 5, 5, 5)

        # Create lazy Napari config instance
        from openhcs.core.config import LazyNapariStreamingConfig
        self.lazy_napari_config = LazyNapariStreamingConfig()

        # Create parameter form for the lazy config
        # Use pipeline_config as context for placeholder resolution
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

        # Set up context for placeholder resolution
        if self.orchestrator:
            context_obj = self.orchestrator.pipeline_config
        else:
            context_obj = None

        self.napari_config_form = ParameterFormManager(
            object_instance=self.lazy_napari_config,
            field_id="napari_config",
            parent=panel,
            context_obj=context_obj
        )

        # Wrap in scroll area for long forms
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setWidget(self.napari_config_form)
        layout.addWidget(scroll)

        return panel

    def _create_instance_manager_panel(self):
        """Create the Napari instance manager panel."""
        panel = QGroupBox("Napari Instances")
        layout = QVBoxLayout(panel)
        layout.setContentsMargins(5, 5, 5, 5)

        # Instance list
        self.instance_list = QListWidget()
        self.instance_list.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        layout.addWidget(self.instance_list)

        # Buttons
        button_layout = QHBoxLayout()

        refresh_instances_btn = QPushButton("Refresh")
        refresh_instances_btn.clicked.connect(self.refresh_napari_instances)
        refresh_instances_btn.setStyleSheet(self.style_gen.generate_button_style())
        button_layout.addWidget(refresh_instances_btn)

        quit_instances_btn = QPushButton("Quit Selected")
        quit_instances_btn.clicked.connect(self.quit_selected_instances)
        quit_instances_btn.setStyleSheet(self.style_gen.generate_button_style())
        button_layout.addWidget(quit_instances_btn)

        force_kill_instances_btn = QPushButton("Force Kill Selected")
        force_kill_instances_btn.clicked.connect(self.force_kill_selected_instances)
        force_kill_instances_btn.setStyleSheet(self.style_gen.generate_button_style())
        button_layout.addWidget(force_kill_instances_btn)

        layout.addLayout(button_layout)

        return panel

    def set_orchestrator(self, orchestrator):
        """Set the orchestrator and load images."""
        self.orchestrator = orchestrator

        # Update napari config form context to use new pipeline_config
        if self.napari_config_form and orchestrator:
            self.napari_config_form.context_obj = orchestrator.pipeline_config
            # Refresh placeholders with new context (uses private method)
            self.napari_config_form._refresh_all_placeholders()

        self.load_images()

    def _restore_folder_selection(self, folder_path: str, folder_items: Dict):
        """Restore folder selection after tree rebuild."""
        if folder_path in folder_items:
            item = folder_items[folder_path]
            item.setSelected(True)
            # Expand parents to make selection visible
            parent = item.parent()
            while parent:
                parent.setExpanded(True)
                parent = parent.parent()

    def on_folder_selection_changed(self):
        """Handle folder tree selection changes to filter table."""
        # Apply folder filter on top of search filter
        self._apply_combined_filters()

    def _apply_combined_filters(self):
        """Apply both search and folder filters together."""
        # Start with search-filtered images
        result = self.filtered_images.copy()

        # Apply folder filter if a folder is selected
        selected_items = self.folder_tree.selectedItems()
        if selected_items:
            folder_path = selected_items[0].data(0, Qt.ItemDataRole.UserRole)
            if folder_path:  # Not root
                # Filter by folder
                result = {
                    filename: metadata for filename, metadata in result.items()
                    if str(Path(filename).parent) == folder_path or filename.startswith(folder_path + "/")
                }

        # Update table with combined filters
        self._populate_table(result)
        logger.debug(f"Combined filters: {len(result)} images shown")

    def filter_images(self, search_term: str):
        """Filter images using shared search service (canonical code path)."""
        from openhcs.ui.shared.search_service import SearchService

        # Create searchable text extractor
        def create_searchable_text(metadata):
            """Create searchable text from image metadata."""
            searchable_fields = [metadata.get('filename', '')]
            # Add all metadata values
            for key, value in metadata.items():
                if key != 'filename' and value is not None:
                    searchable_fields.append(str(value))
            return " ".join(str(field) for field in searchable_fields)

        # Create search service if not exists
        if not hasattr(self, '_search_service'):
            self._search_service = SearchService(
                all_items=self.all_images,
                searchable_text_extractor=create_searchable_text
            )

        # Update search service with current images
        self._search_service.update_items(self.all_images)

        # Perform search using shared service
        self.filtered_images = self._search_service.filter(search_term)

        # Apply combined filters (search + folder selection)
        self._apply_combined_filters()

        # Update count label
        if len(search_term.strip()) >= SearchService.MIN_SEARCH_CHARS:
            self.image_count_label.setText(f"Images: {len(self.filtered_images)}/{len(self.all_images)} (filtered)")
        else:
            self.image_count_label.setText(f"Images: {len(self.all_images)}")

    def refresh_napari_instances(self):
        """Refresh the list of Napari instances with status and queue info."""
        # First, immediately show tracked viewers (synchronous)
        tracked_ports = set(self.napari_viewers.keys())
        self._update_instance_list(tracked_ports)

        # Then start async scan for external viewers in background
        import threading

        def scan_and_update():
            # Scan for all Napari viewers on common ports (including external ones)
            from openhcs.constants.constants import DEFAULT_NAPARI_STREAM_PORT
            common_ports = [DEFAULT_NAPARI_STREAM_PORT + i for i in range(10)]  # Scan ports 5555-5564

            detected_ports = set()

            # First, add ALL tracked viewers (even if not running yet - to show "Starting...")
            for port in self.napari_viewers.keys():
                detected_ports.add(port)

            # Then, scan for external viewers by pinging them in parallel
            external_ports = self._scan_ports_parallel([p for p in common_ports if p not in detected_ports])
            detected_ports.update(external_ports)

            # Update UI on main thread via signal
            self._instance_scan_complete.emit(detected_ports)

        # Start scan in background
        thread = threading.Thread(target=scan_and_update, daemon=True)
        thread.start()

    def _scan_ports_parallel(self, ports: list) -> set:
        """Scan multiple ports in parallel using thread pool."""
        import concurrent.futures

        detected = set()

        # Use ThreadPoolExecutor to ping all ports in parallel
        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
            # Submit all ping tasks
            future_to_port = {executor.submit(self._ping_napari_viewer, port): port for port in ports}

            # Collect results as they complete
            for future in concurrent.futures.as_completed(future_to_port):
                port = future_to_port[future]
                try:
                    if future.result():
                        detected.add(port)
                except Exception as e:
                    logger.debug(f"Error scanning port {port}: {e}")

        return detected

    @pyqtSlot(object)
    def _update_instance_list(self, detected_ports: set):
        """Update instance list on UI thread (called via QMetaObject.invokeMethod)."""
        self.instance_list.clear()

        # Display all detected viewers with status
        for port in sorted(detected_ports):
            viewer = self.napari_viewers.get(port)
            queue_count = len([1 for f, d, c, p in self.pending_napari_queue if p == port])

            # Determine status
            if viewer is not None:
                # Tracked viewer - show detailed status
                if not viewer.is_running:
                    if queue_count > 0:
                        status = f"🚀 Starting ({queue_count} queued)"
                    else:
                        status = "🚀 Starting..."
                elif queue_count > 0:
                    status = f"⏳ {queue_count} queued"
                else:
                    status = "✅ Ready"
            else:
                # External viewer - just show ready
                status = "✅ Ready"

            item = QListWidgetItem(f"Port {port} - {status}")
            item.setData(Qt.ItemDataRole.UserRole, port)
            self.instance_list.addItem(item)

        # Don't clean up tracked viewers - keep them even if not running yet
        # This allows us to show "Starting..." status
        logger.debug(f"Found {len(detected_ports)} Napari instances")

    def _ping_napari_viewer(self, port: int) -> bool:
        """
        Ping a Napari viewer on the given port to check if it's responsive.

        Returns True if viewer responds to ping, False otherwise.
        """
        response = self._ping_napari_viewer_detailed(port)
        return response is not None and response.get('type') == 'pong' and response.get('ready')

    def _ping_napari_viewer_detailed(self, port: int) -> dict | None:
        """
        Ping a Napari viewer and return the full pong response.

        Returns the pong response dict if successful, None otherwise.
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
            control_socket.setsockopt(zmq.RCVTIMEO, 200)  # 200ms timeout (fast scan)
            control_socket.connect(f"tcp://localhost:{control_port}")

            # Send ping
            ping_message = {'type': 'ping'}
            control_socket.send(pickle.dumps(ping_message))

            # Wait for pong
            response = control_socket.recv()
            response_data = pickle.loads(response)

            return response_data

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

    def quit_selected_instances(self):
        """
        Gracefully quit selected Napari instances.

        Verifies viewer is actually Napari via ping/pong before killing.
        """
        selected_items = self.instance_list.selectedItems()
        if not selected_items:
            QMessageBox.warning(self, "No Selection", "Please select Napari instances to quit.")
            return

        for item in selected_items:
            port = item.data(Qt.ItemDataRole.UserRole)

            try:
                # Verify viewer is actually Napari by pinging
                pong_response = self._ping_napari_viewer_detailed(port)
                if not pong_response:
                    logger.warning(f"No responsive viewer found on port {port}")
                    QMessageBox.warning(self, "Not Responsive",
                                      f"No responsive viewer on port {port}. Use Force Kill if needed.")
                    continue

                # Verify it's actually a Napari viewer from OpenHCS
                if not (pong_response.get('viewer') == 'napari' and pong_response.get('openhcs')):
                    logger.warning(f"Viewer on port {port} is not an OpenHCS Napari viewer: {pong_response}")
                    QMessageBox.warning(self, "Not Napari",
                                      f"Viewer on port {port} is not an OpenHCS Napari viewer. Use Force Kill if needed.")
                    continue

                # Confirmed Napari viewer - safe to kill
                self._kill_viewer_on_port(port)
                logger.info(f"Quit Napari instance on port {port}")

            except Exception as e:
                logger.error(f"Failed to quit Napari instance on port {port}: {e}", exc_info=True)

        # Refresh the list
        self.refresh_napari_instances()

    def force_kill_selected_instances(self):
        """
        Force kill selected Napari instances without verification.

        Immediately kills any process listening on the port.
        Use with caution!
        """
        selected_items = self.instance_list.selectedItems()
        if not selected_items:
            QMessageBox.warning(self, "No Selection", "Please select Napari instances to force kill.")
            return

        # Confirm with user
        reply = QMessageBox.question(
            self,
            "Force Kill Confirmation",
            f"Force kill {len(selected_items)} viewer(s) without verification?\n\n"
            "This will immediately kill any process listening on the selected ports.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No
        )

        if reply != QMessageBox.StandardButton.Yes:
            return

        for item in selected_items:
            port = item.data(Qt.ItemDataRole.UserRole)

            try:
                self._kill_viewer_on_port(port)
                logger.info(f"Force killed viewer on port {port}")
            except Exception as e:
                logger.error(f"Failed to force kill viewer on port {port}: {e}", exc_info=True)

        # Refresh the list
        self.refresh_napari_instances()

    def _kill_viewer_on_port(self, port: int):
        """Kill viewer on specified port (internal helper)."""
        # If we have a tracked viewer, clean up ZMQ first
        if port in self.napari_viewers:
            viewer = self.napari_viewers[port]
            if hasattr(viewer, '_cleanup_zmq'):
                viewer._cleanup_zmq()
                logger.debug(f"Cleaned up ZMQ for port {port}")

            # Mark as not running
            viewer._is_running = False

            # Remove from tracking
            del self.napari_viewers[port]

        # Kill all processes on this port
        from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer
        temp_vis = NapariStreamVisualizer(
            filemanager=self.filemanager,
            visualizer_config=None,
            napari_port=port
        )
        logger.info(f"Killing processes on port {port}")
        temp_vis._kill_processes_on_port(port)
        # Also kill control port
        temp_vis._kill_processes_on_port(port + 1000)

    def load_images(self):
        """Load image files from the orchestrator's metadata."""
        if not self.orchestrator:
            self.info_label.setText("No plate loaded")
            return

        try:
            # Get metadata handler from orchestrator
            handler = self.orchestrator.microscope_handler
            metadata_handler = handler.metadata_handler

            # Get image files from metadata
            plate_path = self.orchestrator.plate_path
            image_files = metadata_handler.get_image_files(plate_path)

            if not image_files:
                self.info_label.setText("No images found")
                return

            # Parse first file to determine columns
            first_parsed = handler.parser.parse_filename(image_files[0])

            if first_parsed:
                # Get metadata keys (excluding 'extension')
                metadata_keys = [k for k in first_parsed.keys() if k != 'extension']

                # Set up table columns: Filename + metadata keys
                column_headers = ["Filename"] + [k.replace('_', ' ').title() for k in metadata_keys]
                self.image_table.setColumnCount(len(column_headers))
                self.image_table.setHorizontalHeaderLabels(column_headers)

                # Set all columns to Interactive resize mode (like function selector)
                header = self.image_table.horizontalHeader()
                for col in range(len(column_headers)):
                    header.setSectionResizeMode(col, QHeaderView.ResizeMode.Interactive)
            else:
                # Fallback if parsing fails
                self.image_table.setColumnCount(1)
                self.image_table.setHorizontalHeaderLabels(["Filename"])
                metadata_keys = []

            # Build all_images dictionary
            self.all_images = {}
            for filename in image_files:
                parsed = handler.parser.parse_filename(filename)
                metadata = {'filename': filename}
                if parsed:
                    metadata.update(parsed)
                self.all_images[filename] = metadata

            # Initialize filtered images to all images
            self.filtered_images = self.all_images.copy()

            # Build folder tree from file paths
            self._build_folder_tree()

            # Populate table
            self._populate_table(self.filtered_images)

            # Update count
            self.image_count_label.setText(f"Images: {len(self.all_images)}")
            self.info_label.setText(f"{len(self.all_images)} images loaded")

        except Exception as e:
            logger.error(f"Failed to load images: {e}")
            QMessageBox.warning(self, "Error", f"Failed to load images: {e}")
            self.info_label.setText("Error loading images")

    def _populate_table(self, images_dict: Dict[str, Dict]):
        """Populate table with images from dictionary."""
        # Clear table
        self.image_table.setRowCount(0)

        # Get metadata keys from first image
        if images_dict:
            first_metadata = next(iter(images_dict.values()))
            metadata_keys = [k for k in first_metadata.keys() if k != 'filename' and k != 'extension']
        else:
            metadata_keys = []

        # Populate rows
        for i, (filename, metadata) in enumerate(images_dict.items()):
            self.image_table.insertRow(i)

            # Filename column
            filename_item = QTableWidgetItem(filename)
            filename_item.setData(Qt.ItemDataRole.UserRole, filename)
            self.image_table.setItem(i, 0, filename_item)

            # Metadata columns
            for col_idx, key in enumerate(metadata_keys, start=1):
                value = metadata.get(key, 'N/A')
                display_value = str(value) if value is not None else 'N/A'
                self.image_table.setItem(i, col_idx, QTableWidgetItem(display_value))

    def _build_folder_tree(self):
        """Build folder tree from image file paths."""
        # Save current selection before rebuilding
        selected_folder = None
        selected_items = self.folder_tree.selectedItems()
        if selected_items:
            selected_folder = selected_items[0].data(0, Qt.ItemDataRole.UserRole)

        self.folder_tree.clear()

        # Extract unique folder paths
        folders: Set[str] = set()
        for filename in self.all_images.keys():
            path = Path(filename)
            # Add all parent directories
            for parent in path.parents:
                if str(parent) != '.':
                    folders.add(str(parent))

        # Build tree structure
        root_item = QTreeWidgetItem(["All Images"])
        root_item.setData(0, Qt.ItemDataRole.UserRole, None)
        self.folder_tree.addTopLevelItem(root_item)

        # Sort folders for consistent display
        sorted_folders = sorted(folders)

        # Create tree items for each folder
        folder_items = {}
        for folder in sorted_folders:
            parts = Path(folder).parts
            if len(parts) == 1:
                # Top-level folder
                item = QTreeWidgetItem([folder])
                item.setData(0, Qt.ItemDataRole.UserRole, folder)
                root_item.addChild(item)
                folder_items[folder] = item
            else:
                # Nested folder - find parent
                parent_path = str(Path(folder).parent)
                if parent_path in folder_items:
                    item = QTreeWidgetItem([Path(folder).name])
                    item.setData(0, Qt.ItemDataRole.UserRole, folder)
                    folder_items[parent_path].addChild(item)
                    folder_items[folder] = item

        # Start with everything collapsed (user can expand to explore)
        root_item.setExpanded(False)

        # Restore previous selection if it still exists
        if selected_folder is not None:
            self._restore_folder_selection(selected_folder, folder_items)
    
    def on_selection_changed(self):
        """Handle selection change in the table."""
        has_selection = len(self.image_table.selectedItems()) > 0
        self.view_napari_btn.setEnabled(has_selection)
    
    def on_image_double_clicked(self, row: int, column: int):
        """Handle double-click on an image row."""
        self.view_selected_in_napari()
    
    def view_selected_in_napari(self):
        """View all selected images in Napari."""
        selected_rows = self.image_table.selectionModel().selectedRows()
        if not selected_rows:
            return

        # Stream all selected images
        for row_index in selected_rows:
            row = row_index.row()
            filename_item = self.image_table.item(row, 0)
            filename = filename_item.data(Qt.ItemDataRole.UserRole)

            try:
                self._load_and_stream_to_napari(filename)
            except Exception as e:
                logger.error(f"Failed to view image {filename} in Napari: {e}")
                QMessageBox.warning(self, "Error", f"Failed to view image {filename} in Napari: {e}")
                break  # Stop on first error
    
    def _load_and_stream_to_napari(self, filename: str):
        """Load image into memory and stream to Napari using live config widget values."""
        if not self.orchestrator:
            raise RuntimeError("No orchestrator set")

        # Get the full path to the image
        # Filename is already a path relative to plate_path (from metadata_handler.get_image_files)
        plate_path = Path(self.orchestrator.plate_path)
        image_path = plate_path / filename

        # Load image using FileManager
        image_data = self.filemanager.load(str(image_path), Backend.DISK.value)

        # Resolve Napari config using compiler pattern:
        # 1. Get current widget values
        # 2. Create a temporary dataclass instance with those values
        # 3. Set up nested context: pipeline_config -> widget_instance
        # 4. Resolve to get final merged config
        from openhcs.config_framework.context_manager import config_context
        from openhcs.config_framework.lazy_factory import resolve_lazy_configurations_for_serialization
        from openhcs.core.config import LazyNapariStreamingConfig
        from dataclasses import replace

        # Get current widget values
        current_values = self.napari_config_form.get_current_values()

        # Create a temporary lazy config instance with current widget values
        # This preserves None for unmodified fields (for lazy resolution)
        temp_config = LazyNapariStreamingConfig(**{k: v for k, v in current_values.items() if v is not None})

        # Resolve with nested context (same as compiler does for steps)
        with config_context(self.orchestrator.pipeline_config):
            with config_context(temp_config):
                # Resolve the temp config to get final merged values
                napari_config = resolve_lazy_configurations_for_serialization(temp_config)

        # Get or create Napari viewer for this port
        napari_port = napari_config.napari_port
        viewer = self._get_or_create_napari_viewer(napari_port, napari_config)

        # Stream image to Napari
        self._stream_image_to_viewer(viewer, image_data, filename, napari_config)

        logger.info(f"Streamed {filename} to Napari viewer on port {napari_port}")
    
    def _get_or_create_napari_viewer(self, port: int, config):
        """Get existing Napari viewer or create a new one, reconnecting if needed."""
        from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer

        # Check if we have a viewer for this port
        if port in self.napari_viewers:
            viewer = self.napari_viewers[port]
            # Check if viewer is still running
            if viewer.is_running:
                return viewer
            else:
                # Viewer was closed, remove it and create a new one
                logger.info(f"Napari viewer on port {port} was closed, creating new instance")
                del self.napari_viewers[port]

        # Create new viewer instance
        # Note: If a viewer already exists on this port (e.g., from pipeline execution),
        # start_viewer() will detect it and connect to it instead of killing it
        viewer = NapariStreamVisualizer(
            filemanager=self.filemanager,
            visualizer_config=config,
            viewer_title=f"OpenHCS Image Browser - Port {port}",
            persistent=True,
            napari_port=port,
            display_config=config
        )
        # Start viewer asynchronously (non-blocking)
        # This will reuse existing viewer if one is already running on this port
        viewer.start_viewer(async_mode=True)
        self.napari_viewers[port] = viewer

        logger.info(f"Napari viewer starting asynchronously on port {port}")

        # Refresh instance list to show starting status
        self.refresh_napari_instances()

        # Schedule refresh and queue processing after viewer is ready
        self._schedule_post_viewer_startup(viewer, port)

        return viewer

    def _schedule_post_viewer_startup(self, viewer, port: int):
        """Schedule refresh and queue processing after viewer startup."""
        import threading

        def wait_and_process():
            import time
            # Wait for viewer to be ready
            max_wait = 15
            start_time = time.time()

            while not viewer.is_running and (time.time() - start_time) < max_wait:
                time.sleep(0.5)

            if viewer.is_running:
                # Refresh instance list on UI thread
                from PyQt6.QtCore import QMetaObject, Qt as QtCore, Q_ARG
                QMetaObject.invokeMethod(
                    self,
                    "_on_viewer_ready",
                    QtCore.ConnectionType.QueuedConnection,
                    Q_ARG(int, port)
                )
            else:
                logger.error(f"Napari viewer on port {port} failed to start within {max_wait} seconds")

        thread = threading.Thread(target=wait_and_process, daemon=True)
        thread.start()

    @pyqtSlot(int)
    def _on_viewer_ready(self, port: int):
        """Called when a new viewer is ready - refresh list and process queue."""
        logger.info(f"✅ Napari viewer on port {port} is ready")

        # Refresh instance list to show viewer is ready
        self.refresh_napari_instances()

        # Process any queued images for this port
        self._process_pending_queue(port)

        # Refresh again after processing to clear queue count
        self.refresh_napari_instances()

    def _process_pending_queue(self, port: int):
        """Process all queued images for the specified port."""
        if not self.pending_napari_queue:
            return

        # Get viewer for this port
        if port not in self.napari_viewers:
            logger.warning(f"No viewer found for port {port}, cannot process queue")
            return

        viewer = self.napari_viewers[port]

        # Verify viewer is actually running before processing queue
        if not viewer.is_running:
            logger.warning(f"Viewer on port {port} is not running yet, keeping queue")
            return

        # Filter queue for this port
        port_queue = [(f, d, c) for f, d, c, p in self.pending_napari_queue if p == port]

        # Remove processed items from queue
        self.pending_napari_queue = [(f, d, c, p) for f, d, c, p in self.pending_napari_queue if p != port]

        # Stream all queued images (skip is_running check since we already verified)
        logger.info(f"Processing {len(port_queue)} queued images for port {port}")
        for filename, image_data, config in port_queue:
            self._stream_image_to_viewer(viewer, image_data, filename, config, skip_running_check=True)
    
    def _stream_image_to_viewer(self, viewer, image_data, filename: str, config, skip_running_check=False):
        """Stream image data to Napari viewer asynchronously."""
        # If viewer isn't ready yet, queue the image (unless we're processing the queue)
        if not skip_running_check and not viewer.is_running:
            logger.info(f"Viewer not ready, queuing {filename} for port {viewer.napari_port}")
            self.pending_napari_queue.append((filename, image_data, config, viewer.napari_port))

            # Refresh instance list to show updated queue count
            self.refresh_napari_instances()
            return

        # Stream in background thread to avoid blocking UI
        import threading

        def stream_async():
            try:
                # Viewer is already running, stream immediately

                # Use the napari streaming backend to send the image
                from openhcs.constants.constants import Backend as BackendEnum

                # Prepare metadata for streaming
                metadata = {
                    'napari_port': viewer.napari_port,
                    'display_config': config,
                    'microscope_handler': self.orchestrator.microscope_handler,
                    'step_index': 0,
                    'step_name': 'image_browser'
                }

                # Stream to Napari
                self.filemanager.save_batch(
                    [image_data],
                    [filename],
                    BackendEnum.NAPARI_STREAM.value,
                    **metadata
                )
                logger.info(f"Successfully streamed {filename} to Napari on port {viewer.napari_port}")
            except Exception as e:
                logger.error(f"Failed to stream image to Napari: {e}")
                # Show error in UI thread
                from PyQt6.QtCore import QMetaObject, Qt
                QMetaObject.invokeMethod(
                    self, "_show_streaming_error",
                    Qt.ConnectionType.QueuedConnection,
                    str(e)
                )

        # Start streaming in background thread
        thread = threading.Thread(target=stream_async, daemon=True)
        thread.start()
        logger.info(f"Streaming {filename} to Napari asynchronously...")

    @pyqtSlot(str)
    def _show_streaming_error(self, error_msg: str):
        """Show streaming error in UI thread (called via QMetaObject.invokeMethod)."""
        QMessageBox.warning(self, "Streaming Error", f"Failed to stream image to Napari: {error_msg}")
    
    def cleanup(self):
        """Clean up Napari viewers."""
        for viewer in self.napari_viewers.values():
            try:
                viewer.stop_viewer()
            except:
                pass
        self.napari_viewers.clear()

