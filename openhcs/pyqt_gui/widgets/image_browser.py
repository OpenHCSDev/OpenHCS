"""
Image Browser Widget for PyQt6 GUI.

Displays a table of all image files from plate metadata and allows users to
view them in Napari with configurable display settings.
"""

import logging
from pathlib import Path
from typing import Optional, List, Dict, Set

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QTableWidget, QTableWidgetItem,
    QPushButton, QLabel, QHeaderView, QAbstractItemView, QMessageBox,
    QSplitter, QGroupBox, QTreeWidget, QTreeWidgetItem, QScrollArea,
    QLineEdit
)
from PyQt6.QtCore import Qt, pyqtSignal, pyqtSlot

from openhcs.constants.constants import Backend
from openhcs.io.filemanager import FileManager
from openhcs.io.base import storage_registry
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.widgets.shared.column_filter_widget import MultiColumnFilterPanel

logger = logging.getLogger(__name__)


class ImageBrowserWidget(QWidget):
    """
    Image browser widget that displays all image files from plate metadata.
    
    Users can click on files to view them in Napari with configurable settings
    from the current PipelineConfig.
    """
    
    # Signals
    image_selected = pyqtSignal(str)  # Emitted when an image is selected

    def __init__(self, orchestrator=None, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        super().__init__(parent)

        self.orchestrator = orchestrator
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.style_gen = StyleSheetGenerator(self.color_scheme)
        self.filemanager = FileManager(storage_registry)

        # Lazy config widgets (will be created in init_ui)
        self.napari_config_form = None
        self.lazy_napari_config = None
        self.fiji_config_form = None
        self.lazy_fiji_config = None

        # Image data tracking
        self.all_images = {}  # filename -> metadata dict
        self.filtered_images = {}  # filename -> metadata dict (after search/filter)
        self.selected_wells = set()  # Selected wells for filtering
        self.metadata_keys = []  # Column names from parser metadata

        # Plate view widget (will be created in init_ui)
        self.plate_view_widget = None
        self.plate_view_detached_window = None
        self.middle_splitter = None  # Reference to splitter for reattaching

        # Column filter panel
        self.column_filter_panel = None

        # Start global ack listener for image acknowledgment tracking
        from openhcs.runtime.zmq_base import start_global_ack_listener
        start_global_ack_listener()

        self.init_ui()

        # Load images if orchestrator is provided
        if self.orchestrator:
            self.load_images()

    def init_ui(self):
        """Initialize the user interface."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(10)



        # Search input row
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

        # Create main splitter (tree+filters | table | config)
        main_splitter = QSplitter(Qt.Orientation.Horizontal)

        # Left panel: Vertical splitter for Folder tree + Column filters
        left_splitter = QSplitter(Qt.Orientation.Vertical)

        # Folder tree
        tree_widget = self._create_folder_tree()
        left_splitter.addWidget(tree_widget)

        # Column filter panel (initially empty, populated when images load)
        self.column_filter_panel = MultiColumnFilterPanel()
        self.column_filter_panel.filters_changed.connect(self._on_column_filters_changed)

        # Wrap in scroll area for vertical scrolling when many filters
        filter_scroll = QScrollArea()
        filter_scroll.setWidgetResizable(True)
        filter_scroll.setWidget(self.column_filter_panel)
        filter_scroll.setVisible(False)  # Hidden until images load
        self.filter_scroll_area = filter_scroll
        left_splitter.addWidget(filter_scroll)

        # Set initial sizes: tree gets more space (60% tree, 40% filters)
        left_splitter.setSizes([300, 200])

        main_splitter.addWidget(left_splitter)

        # Middle: Vertical splitter for plate view and table
        self.middle_splitter = QSplitter(Qt.Orientation.Vertical)

        # Plate view (initially hidden)
        from openhcs.pyqt_gui.widgets.shared.plate_view_widget import PlateViewWidget
        self.plate_view_widget = PlateViewWidget(color_scheme=self.color_scheme, parent=self)
        self.plate_view_widget.wells_selected.connect(self._on_wells_selected)
        self.plate_view_widget.detach_requested.connect(self._detach_plate_view)
        self.plate_view_widget.setVisible(False)
        self.middle_splitter.addWidget(self.plate_view_widget)

        # Image table
        table_widget = self._create_table_widget()
        self.middle_splitter.addWidget(table_widget)

        # Set initial sizes (30% plate view, 70% table when visible)
        self.middle_splitter.setSizes([150, 350])

        main_splitter.addWidget(self.middle_splitter)

        # Right: Napari config panel + instance manager
        right_panel = self._create_right_panel()
        main_splitter.addWidget(right_panel)

        # Set initial splitter sizes (20% tree, 50% middle, 30% config)
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

        self.view_fiji_btn = QPushButton("View in Fiji")
        self.view_fiji_btn.clicked.connect(self.view_selected_in_fiji)
        self.view_fiji_btn.setStyleSheet(self.style_gen.generate_button_style())
        self.view_fiji_btn.setEnabled(False)
        button_layout.addWidget(self.view_fiji_btn)

        button_layout.addStretch()

        # Plate view toggle button (moved from header for compact layout)
        self.plate_view_toggle_btn = QPushButton("Show Plate View")
        self.plate_view_toggle_btn.setCheckable(True)
        self.plate_view_toggle_btn.clicked.connect(self._toggle_plate_view)
        self.plate_view_toggle_btn.setStyleSheet(self.style_gen.generate_button_style())
        button_layout.addWidget(self.plate_view_toggle_btn)

        # Refresh button (moved from header for compact layout)
        self.refresh_btn = QPushButton("Refresh")
        self.refresh_btn.clicked.connect(self.load_images)
        self.refresh_btn.setStyleSheet(self.style_gen.generate_button_style())
        button_layout.addWidget(self.refresh_btn)

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

        # Connect double-click to view in enabled viewer(s)
        self.image_table.cellDoubleClicked.connect(self.on_image_double_clicked)

        layout.addWidget(self.image_table)
        return table_container

    def _create_right_panel(self):
        """Create the right panel with config tabs and instance manager."""
        container = QWidget()
        layout = QVBoxLayout(container)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        # Vertical splitter for configs and instance manager
        vertical_splitter = QSplitter(Qt.Orientation.Vertical)

        # Tab widget for streaming configs
        from PyQt6.QtWidgets import QTabWidget
        self.streaming_tabs = QTabWidget()
        self.streaming_tabs.setStyleSheet(self.style_gen.generate_tab_widget_style())

        # Napari config panel (with enable checkbox)
        napari_panel = self._create_napari_config_panel()
        self.napari_tab_index = self.streaming_tabs.addTab(napari_panel, "Napari")

        # Fiji config panel (with enable checkbox)
        fiji_panel = self._create_fiji_config_panel()
        self.fiji_tab_index = self.streaming_tabs.addTab(fiji_panel, "Fiji")

        # Update tab text when configs are enabled/disabled
        self._update_tab_labels()

        vertical_splitter.addWidget(self.streaming_tabs)

        # Instance manager panel
        instance_panel = self._create_instance_manager_panel()
        vertical_splitter.addWidget(instance_panel)

        # Set initial sizes (30% configs, 70% instance manager)
        vertical_splitter.setSizes([150, 350])

        layout.addWidget(vertical_splitter)

        return container

    def _create_napari_config_panel(self):
        """Create the Napari configuration panel with enable checkbox and lazy config widget."""
        from PyQt6.QtWidgets import QCheckBox

        panel = QGroupBox()
        layout = QVBoxLayout(panel)
        layout.setContentsMargins(5, 5, 5, 5)
        layout.setSpacing(5)

        # Enable checkbox in header
        self.napari_enable_checkbox = QCheckBox("Enable Napari Streaming")
        self.napari_enable_checkbox.setChecked(True)  # Enabled by default
        self.napari_enable_checkbox.toggled.connect(self._on_napari_enable_toggled)
        layout.addWidget(self.napari_enable_checkbox)

        # Create lazy Napari config instance
        from openhcs.core.config import LazyNapariStreamingConfig
        self.lazy_napari_config = LazyNapariStreamingConfig()

        # Create parameter form for the lazy config
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

    def _create_fiji_config_panel(self):
        """Create the Fiji configuration panel with enable checkbox and lazy config widget."""
        from PyQt6.QtWidgets import QCheckBox

        panel = QGroupBox()
        layout = QVBoxLayout(panel)
        layout.setContentsMargins(5, 5, 5, 5)
        layout.setSpacing(5)

        # Enable checkbox in header
        self.fiji_enable_checkbox = QCheckBox("Enable Fiji Streaming")
        self.fiji_enable_checkbox.setChecked(False)  # Disabled by default
        self.fiji_enable_checkbox.toggled.connect(self._on_fiji_enable_toggled)
        layout.addWidget(self.fiji_enable_checkbox)

        # Create lazy Fiji config instance
        from openhcs.config_framework.lazy_factory import LazyFijiStreamingConfig
        self.lazy_fiji_config = LazyFijiStreamingConfig()

        # Create parameter form for the lazy config
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

        # Set up context for placeholder resolution
        if self.orchestrator:
            context_obj = self.orchestrator.pipeline_config
        else:
            context_obj = None

        self.fiji_config_form = ParameterFormManager(
            object_instance=self.lazy_fiji_config,
            field_id="fiji_config",
            parent=panel,
            context_obj=context_obj
        )

        # Wrap in scroll area for long forms
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setWidget(self.fiji_config_form)
        layout.addWidget(scroll)

        # Initially disable the form (checkbox is unchecked by default)
        self.fiji_config_form.setEnabled(False)

        return panel

    def _update_tab_labels(self):
        """Update tab labels to show enabled/disabled status."""
        napari_enabled = self.napari_enable_checkbox.isChecked()
        fiji_enabled = self.fiji_enable_checkbox.isChecked()

        napari_label = "Napari ✓" if napari_enabled else "Napari"
        fiji_label = "Fiji ✓" if fiji_enabled else "Fiji"

        self.streaming_tabs.setTabText(self.napari_tab_index, napari_label)
        self.streaming_tabs.setTabText(self.fiji_tab_index, fiji_label)

    def _on_napari_enable_toggled(self, checked: bool):
        """Handle Napari enable checkbox toggle."""
        self.napari_config_form.setEnabled(checked)
        self.view_napari_btn.setEnabled(checked and len(self.image_table.selectedItems()) > 0)
        self._update_tab_labels()

    def _on_fiji_enable_toggled(self, checked: bool):
        """Handle Fiji enable checkbox toggle."""
        self.fiji_config_form.setEnabled(checked)
        self.view_fiji_btn.setEnabled(checked and len(self.image_table.selectedItems()) > 0)
        self._update_tab_labels()

    def _create_instance_manager_panel(self):
        """Create the viewer instance manager panel using ZMQServerManagerWidget."""
        from openhcs.pyqt_gui.widgets.shared.zmq_server_manager import ZMQServerManagerWidget
        from openhcs.constants.constants import DEFAULT_NAPARI_STREAM_PORT

        # Scan Napari and Fiji ports
        # Napari: 5555-5564 (10 ports)
        # Fiji: 5565-5574 (10 ports, non-overlapping with Napari)
        napari_ports = [DEFAULT_NAPARI_STREAM_PORT + i for i in range(10)]  # 5555-5564
        fiji_ports = [5565 + i for i in range(10)]  # 5565-5574 (avoid overlap with Napari)
        ports_to_scan = napari_ports + fiji_ports

        # Create ZMQ server manager widget
        zmq_manager = ZMQServerManagerWidget(
            ports_to_scan=ports_to_scan,
            title="Viewer Instances",
            style_generator=self.style_gen,
            parent=self
        )

        return zmq_manager

    def set_orchestrator(self, orchestrator):
        """Set the orchestrator and load images."""
        self.orchestrator = orchestrator

        # Update config form contexts to use new pipeline_config
        if self.napari_config_form and orchestrator:
            self.napari_config_form.context_obj = orchestrator.pipeline_config
            # Refresh placeholders with new context (uses private method)
            self.napari_config_form._refresh_all_placeholders()

        if self.fiji_config_form and orchestrator:
            self.fiji_config_form.context_obj = orchestrator.pipeline_config
            self.fiji_config_form._refresh_all_placeholders()

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

        # Update plate view for new folder
        if self.plate_view_widget and self.plate_view_widget.isVisible():
            self._update_plate_view()

    def _apply_combined_filters(self):
        """Apply search, folder, well, and column filters together."""
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

        # Apply well filter if wells are selected
        if self.selected_wells:
            result = {
                filename: metadata for filename, metadata in result.items()
                if self._matches_wells(filename, metadata)
            }

        # Apply column filters
        if self.column_filter_panel:
            active_filters = self.column_filter_panel.get_active_filters()
            if active_filters:
                # Filter with AND logic across columns
                filtered_result = {}
                for filename, metadata in result.items():
                    matches = True
                    for column_name, selected_values in active_filters.items():
                        # Get the metadata key (lowercase with underscores)
                        metadata_key = column_name.lower().replace(' ', '_')
                        item_value = str(metadata.get(metadata_key, ''))
                        if item_value not in selected_values:
                            matches = False
                            break
                    if matches:
                        filtered_result[filename] = metadata
                result = filtered_result

        # Update table with combined filters
        self._populate_table(result)
        logger.debug(f"Combined filters: {len(result)} images shown")

    def _build_column_filters(self):
        """Build column filter widgets from loaded image metadata."""
        if not self.all_images or not self.metadata_keys:
            return

        # Clear existing filters
        self.column_filter_panel.clear_all_filters()

        # Extract unique values for each metadata column
        for metadata_key in self.metadata_keys:
            unique_values = set()
            for metadata in self.all_images.values():
                value = metadata.get(metadata_key)
                if value is not None:
                    unique_values.add(str(value))

            if unique_values:
                # Create filter for this column
                column_display_name = metadata_key.replace('_', ' ').title()
                self.column_filter_panel.add_column_filter(column_display_name, sorted(list(unique_values)))

        # Show filter panel if we have filters
        if self.column_filter_panel.column_filters:
            self.filter_scroll_area.setVisible(True)

        logger.debug(f"Built {len(self.column_filter_panel.column_filters)} column filters")

    def _on_column_filters_changed(self):
        """Handle column filter changes."""
        self._apply_combined_filters()

        # Update plate view if visible
        if self.plate_view_widget and self.plate_view_widget.isVisible():
            self._update_plate_view()

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

        # Apply combined filters (search + folder + column filters)
        self._apply_combined_filters()

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
                self.metadata_keys = [k for k in first_parsed.keys() if k != 'extension']

                # Set up table columns: Filename + metadata keys
                column_headers = ["Filename"] + [k.replace('_', ' ').title() for k in self.metadata_keys]
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
                self.metadata_keys = []

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

            # Build column filters from metadata
            self._build_column_filters()

            # Populate table
            self._populate_table(self.filtered_images)

            # Update info label
            self.info_label.setText(f"{len(self.all_images)} images loaded")

            # Update plate view if visible
            if self.plate_view_widget and self.plate_view_widget.isVisible():
                self._update_plate_view()

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
        # Enable buttons based on selection AND checkbox state
        self.view_napari_btn.setEnabled(has_selection and self.napari_enable_checkbox.isChecked())
        self.view_fiji_btn.setEnabled(has_selection and self.fiji_enable_checkbox.isChecked())
    
    def on_image_double_clicked(self, row: int, column: int):
        """Handle double-click on an image row - stream to enabled viewer(s)."""
        napari_enabled = self.napari_enable_checkbox.isChecked()
        fiji_enabled = self.fiji_enable_checkbox.isChecked()

        # Stream to whichever viewer(s) are enabled
        if napari_enabled and fiji_enabled:
            # Both enabled - stream to both
            self.view_selected_in_napari()
            self.view_selected_in_fiji()
        elif napari_enabled:
            # Only Napari enabled
            self.view_selected_in_napari()
        elif fiji_enabled:
            # Only Fiji enabled
            self.view_selected_in_fiji()
        else:
            # Neither enabled - show message
            QMessageBox.information(
                self,
                "No Viewer Enabled",
                "Please enable Napari or Fiji streaming to view images."
            )
    
    def view_selected_in_napari(self):
        """View all selected images in Napari as a batch (builds hyperstack)."""
        selected_rows = self.image_table.selectionModel().selectedRows()
        if not selected_rows:
            return

        # Collect all filenames
        filenames = []
        for row_index in selected_rows:
            row = row_index.row()
            filename_item = self.image_table.item(row, 0)
            filename = filename_item.data(Qt.ItemDataRole.UserRole)
            filenames.append(filename)

        try:
            # Stream all images as a batch
            self._load_and_stream_batch_to_napari(filenames)
        except Exception as e:
            logger.error(f"Failed to view images in Napari: {e}")
            QMessageBox.warning(self, "Error", f"Failed to view images in Napari: {e}")

    def view_selected_in_fiji(self):
        """View all selected images in Fiji as a batch (builds hyperstack)."""
        selected_rows = self.image_table.selectionModel().selectedRows()
        if not selected_rows:
            return

        # Collect all filenames
        filenames = []
        for row_index in selected_rows:
            row = row_index.row()
            filename_item = self.image_table.item(row, 0)
            filename = filename_item.data(Qt.ItemDataRole.UserRole)
            filenames.append(filename)

        try:
            # Stream all images as a batch
            self._load_and_stream_batch_to_fiji(filenames)
        except Exception as e:
            logger.error(f"Failed to view images in Fiji: {e}")
            QMessageBox.warning(self, "Error", f"Failed to view images in Fiji: {e}")
    
    def _load_and_stream_batch_to_napari(self, filenames: list):
        """Load multiple images and stream as batch to Napari (builds hyperstack)."""
        if not self.orchestrator:
            raise RuntimeError("No orchestrator set")

        # Get plate path
        plate_path = Path(self.orchestrator.plate_path)

        # Resolve backend (lightweight operation, safe in UI thread)
        from openhcs.config_framework.global_config import get_current_global_config
        from openhcs.core.config import GlobalPipelineConfig
        global_config = get_current_global_config(GlobalPipelineConfig)

        if global_config.vfs_config.read_backend != Backend.AUTO:
            read_backend = global_config.vfs_config.read_backend.value
        else:
            read_backend = self.orchestrator.microscope_handler.get_primary_backend(plate_path)

        # Resolve Napari config (lightweight operation, safe in UI thread)
        from openhcs.config_framework.context_manager import config_context
        from openhcs.config_framework.lazy_factory import resolve_lazy_configurations_for_serialization, LazyNapariStreamingConfig

        current_values = self.napari_config_form.get_current_values()
        temp_config = LazyNapariStreamingConfig(**{k: v for k, v in current_values.items() if v is not None})

        with config_context(self.orchestrator.pipeline_config):
            with config_context(temp_config):
                napari_config = resolve_lazy_configurations_for_serialization(temp_config)

        # Get or create viewer (lightweight operation, safe in UI thread)
        viewer = self.orchestrator.get_or_create_visualizer(napari_config)

        # Load and stream in background thread (HEAVY OPERATION - must not block UI)
        self._load_and_stream_batch_to_napari_async(
            viewer, filenames, plate_path, read_backend, napari_config
        )

        logger.info(f"Loading and streaming batch of {len(filenames)} images to Napari viewer on port {napari_config.napari_port}...")

    def _load_and_stream_batch_to_fiji(self, filenames: list):
        """Load multiple images and stream as batch to Fiji (builds hyperstack)."""
        if not self.orchestrator:
            raise RuntimeError("No orchestrator set")

        # Get plate path
        plate_path = Path(self.orchestrator.plate_path)

        # Resolve backend (lightweight operation, safe in UI thread)
        from openhcs.config_framework.global_config import get_current_global_config
        from openhcs.core.config import GlobalPipelineConfig
        global_config = get_current_global_config(GlobalPipelineConfig)

        if global_config.vfs_config.read_backend != Backend.AUTO:
            read_backend = global_config.vfs_config.read_backend.value
        else:
            read_backend = self.orchestrator.microscope_handler.get_primary_backend(plate_path)

        # Resolve Fiji config (lightweight operation, safe in UI thread)
        from openhcs.config_framework.context_manager import config_context
        from openhcs.config_framework.lazy_factory import resolve_lazy_configurations_for_serialization, LazyFijiStreamingConfig

        current_values = self.fiji_config_form.get_current_values()
        temp_config = LazyFijiStreamingConfig(**{k: v for k, v in current_values.items() if v is not None})

        with config_context(self.orchestrator.pipeline_config):
            with config_context(temp_config):
                fiji_config = resolve_lazy_configurations_for_serialization(temp_config)

        # Get or create viewer (lightweight operation, safe in UI thread)
        viewer = self.orchestrator.get_or_create_visualizer(fiji_config)

        # Load and stream in background thread (HEAVY OPERATION - must not block UI)
        self._load_and_stream_batch_to_fiji_async(
            viewer, filenames, plate_path, read_backend, fiji_config
        )

        logger.info(f"Loading and streaming batch of {len(filenames)} images to Fiji viewer on port {fiji_config.fiji_port}...")

    def _load_and_stream_batch_to_napari_async(self, viewer, filenames: list, plate_path: Path,
                                                 read_backend: str, config):
        """Load and stream batch of images to Napari in background thread (NEVER blocks UI)."""
        import threading

        def load_and_stream():
            try:
                # HEAVY OPERATION: Load all images (runs in background thread)
                image_data_list = []
                file_paths = []
                for filename in filenames:
                    image_path = plate_path / filename
                    image_data = self.filemanager.load(str(image_path), read_backend)
                    image_data_list.append(image_data)
                    file_paths.append(filename)

                logger.info(f"Loaded {len(image_data_list)} images in background thread")

                # Register that we're launching a viewer
                from openhcs.pyqt_gui.widgets.shared.zmq_server_manager import (
                    register_launching_viewer, unregister_launching_viewer
                )

                # Check if viewer is already ready (quick ping with short timeout)
                is_already_running = viewer.wait_for_ready(timeout=0.1)

                if not is_already_running:
                    # Viewer is launching - register it and show in UI
                    register_launching_viewer(viewer.napari_port, 'napari', len(file_paths))
                    logger.info(f"Waiting for Napari viewer on port {viewer.napari_port} to be ready...")

                    # Wait for viewer to be ready before streaming
                    if not viewer.wait_for_ready(timeout=15.0):
                        unregister_launching_viewer(viewer.napari_port)
                        raise RuntimeError(f"Napari viewer on port {viewer.napari_port} failed to become ready")

                    logger.info(f"Napari viewer on port {viewer.napari_port} is ready")
                    # Unregister from launching registry (now ready)
                    unregister_launching_viewer(viewer.napari_port)
                else:
                    logger.info(f"Napari viewer on port {viewer.napari_port} is already running")

                # Use the napari streaming backend to send the batch
                from openhcs.constants.constants import Backend as BackendEnum

                # Prepare metadata for streaming
                metadata = {
                    'napari_port': viewer.napari_port,
                    'display_config': config,
                    'microscope_handler': self.orchestrator.microscope_handler,
                    'step_index': 0,
                    'step_name': 'image_browser'
                }

                # Stream batch to Napari
                self.filemanager.save_batch(
                    image_data_list,
                    file_paths,
                    BackendEnum.NAPARI_STREAM.value,
                    **metadata
                )
                logger.info(f"Successfully streamed batch of {len(file_paths)} images to Napari on port {viewer.napari_port}")
            except Exception as e:
                logger.error(f"Failed to load/stream batch to Napari: {e}")
                # Show error in UI thread
                from PyQt6.QtCore import QMetaObject, Qt
                QMetaObject.invokeMethod(
                    self, "_show_streaming_error",
                    Qt.ConnectionType.QueuedConnection,
                    str(e)
                )

        # Start loading and streaming in background thread
        thread = threading.Thread(target=load_and_stream, daemon=True)
        thread.start()
        logger.info(f"Started background thread to load and stream {len(filenames)} images to Napari")

    def _stream_batch_to_napari(self, viewer, image_data_list: list, file_paths: list, config):
        """Stream batch of images to Napari viewer asynchronously (builds hyperstack)."""
        # Stream in background thread to avoid blocking UI
        import threading

        def stream_async():
            try:
                from openhcs.pyqt_gui.widgets.shared.zmq_server_manager import (
                    register_launching_viewer, unregister_launching_viewer
                )

                # Check if viewer is already ready (quick ping with short timeout)
                # If it responds immediately, it was already running - don't show as launching
                is_already_running = viewer.wait_for_ready(timeout=0.1)

                if not is_already_running:
                    # Viewer is launching - register it and show in UI
                    register_launching_viewer(viewer.napari_port, 'napari', len(file_paths))
                    logger.info(f"Waiting for Napari viewer on port {viewer.napari_port} to be ready...")

                    # Wait for viewer to be ready before streaming
                    if not viewer.wait_for_ready(timeout=15.0):
                        unregister_launching_viewer(viewer.napari_port)
                        raise RuntimeError(f"Napari viewer on port {viewer.napari_port} failed to become ready")

                    logger.info(f"Napari viewer on port {viewer.napari_port} is ready")
                    # Unregister from launching registry (now ready)
                    unregister_launching_viewer(viewer.napari_port)
                else:
                    logger.info(f"Napari viewer on port {viewer.napari_port} is already running")

                # Use the napari streaming backend to send the batch
                from openhcs.constants.constants import Backend as BackendEnum

                # Prepare metadata for streaming
                metadata = {
                    'napari_port': viewer.napari_port,
                    'display_config': config,
                    'microscope_handler': self.orchestrator.microscope_handler,
                    'step_index': 0,
                    'step_name': 'image_browser'
                }

                # Stream batch to Napari
                self.filemanager.save_batch(
                    image_data_list,
                    file_paths,
                    BackendEnum.NAPARI_STREAM.value,
                    **metadata
                )
                logger.info(f"Successfully streamed batch of {len(file_paths)} images to Napari on port {viewer.napari_port}")
            except Exception as e:
                logger.error(f"Failed to stream batch to Napari: {e}")
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
        logger.info(f"Streaming batch of {len(file_paths)} images to Napari asynchronously...")

    @pyqtSlot(str)
    def _show_streaming_error(self, error_msg: str):
        """Show streaming error in UI thread (called via QMetaObject.invokeMethod)."""
        QMessageBox.warning(self, "Streaming Error", f"Failed to stream images to Napari: {error_msg}")

    def _load_and_stream_batch_to_fiji_async(self, viewer, filenames: list, plate_path: Path,
                                               read_backend: str, config):
        """Load and stream batch of images to Fiji in background thread (NEVER blocks UI)."""
        import threading

        def load_and_stream():
            try:
                # HEAVY OPERATION: Load all images (runs in background thread)
                image_data_list = []
                file_paths = []
                for filename in filenames:
                    image_path = plate_path / filename
                    image_data = self.filemanager.load(str(image_path), read_backend)
                    image_data_list.append(image_data)
                    file_paths.append(filename)

                logger.info(f"Loaded {len(image_data_list)} images in background thread")

                # Register that we're launching a viewer
                from openhcs.pyqt_gui.widgets.shared.zmq_server_manager import (
                    register_launching_viewer, unregister_launching_viewer
                )

                # Check if viewer is already ready (quick ping with short timeout)
                is_already_running = viewer.wait_for_ready(timeout=0.1)

                if not is_already_running:
                    # Viewer is launching - register it and show in UI
                    register_launching_viewer(viewer.fiji_port, 'fiji', len(file_paths))
                    logger.info(f"Waiting for Fiji viewer on port {viewer.fiji_port} to be ready...")

                    # Wait for viewer to be ready before streaming
                    if not viewer.wait_for_ready(timeout=15.0):
                        unregister_launching_viewer(viewer.fiji_port)
                        raise RuntimeError(f"Fiji viewer on port {viewer.fiji_port} failed to become ready")

                    logger.info(f"Fiji viewer on port {viewer.fiji_port} is ready")
                    # Unregister from launching registry (now ready)
                    unregister_launching_viewer(viewer.fiji_port)
                else:
                    logger.info(f"Fiji viewer on port {viewer.fiji_port} is already running")

                # Use the Fiji streaming backend to send the batch
                from openhcs.constants.constants import Backend as BackendEnum

                # Prepare metadata for streaming
                metadata = {
                    'fiji_port': viewer.fiji_port,
                    'display_config': config,
                    'microscope_handler': self.orchestrator.microscope_handler,
                    'step_index': 0,
                    'step_name': 'image_browser'
                }

                # Stream batch to Fiji
                self.filemanager.save_batch(
                    image_data_list,
                    file_paths,
                    BackendEnum.FIJI_STREAM.value,
                    **metadata
                )
                logger.info(f"Successfully streamed batch of {len(file_paths)} images to Fiji on port {viewer.fiji_port}")
            except Exception as e:
                logger.error(f"Failed to load/stream batch to Fiji: {e}")
                # Show error in UI thread
                from PyQt6.QtCore import QMetaObject, Qt
                QMetaObject.invokeMethod(
                    self, "_show_fiji_streaming_error",
                    Qt.ConnectionType.QueuedConnection,
                    str(e)
                )

        # Start loading and streaming in background thread
        thread = threading.Thread(target=load_and_stream, daemon=True)
        thread.start()
        logger.info(f"Started background thread to load and stream {len(filenames)} images to Fiji")

    def _stream_batch_to_fiji(self, viewer, image_data_list: list, file_paths: list, config):
        """Stream batch of images to Fiji viewer asynchronously (builds hyperstack)."""
        # Stream in background thread to avoid blocking UI
        import threading

        def stream_async():
            try:
                from openhcs.pyqt_gui.widgets.shared.zmq_server_manager import (
                    register_launching_viewer, unregister_launching_viewer
                )

                # Check if viewer is already ready (quick ping with short timeout)
                # If it responds immediately, it was already running - don't show as launching
                is_already_running = viewer.wait_for_ready(timeout=0.1)

                if not is_already_running:
                    # Viewer is launching - register it and show in UI
                    register_launching_viewer(viewer.fiji_port, 'fiji', len(file_paths))
                    logger.info(f"Waiting for Fiji viewer on port {viewer.fiji_port} to be ready...")

                    # Wait for viewer to be ready before streaming
                    if not viewer.wait_for_ready(timeout=15.0):
                        unregister_launching_viewer(viewer.fiji_port)
                        raise RuntimeError(f"Fiji viewer on port {viewer.fiji_port} failed to become ready")

                    logger.info(f"Fiji viewer on port {viewer.fiji_port} is ready")
                    # Unregister from launching registry (now ready)
                    unregister_launching_viewer(viewer.fiji_port)
                else:
                    logger.info(f"Fiji viewer on port {viewer.fiji_port} is already running")

                # Use the Fiji streaming backend to send the batch
                from openhcs.constants.constants import Backend as BackendEnum

                # Prepare metadata for streaming
                metadata = {
                    'fiji_port': viewer.fiji_port,
                    'display_config': config,
                    'microscope_handler': self.orchestrator.microscope_handler,
                    'step_index': 0,
                    'step_name': 'image_browser'
                }

                # Stream batch to Fiji
                self.filemanager.save_batch(
                    image_data_list,
                    file_paths,
                    BackendEnum.FIJI_STREAM.value,
                    **metadata
                )
                logger.info(f"Successfully streamed batch of {len(file_paths)} images to Fiji on port {viewer.fiji_port}")
            except Exception as e:
                logger.error(f"Failed to stream batch to Fiji: {e}")
                # Show error in UI thread
                from PyQt6.QtCore import QMetaObject, Qt
                QMetaObject.invokeMethod(
                    self, "_show_fiji_streaming_error",
                    Qt.ConnectionType.QueuedConnection,
                    str(e)
                )

        # Start streaming in background thread
        thread = threading.Thread(target=stream_async, daemon=True)
        thread.start()
        logger.info(f"Streaming batch of {len(file_paths)} images to Fiji asynchronously...")

    @pyqtSlot(str)
    def _show_fiji_streaming_error(self, error_msg: str):
        """Show Fiji streaming error in UI thread."""
        QMessageBox.warning(self, "Streaming Error", f"Failed to stream images to Fiji: {error_msg}")

    def cleanup(self):
        """Clean up viewers - orchestrator manages viewer lifecycle."""
        # Viewers are managed by orchestrator, no cleanup needed here
        pass

    # ========== Plate View Methods ==========

    def _toggle_plate_view(self, checked: bool):
        """Toggle plate view visibility."""
        # If detached, just show/hide the window
        if self.plate_view_detached_window:
            self.plate_view_detached_window.setVisible(checked)
            if checked:
                self.plate_view_toggle_btn.setText("Hide Plate View")
            else:
                self.plate_view_toggle_btn.setText("Show Plate View")
            return

        # Otherwise toggle in main layout
        self.plate_view_widget.setVisible(checked)

        if checked:
            self.plate_view_toggle_btn.setText("Hide Plate View")
            # Update plate view with current images
            self._update_plate_view()
        else:
            self.plate_view_toggle_btn.setText("Show Plate View")

    def _detach_plate_view(self):
        """Detach plate view to external window."""
        if self.plate_view_detached_window:
            # Already detached, just show it
            self.plate_view_detached_window.show()
            self.plate_view_detached_window.raise_()
            return

        from PyQt6.QtWidgets import QDialog

        # Create detached window
        self.plate_view_detached_window = QDialog(self)
        self.plate_view_detached_window.setWindowTitle("Plate View")
        self.plate_view_detached_window.setWindowFlags(Qt.WindowType.Dialog)
        self.plate_view_detached_window.setMinimumSize(600, 400)
        self.plate_view_detached_window.resize(800, 600)

        # Create layout for window
        window_layout = QVBoxLayout(self.plate_view_detached_window)
        window_layout.setContentsMargins(10, 10, 10, 10)

        # Add reattach button
        reattach_btn = QPushButton("⬅ Reattach to Main Window")
        reattach_btn.setStyleSheet(self.style_gen.generate_button_style())
        reattach_btn.clicked.connect(self._reattach_plate_view)
        window_layout.addWidget(reattach_btn)

        # Move plate view widget to window
        self.plate_view_widget.setParent(self.plate_view_detached_window)
        self.plate_view_widget.setVisible(True)
        window_layout.addWidget(self.plate_view_widget)

        # Connect close event to reattach
        self.plate_view_detached_window.closeEvent = lambda event: self._on_detached_window_closed(event)

        # Show window
        self.plate_view_detached_window.show()

        logger.info("Plate view detached to external window")

    def _reattach_plate_view(self):
        """Reattach plate view to main layout."""
        if not self.plate_view_detached_window:
            return

        # Store reference before clearing
        window = self.plate_view_detached_window
        self.plate_view_detached_window = None

        # Move plate view widget back to splitter
        self.plate_view_widget.setParent(self)
        self.middle_splitter.insertWidget(0, self.plate_view_widget)
        self.plate_view_widget.setVisible(self.plate_view_toggle_btn.isChecked())

        # Close and cleanup detached window
        window.close()
        window.deleteLater()

        logger.info("Plate view reattached to main window")

    def _on_detached_window_closed(self, event):
        """Handle detached window close event - reattach automatically."""
        # Only reattach if window still exists (not already reattached)
        if self.plate_view_detached_window:
            # Clear reference first to prevent double-close
            window = self.plate_view_detached_window
            self.plate_view_detached_window = None

            # Move plate view widget back to splitter
            self.plate_view_widget.setParent(self)
            self.middle_splitter.insertWidget(0, self.plate_view_widget)
            self.plate_view_widget.setVisible(self.plate_view_toggle_btn.isChecked())

            logger.info("Plate view reattached to main window (window closed)")

        event.accept()

    def _on_wells_selected(self, well_ids: Set[str]):
        """Handle well selection from plate view."""
        self.selected_wells = well_ids
        self._apply_combined_filters()

    def _update_plate_view(self):
        """Update plate view with current image data."""
        # Extract all well IDs from current images (filter out failures)
        well_ids = set()
        for filename, metadata in self.all_images.items():
            try:
                well_id = self._extract_well_id(metadata)
                well_ids.add(well_id)
            except (KeyError, ValueError):
                # Skip images without well metadata (e.g., plate-level files)
                pass

        # Update plate view
        self.plate_view_widget.set_available_wells(well_ids)

        # Handle subdirectory selection
        current_folder = self._get_current_folder()
        subdirs = self._detect_plate_subdirs(current_folder)
        self.plate_view_widget.set_subdirectories(subdirs)

    def _matches_wells(self, filename: str, metadata: dict) -> bool:
        """Check if image matches selected wells."""
        try:
            well_id = self._extract_well_id(metadata)
            return well_id in self.selected_wells
        except (KeyError, ValueError):
            # Image has no well metadata, doesn't match well filter
            return False

    def _get_current_folder(self) -> Optional[str]:
        """Get currently selected folder path from tree."""
        selected_items = self.folder_tree.selectedItems()
        if selected_items:
            folder_path = selected_items[0].data(0, Qt.ItemDataRole.UserRole)
            return folder_path
        return None

    def _detect_plate_subdirs(self, current_folder: Optional[str]) -> List[str]:
        """
        Detect plate output subdirectories.

        Logic:
        - If at plate root (no folder selected or root selected), look for subdirs with well images
        - If in a subdir, return empty list (already in a plate output)

        Returns list of subdirectory names (not full paths).
        """
        if not self.orchestrator:
            return []

        plate_path = self.orchestrator.plate_path

        # If no folder selected or root selected, we're at plate root
        if current_folder is None:
            base_path = plate_path
        else:
            # Check if current folder is plate root
            if str(Path(current_folder)) == str(plate_path):
                base_path = plate_path
            else:
                # Already in a subdirectory, no subdirs to show
                return []

        # Find immediate subdirectories that contain well images
        subdirs_with_wells = set()

        for filename in self.all_images.keys():
            file_path = Path(filename)

            # Check if file is in a subdirectory of base_path
            try:
                relative = file_path.relative_to(base_path)
                parts = relative.parts

                # If file is in a subdirectory (not directly in base_path)
                if len(parts) > 1:
                    subdir_name = parts[0]

                    # Check if this file has well metadata
                    metadata = self.all_images[filename]
                    try:
                        self._extract_well_id(metadata)
                        # Has well metadata, add subdir
                        subdirs_with_wells.add(subdir_name)
                    except (KeyError, ValueError):
                        # No well metadata, skip
                        pass
            except ValueError:
                # File not relative to base_path, skip
                pass

        return sorted(list(subdirs_with_wells))

    # ========== Plate View Helper Methods ==========

    def _extract_well_id(self, metadata: dict) -> str:
        """
        Extract well ID from metadata.

        Returns well ID like 'A01', 'B03', 'R01C03', etc.
        Raises KeyError if metadata missing 'well' component.
        """
        # Well ID is a single component in metadata
        return str(metadata['well'])

    def _detect_plate_dimensions(self, well_ids: Set[str]) -> tuple[int, int]:
        """
        Auto-detect plate dimensions from well IDs.

        Uses existing infrastructure:
        - FilenameParser.extract_component_coordinates() to parse each well ID
        - Determines max row/col from parsed coordinates

        Returns (rows, cols) tuple.
        Raises ValueError if well IDs are invalid format.
        """
        parser = self.orchestrator.microscope_handler.parser

        rows = set()
        cols = set()

        for well_id in well_ids:
            # REUSE: Parser's extract_component_coordinates (fail loud if invalid)
            row, col = parser.extract_component_coordinates(well_id)
            rows.add(row)
            cols.add(int(col))

        # Convert row letters to indices (A=1, B=2, AA=27, etc.)
        row_indices = [
            sum((ord(c.upper()) - ord('A') + 1) * (26 ** i)
                for i, c in enumerate(reversed(row)))
            for row in rows
        ]

        return (max(row_indices), max(cols))

