"""
Image Browser Widget for PyQt6 GUI.

Displays a table of all image files from plate metadata and allows users to
view them in Napari with configurable display settings.
"""

import logging
from pathlib import Path
from typing import Optional, List, Dict, Set, Any

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QTableWidget, QTableWidgetItem,
    QPushButton, QLabel, QHeaderView, QAbstractItemView, QMessageBox,
    QSplitter, QGroupBox, QTreeWidget, QTreeWidgetItem, QScrollArea,
    QLineEdit, QTabWidget, QTextEdit
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
    _status_update_signal = pyqtSignal(str)  # Internal signal for thread-safe status updates

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

        # File data tracking (images + results)
        self.all_files = {}  # filename -> metadata dict (merged images + results)
        self.all_images = {}  # filename -> metadata dict (images only, temporary for merging)
        self.all_results = {}  # filename -> file info dict (results only, temporary for merging)
        self.result_full_paths = {}  # filename -> Path (full path for results, for opening files)
        self.filtered_files = {}  # filename -> metadata dict (after search/filter)
        self.selected_wells = set()  # Selected wells for filtering
        self.metadata_keys = []  # Column names from parser metadata (union of all keys)

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

        # Connect internal signal for thread-safe status updates
        self._status_update_signal.connect(self._update_status_label)

        # Load images if orchestrator is provided
        if self.orchestrator:
            self.load_images()

    def init_ui(self):
        """Initialize the user interface."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(5, 5, 5, 5)  # Reduced margins
        layout.setSpacing(5)  # Reduced spacing between rows

        # Search input row with buttons on the right
        search_layout = QHBoxLayout()
        search_layout.setSpacing(10)

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
        search_layout.addWidget(self.search_input, 1)  # Stretch factor 1 - can compress

        # Plate view toggle button (moved from bottom)
        self.plate_view_toggle_btn = QPushButton("Show Plate View")
        self.plate_view_toggle_btn.setCheckable(True)
        self.plate_view_toggle_btn.clicked.connect(self._toggle_plate_view)
        self.plate_view_toggle_btn.setStyleSheet(self.style_gen.generate_button_style())
        search_layout.addWidget(self.plate_view_toggle_btn, 0)  # No stretch

        # Refresh button (moved from bottom)
        self.refresh_btn = QPushButton("Refresh")
        self.refresh_btn.clicked.connect(self.load_images)
        self.refresh_btn.setStyleSheet(self.style_gen.generate_button_style())
        search_layout.addWidget(self.refresh_btn, 0)  # No stretch

        # Info label (moved from bottom)
        self.info_label = QLabel("No images loaded")
        self.info_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_disabled)};")
        search_layout.addWidget(self.info_label, 0)  # No stretch

        layout.addLayout(search_layout)

        # Create main splitter (tree+filters | table | config)
        main_splitter = QSplitter(Qt.Orientation.Horizontal)

        # Left panel: Vertical splitter for Folder tree + Column filters
        left_splitter = QSplitter(Qt.Orientation.Vertical)

        # Folder tree
        tree_widget = self._create_folder_tree()
        left_splitter.addWidget(tree_widget)

        # Column filter panel (initially empty, populated when images load)
        # DO NOT wrap in scroll area - breaks splitter resizing!
        # Each filter has its own scroll area for checkboxes
        self.column_filter_panel = MultiColumnFilterPanel(color_scheme=self.color_scheme)
        self.column_filter_panel.filters_changed.connect(self._on_column_filters_changed)
        self.column_filter_panel.setVisible(False)  # Hidden until images load
        left_splitter.addWidget(self.column_filter_panel)

        # Set initial sizes: filters get more space (20% tree, 80% filters)
        left_splitter.setSizes([100, 400])

        main_splitter.addWidget(left_splitter)

        # Middle: Vertical splitter for plate view and tabs
        self.middle_splitter = QSplitter(Qt.Orientation.Vertical)

        # Plate view (initially hidden)
        from openhcs.pyqt_gui.widgets.shared.plate_view_widget import PlateViewWidget
        self.plate_view_widget = PlateViewWidget(color_scheme=self.color_scheme, parent=self)
        self.plate_view_widget.wells_selected.connect(self._on_wells_selected)
        self.plate_view_widget.detach_requested.connect(self._detach_plate_view)
        self.plate_view_widget.setVisible(False)
        self.middle_splitter.addWidget(self.plate_view_widget)

        # Single table for both images and results (no tabs needed)
        image_table_widget = self._create_table_widget()
        self.middle_splitter.addWidget(image_table_widget)

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

        # Connect selection change
        self.file_table.itemSelectionChanged.connect(self.on_selection_changed)

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
        """Create and configure the unified file table widget (images + results)."""
        table_container = QWidget()
        layout = QVBoxLayout(table_container)
        layout.setContentsMargins(0, 0, 0, 0)

        # Unified table for images and results (columns will be set dynamically based on parser metadata)
        self.file_table = QTableWidget()
        self.file_table.setColumnCount(2)  # Start with Filename + Type
        self.file_table.setHorizontalHeaderLabels(["Filename", "Type"])

        # Configure table
        self.file_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.file_table.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)  # Enable multi-selection
        self.file_table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.file_table.setSortingEnabled(True)

        # Configure header - make all columns resizable and movable (like function selector)
        header = self.file_table.horizontalHeader()
        header.setSectionsMovable(True)  # Allow column reordering
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.Interactive)  # Filename - resizable
        header.setSectionResizeMode(1, QHeaderView.ResizeMode.Interactive)  # Type - resizable

        # Apply styling
        self.file_table.setStyleSheet(self.style_gen.generate_table_widget_style())

        # Connect double-click to view in enabled viewer(s)
        self.file_table.cellDoubleClicked.connect(self.on_file_double_clicked)

        layout.addWidget(self.file_table)

        return table_container

    # Removed _create_results_widget - now using unified file table

    def _create_right_panel(self):
        """Create the right panel with config tabs and instance manager."""
        container = QWidget()
        container.setMinimumWidth(300)  # Prevent clipping of config widgets
        layout = QVBoxLayout(container)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(5)

        # Tab bar row with view buttons
        tab_row = QHBoxLayout()
        tab_row.setContentsMargins(0, 0, 0, 0)
        tab_row.setSpacing(5)

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

        # Extract tab bar and add to horizontal layout
        self.tab_bar = self.streaming_tabs.tabBar()
        self.tab_bar.setExpanding(False)
        self.tab_bar.setUsesScrollButtons(False)
        tab_row.addWidget(self.tab_bar, 0)  # No stretch - tabs at natural size

        # View buttons beside tabs
        self.view_napari_btn = QPushButton("View in Napari")
        self.view_napari_btn.clicked.connect(self.view_selected_in_napari)
        self.view_napari_btn.setStyleSheet(self.style_gen.generate_button_style())
        self.view_napari_btn.setEnabled(False)
        tab_row.addWidget(self.view_napari_btn, 0)  # No stretch

        self.view_fiji_btn = QPushButton("View in Fiji")
        self.view_fiji_btn.clicked.connect(self.view_selected_in_fiji)
        self.view_fiji_btn.setStyleSheet(self.style_gen.generate_button_style())
        self.view_fiji_btn.setEnabled(False)
        tab_row.addWidget(self.view_fiji_btn, 0)  # No stretch

        layout.addLayout(tab_row)

        # Vertical splitter for configs and instance manager
        vertical_splitter = QSplitter(Qt.Orientation.Vertical)

        # Extract the stacked widget (content area) from tab widget and add it to splitter
        # The tab bar is already in tab_row above
        from PyQt6.QtWidgets import QStackedWidget
        stacked_widget = self.streaming_tabs.findChild(QStackedWidget)
        if stacked_widget:
            stacked_widget.setMinimumWidth(300)  # Prevent clipping of config widgets
            vertical_splitter.addWidget(stacked_widget)

        # Instance manager panel
        instance_panel = self._create_instance_manager_panel()
        vertical_splitter.addWidget(instance_panel)

        # Set initial sizes (80% configs, 20% instance manager)
        vertical_splitter.setSizes([400, 100])

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
            context_obj=context_obj,
            color_scheme=self.color_scheme
        )

        # Wrap in scroll area for long forms (vertical scrolling only)
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
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
            context_obj=context_obj,
            color_scheme=self.color_scheme
        )

        # Wrap in scroll area for long forms (vertical scrolling only)
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
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
        self.view_napari_btn.setEnabled(checked and len(self.file_table.selectedItems()) > 0)
        self._update_tab_labels()

    def _on_fiji_enable_toggled(self, checked: bool):
        """Handle Fiji enable checkbox toggle."""
        self.fiji_config_form.setEnabled(checked)
        self.view_fiji_btn.setEnabled(checked and len(self.file_table.selectedItems()) > 0)
        self._update_tab_labels()

    def _create_instance_manager_panel(self):
        """Create the viewer instance manager panel using ZMQServerManagerWidget."""
        from openhcs.pyqt_gui.widgets.shared.zmq_server_manager import ZMQServerManagerWidget
        from openhcs.core.config import get_all_streaming_ports

        # Scan all streaming ports using orchestrator's pipeline config
        # This ensures we find viewers launched with custom ports
        # Exclude execution server port (only want viewer ports)
        from openhcs.constants.constants import DEFAULT_EXECUTION_SERVER_PORT
        all_ports = get_all_streaming_ports(
            config=self.orchestrator.pipeline_config if self.orchestrator else None,
            num_ports_per_type=10
        )
        ports_to_scan = [p for p in all_ports if p != DEFAULT_EXECUTION_SERVER_PORT]

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

        # Use orchestrator's FileManager (has plate-specific backends like VirtualWorkspaceBackend)
        if orchestrator:
            self.filemanager = orchestrator.filemanager
            logger.debug("Image browser now using orchestrator's FileManager")

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
        # Start with search-filtered files
        result = self.filtered_files.copy()

        # Apply folder filter if a folder is selected
        selected_items = self.folder_tree.selectedItems()
        if selected_items:
            folder_path = selected_items[0].data(0, Qt.ItemDataRole.UserRole)
            if folder_path:  # Not root
                # Filter by folder - include both the selected folder AND its associated results folder
                # e.g., if "images" is selected, also include "images_results"
                results_folder_path = f"{folder_path}_results"

                result = {
                    filename: metadata for filename, metadata in result.items()
                    if (str(Path(filename).parent) == folder_path or
                        filename.startswith(folder_path + "/") or
                        str(Path(filename).parent) == results_folder_path or
                        filename.startswith(results_folder_path + "/"))
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
                        raw_value = metadata.get(metadata_key, '')
                        # Get display value for comparison (metadata name if available)
                        item_value = self._get_metadata_display_value(metadata_key, raw_value)
                        if item_value not in selected_values:
                            matches = False
                            break
                    if matches:
                        filtered_result[filename] = metadata
                result = filtered_result

        # Update table with combined filters
        self._populate_table(result)
        logger.debug(f"Combined filters: {len(result)} images shown")

    def _get_metadata_display_value(self, metadata_key: str, raw_value: Any) -> str:
        """
        Get display value for metadata, using metadata cache if available.

        For components like channel, this returns "1 | W1" format (raw key | metadata name)
        to preserve both the number and the metadata name. This handles cases where
        different subdirectories might have the same channel number mapped to different names.

        Args:
            metadata_key: Metadata key (e.g., "channel", "site", "well")
            raw_value: Raw value from parser (e.g., 1, 2, "A01")

        Returns:
            Display value in format "raw_key | metadata_name" if metadata available,
            otherwise just "raw_key"
        """
        if raw_value is None:
            return 'N/A'

        # Convert to string for lookup
        value_str = str(raw_value)

        # Try to get metadata display name from cache
        if self.orchestrator:
            try:
                # Map metadata_key to AllComponents enum
                from openhcs.constants import AllComponents
                component_map = {
                    'channel': AllComponents.CHANNEL,
                    'site': AllComponents.SITE,
                    'z_index': AllComponents.Z_INDEX,
                    'timepoint': AllComponents.TIMEPOINT,
                    'well': AllComponents.WELL,
                }

                component = component_map.get(metadata_key)
                if component:
                    metadata_name = self.orchestrator._metadata_cache_service.get_component_metadata(component, value_str)
                    if metadata_name:
                        # Format like TUI: "Channel 1 | HOECHST 33342"
                        # But for table cells, just show "1 | W1" (more compact)
                        return f"{value_str} | {metadata_name}"
            except Exception as e:
                logger.debug(f"Could not get metadata for {metadata_key} {value_str}: {e}")

        # Fallback to raw value only
        return value_str

    def _build_column_filters(self):
        """Build column filter widgets from loaded file metadata."""
        if not self.all_files or not self.metadata_keys:
            return

        # Clear existing filters
        self.column_filter_panel.clear_all_filters()

        # Extract unique values for each metadata column
        for metadata_key in self.metadata_keys:
            unique_values = set()
            for metadata in self.all_files.values():
                value = metadata.get(metadata_key)
                if value is not None:
                    # Use metadata display value instead of raw value
                    display_value = self._get_metadata_display_value(metadata_key, value)
                    unique_values.add(display_value)

            if unique_values:
                # Create filter for this column
                column_display_name = metadata_key.replace('_', ' ').title()
                self.column_filter_panel.add_column_filter(column_display_name, sorted(list(unique_values)))

        # Show filter panel if we have filters
        if self.column_filter_panel.column_filters:
            self.column_filter_panel.setVisible(True)

        # Connect well filter to plate view for bidirectional sync
        if 'Well' in self.column_filter_panel.column_filters and self.plate_view_widget:
            well_filter = self.column_filter_panel.column_filters['Well']
            self.plate_view_widget.set_well_filter_widget(well_filter)

            # Connect well filter changes to sync back to plate view
            well_filter.filter_changed.connect(self._on_well_filter_changed)

        logger.debug(f"Built {len(self.column_filter_panel.column_filters)} column filters")

    def _on_column_filters_changed(self):
        """Handle column filter changes."""
        self._apply_combined_filters()

    def _on_well_filter_changed(self):
        """Handle well filter checkbox changes - sync to plate view."""
        if self.plate_view_widget:
            self.plate_view_widget.sync_from_well_filter()
        # Apply the filter to the table
        self._apply_combined_filters()

    def filter_images(self, search_term: str):
        """Filter files using shared search service (canonical code path)."""
        from openhcs.ui.shared.search_service import SearchService

        # Create searchable text extractor
        def create_searchable_text(metadata):
            """Create searchable text from file metadata."""
            searchable_fields = [metadata.get('filename', '')]
            # Add all metadata values
            for key, value in metadata.items():
                if key != 'filename' and value is not None:
                    searchable_fields.append(str(value))
            return " ".join(str(field) for field in searchable_fields)

        # Create search service if not exists
        if not hasattr(self, '_search_service'):
            self._search_service = SearchService(
                all_items=self.all_files,
                searchable_text_extractor=create_searchable_text
            )

        # Update search service with current files
        self._search_service.update_items(self.all_files)

        # Perform search using shared service
        self.filtered_files = self._search_service.filter(search_term)

        # Apply combined filters (search + folder + column filters)
        self._apply_combined_filters()

    def load_images(self):
        """Load image files from the orchestrator's metadata."""
        if not self.orchestrator:
            self.info_label.setText("No plate loaded")
            # Still try to load results even if no orchestrator
            self.load_results()
            return

        try:
            logger.info("IMAGE BROWSER: Starting load_images()")
            # Get metadata handler from orchestrator
            handler = self.orchestrator.microscope_handler
            metadata_handler = handler.metadata_handler
            logger.info(f"IMAGE BROWSER: Got metadata handler: {type(metadata_handler).__name__}")

            # Get image files from metadata
            plate_path = self.orchestrator.plate_path
            logger.info(f"IMAGE BROWSER: Calling get_image_files for plate: {plate_path}")
            image_files = metadata_handler.get_image_files(plate_path)
            logger.info(f"IMAGE BROWSER: get_image_files returned {len(image_files) if image_files else 0} files")

            if not image_files:
                self.info_label.setText("No images found")
                # Still load results even if no images
                self.load_results()
                return

            # Build all_images dictionary
            self.all_images = {}
            for filename in image_files:
                parsed = handler.parser.parse_filename(filename)
                metadata = {'filename': filename}
                if parsed:
                    metadata.update(parsed)
                self.all_images[filename] = metadata

            logger.info(f"IMAGE BROWSER: Built all_images dict with {len(self.all_images)} entries")

        except Exception as e:
            logger.error(f"Failed to load images: {e}", exc_info=True)
            QMessageBox.warning(self, "Error", f"Failed to load images: {e}")
            self.info_label.setText("Error loading images")
            self.all_images = {}

        # Load results and merge with images
        self.load_results()

        # Merge images and results into unified all_files dictionary
        self.all_files = {**self.all_images, **self.all_results}

        # Determine metadata keys from all files (union of all keys)
        all_keys = set()
        for file_metadata in self.all_files.values():
            all_keys.update(file_metadata.keys())

        # Remove 'filename' from keys (it's always the first column)
        all_keys.discard('filename')

        # Sort keys for consistent column order (extension first, then alphabetical)
        self.metadata_keys = sorted(all_keys, key=lambda k: (k != 'extension', k))

        # Set up table columns: Filename + metadata keys
        column_headers = ["Filename"] + [k.replace('_', ' ').title() for k in self.metadata_keys]
        self.file_table.setColumnCount(len(column_headers))
        self.file_table.setHorizontalHeaderLabels(column_headers)

        # Set all columns to Interactive resize mode
        header = self.file_table.horizontalHeader()
        for col in range(len(column_headers)):
            header.setSectionResizeMode(col, QHeaderView.ResizeMode.Interactive)

        # Initialize filtered files to all files
        self.filtered_files = self.all_files.copy()

        # Build folder tree from file paths
        self._build_folder_tree()

        # Build column filters from metadata
        self._build_column_filters()

        # Populate table
        self._populate_table(self.filtered_files)

        # Update info label
        total_files = len(self.all_files)
        num_images = len(self.all_images)
        num_results = len(self.all_results)
        self.info_label.setText(f"{total_files} files loaded ({num_images} images, {num_results} results)")

        # Update plate view if visible
        if self.plate_view_widget and self.plate_view_widget.isVisible():
            self._update_plate_view()

    def load_results(self):
        """Load result files (ROI JSON, CSV) from the results directory and populate self.all_results."""
        self.all_results = {}

        if not self.orchestrator:
            logger.warning("IMAGE BROWSER RESULTS: No orchestrator available")
            return

        try:
            # Get results directory from metadata (single source of truth)
            # The metadata contains the results_dir field that was calculated during compilation
            handler = self.orchestrator.microscope_handler
            plate_path = self.orchestrator.plate_path

            # Load metadata JSON directly
            from openhcs.io.metadata_writer import get_metadata_path
            import json

            metadata_path = get_metadata_path(plate_path)
            if not metadata_path.exists():
                logger.warning(f"IMAGE BROWSER RESULTS: Metadata file not found: {metadata_path}")
                self.all_results = {}
                return

            with open(metadata_path) as f:
                metadata = json.load(f)

            # Find the main subdirectory's results_dir field
            results_dir = None
            if metadata and 'subdirectories' in metadata:
                # First try to find the subdirectory marked as main
                for subdir_name, subdir_metadata in metadata['subdirectories'].items():
                    if subdir_metadata.get('main') and 'results_dir' in subdir_metadata and subdir_metadata['results_dir']:
                        # Build full path: plate_path / results_dir
                        results_dir = plate_path / subdir_metadata['results_dir']
                        logger.info(f"IMAGE BROWSER RESULTS: Found results_dir in main subdirectory '{subdir_name}': {subdir_metadata['results_dir']}")
                        break

                # Fallback: if no main subdirectory, use first subdirectory with results_dir
                if not results_dir:
                    for subdir_name, subdir_metadata in metadata['subdirectories'].items():
                        if 'results_dir' in subdir_metadata and subdir_metadata['results_dir']:
                            results_dir = plate_path / subdir_metadata['results_dir']
                            logger.info(f"IMAGE BROWSER RESULTS: Found results_dir in subdirectory '{subdir_name}': {subdir_metadata['results_dir']}")
                            break

            if not results_dir:
                logger.warning("IMAGE BROWSER RESULTS: No results_dir found in metadata")
                return

            logger.info(f"IMAGE BROWSER RESULTS: plate_path = {plate_path}")
            logger.info(f"IMAGE BROWSER RESULTS: Resolved results directory = {results_dir}")

            if not results_dir.exists():
                logger.warning(f"IMAGE BROWSER RESULTS: Results directory does not exist: {results_dir}")
                return

            # Get parser from orchestrator for filename parsing
            handler = self.orchestrator.microscope_handler

            # Scan for ROI JSON files and CSV files
            logger.info(f"IMAGE BROWSER RESULTS: Scanning directory recursively...")
            file_count = 0
            for file_path in results_dir.rglob('*'):
                if file_path.is_file():
                    file_count += 1
                    suffix = file_path.suffix.lower()
                    logger.debug(f"IMAGE BROWSER RESULTS: Found file: {file_path.name} (suffix={suffix})")

                    # Determine file type using FileFormat registry
                    from openhcs.constants.constants import FileFormat

                    file_type = None
                    if file_path.name.endswith('.roi.zip'):
                        file_type = 'ROI'
                        logger.info(f"IMAGE BROWSER RESULTS: ✓ Matched as ROI: {file_path.name}")
                    elif suffix in FileFormat.CSV.value:
                        file_type = 'CSV'
                        logger.info(f"IMAGE BROWSER RESULTS: ✓ Matched as CSV: {file_path.name}")
                    elif suffix in FileFormat.JSON.value:
                        file_type = 'JSON'
                        logger.info(f"IMAGE BROWSER RESULTS: ✓ Matched as JSON: {file_path.name}")
                    else:
                        logger.debug(f"IMAGE BROWSER RESULTS: ✗ Filtered out: {file_path.name} (suffix={suffix})")

                    if file_type:
                        # Get relative path from plate_path (not results_dir) to include subdirectory
                        rel_path = file_path.relative_to(plate_path)

                        # Get file size
                        size_bytes = file_path.stat().st_size
                        if size_bytes < 1024:
                            size_str = f"{size_bytes} B"
                        elif size_bytes < 1024 * 1024:
                            size_str = f"{size_bytes / 1024:.1f} KB"
                        else:
                            size_str = f"{size_bytes / (1024 * 1024):.1f} MB"

                        # Parse ONLY the filename (not the full path) to extract metadata
                        parsed = handler.parser.parse_filename(file_path.name)

                        # Build file info with parsed metadata (no full_path in metadata dict)
                        file_info = {
                            'filename': str(rel_path),
                            'type': file_type,
                            'size': size_str,
                        }

                        # Add parsed metadata components if parsing succeeded
                        if parsed:
                            file_info.update(parsed)
                            logger.info(f"IMAGE BROWSER RESULTS: ✓ Parsed result: {file_path.name} -> {parsed}")
                            logger.info(f"IMAGE BROWSER RESULTS:   Full file_info: {file_info}")
                        else:
                            logger.warning(f"IMAGE BROWSER RESULTS: ✗ Could not parse filename: {file_path.name}")

                        # Store file info and full path separately
                        self.all_results[str(rel_path)] = file_info
                        self.result_full_paths[str(rel_path)] = file_path

            logger.info(f"IMAGE BROWSER RESULTS: Scanned {file_count} total files, matched {len(self.all_results)} result files")

        except Exception as e:
            logger.error(f"IMAGE BROWSER RESULTS: Failed to load results: {e}", exc_info=True)

    # Removed _populate_results_table - now using unified _populate_table
    # Removed on_result_double_clicked - now using unified on_file_double_clicked

    def _stream_roi_file(self, roi_zip_path: Path):
        """Load ROI .roi.zip file and stream to enabled viewer(s)."""
        try:
            from openhcs.core.roi import load_rois_from_zip

            # Load ROIs from .roi.zip archive
            rois = load_rois_from_zip(roi_zip_path)

            if not rois:
                QMessageBox.information(self, "No ROIs", f"No ROIs found in {roi_zip_path.name}")
                return

            # Check which viewers are enabled
            napari_enabled = self.napari_enable_checkbox.isChecked()
            fiji_enabled = self.fiji_enable_checkbox.isChecked()

            if not napari_enabled and not fiji_enabled:
                QMessageBox.information(
                    self,
                    "No Viewer Enabled",
                    "Please enable Napari or Fiji streaming to view ROIs."
                )
                return

            # Stream to enabled viewers
            if napari_enabled:
                self._stream_rois_to_napari(rois, roi_zip_path)

            if fiji_enabled:
                self._stream_rois_to_fiji(rois, roi_zip_path)

            logger.info(f"Streamed {len(rois)} ROIs from {roi_zip_path.name}")

        except Exception as e:
            logger.error(f"Failed to stream ROI file: {e}")
            QMessageBox.warning(self, "Error", f"Failed to stream ROI file: {e}")

    def _populate_table(self, files_dict: Dict[str, Dict]):
        """Populate table with files (images + results) from dictionary."""
        # Clear table
        self.file_table.setRowCount(0)

        # Populate rows
        for i, (filename, metadata) in enumerate(files_dict.items()):
            self.file_table.insertRow(i)

            # Filename column
            filename_item = QTableWidgetItem(filename)
            filename_item.setData(Qt.ItemDataRole.UserRole, filename)
            self.file_table.setItem(i, 0, filename_item)

            # Metadata columns - use metadata display values
            for col_idx, key in enumerate(self.metadata_keys, start=1):
                value = metadata.get(key, 'N/A')
                # Get display value (metadata name if available, otherwise raw value)
                display_value = self._get_metadata_display_value(key, value)
                self.file_table.setItem(i, col_idx, QTableWidgetItem(display_value))

    def _build_folder_tree(self):
        """Build folder tree from file paths (images + results)."""
        # Save current selection before rebuilding
        selected_folder = None
        selected_items = self.folder_tree.selectedItems()
        if selected_items:
            selected_folder = selected_items[0].data(0, Qt.ItemDataRole.UserRole)

        self.folder_tree.clear()

        # Extract unique folder paths (exclude *_results folders since they're auto-included)
        folders: Set[str] = set()
        for filename in self.all_files.keys():
            path = Path(filename)
            # Add all parent directories
            for parent in path.parents:
                parent_str = str(parent)
                if parent_str != '.' and not parent_str.endswith('_results'):
                    folders.add(parent_str)

        # Build tree structure
        root_item = QTreeWidgetItem(["All Files"])
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
        has_selection = len(self.file_table.selectedItems()) > 0
        # Enable buttons based on selection AND checkbox state
        self.view_napari_btn.setEnabled(has_selection and self.napari_enable_checkbox.isChecked())
        self.view_fiji_btn.setEnabled(has_selection and self.fiji_enable_checkbox.isChecked())
    
    def on_file_double_clicked(self, row: int, column: int):
        """Handle double-click on a file row - stream images or display results."""
        # Get file info from table
        filename_item = self.file_table.item(row, 0)
        filename = filename_item.data(Qt.ItemDataRole.UserRole)

        # Check if this is a result file (has 'type' field) or an image
        file_info = self.all_files.get(filename, {})
        file_type = file_info.get('type')

        if file_type:
            # This is a result file (ROI, CSV, JSON)
            self._handle_result_double_click(file_info)
        else:
            # This is an image file
            self._handle_image_double_click()

    def _handle_image_double_click(self):
        """Handle double-click on an image - stream to enabled viewer(s)."""
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

    def _handle_result_double_click(self, file_info: dict):
        """Handle double-click on a result file - stream ROIs or display CSV."""
        filename = file_info['filename']
        file_path = self.result_full_paths.get(filename)

        if not file_path:
            logger.error(f"Could not find full path for result file: {filename}")
            return

        file_type = file_info['type']

        if file_type == 'ROI':
            # Stream ROI JSON to enabled viewer(s)
            self._stream_roi_file(file_path)
        elif file_type == 'CSV':
            # Open CSV in system default application
            import subprocess
            subprocess.run(['xdg-open', str(file_path)])
        elif file_type == 'JSON':
            # Open JSON in system default application
            import subprocess
            subprocess.run(['xdg-open', str(file_path)])
    
    def view_selected_in_napari(self):
        """View all selected images in Napari as a batch (builds hyperstack)."""
        selected_rows = self.file_table.selectionModel().selectedRows()
        if not selected_rows:
            return

        # Collect all filenames and separate ROI files from images
        image_filenames = []
        roi_filenames = []
        for row_index in selected_rows:
            row = row_index.row()
            filename_item = self.file_table.item(row, 0)
            filename = filename_item.data(Qt.ItemDataRole.UserRole)

            # Check if this is a .roi.zip file
            if filename.endswith('.roi.zip'):
                roi_filenames.append(filename)
            else:
                image_filenames.append(filename)

        try:
            # Stream ROI files separately
            if roi_filenames:
                plate_path = Path(self.orchestrator.plate_path)
                for roi_filename in roi_filenames:
                    roi_path = plate_path / roi_filename
                    self._stream_roi_file(roi_path)

            # Stream image files as a batch
            if image_filenames:
                self._load_and_stream_batch_to_napari(image_filenames)

        except Exception as e:
            logger.error(f"Failed to view images in Napari: {e}")
            QMessageBox.warning(self, "Error", f"Failed to view images in Napari: {e}")

    def view_selected_in_fiji(self):
        """View all selected images in Fiji as a batch (builds hyperstack)."""
        selected_rows = self.file_table.selectionModel().selectedRows()
        if not selected_rows:
            return

        # Collect all filenames and separate ROI files from images
        image_filenames = []
        roi_filenames = []
        for row_index in selected_rows:
            row = row_index.row()
            filename_item = self.file_table.item(row, 0)
            filename = filename_item.data(Qt.ItemDataRole.UserRole)

            # Check if this is a .roi.zip file
            if filename.endswith('.roi.zip'):
                roi_filenames.append(filename)
            else:
                image_filenames.append(filename)

        logger.info(f"🎯 IMAGE BROWSER: User selected {len(image_filenames)} images and {len(roi_filenames)} ROI files to view in Fiji")
        logger.info(f"🎯 IMAGE BROWSER: Image filenames: {image_filenames[:5]}{'...' if len(image_filenames) > 5 else ''}")
        if roi_filenames:
            logger.info(f"🎯 IMAGE BROWSER: ROI filenames: {roi_filenames}")

        try:
            # Stream ROI files separately
            if roi_filenames:
                plate_path = Path(self.orchestrator.plate_path)
                for roi_filename in roi_filenames:
                    roi_path = plate_path / roi_filename
                    self._stream_roi_file(roi_path)

            # Stream image files as a batch
            if image_filenames:
                self._load_and_stream_batch_to_fiji(image_filenames)

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
            read_backend = self.orchestrator.microscope_handler.get_primary_backend(plate_path, self.orchestrator.filemanager)

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
            read_backend = self.orchestrator.microscope_handler.get_primary_backend(plate_path, self.orchestrator.filemanager)

        # Resolve Fiji config (lightweight operation, safe in UI thread)
        from openhcs.config_framework.context_manager import config_context
        from openhcs.config_framework.lazy_factory import resolve_lazy_configurations_for_serialization
        from openhcs.core.config import LazyFijiStreamingConfig

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
                # Register that we're launching a viewer BEFORE loading (so UI shows it immediately)
                from openhcs.pyqt_gui.widgets.shared.zmq_server_manager import (
                    register_launching_viewer, unregister_launching_viewer
                )

                # Check if viewer is already ready (quick ping with short timeout)
                is_already_running = viewer.wait_for_ready(timeout=0.1)

                if not is_already_running:
                    # Viewer is launching - register it immediately so UI shows it
                    register_launching_viewer(viewer.napari_port, 'napari', len(filenames))
                    logger.info(f"Registered launching Napari viewer on port {viewer.napari_port} with {len(filenames)} queued images")

                # Show loading status
                self._update_status_threadsafe(f"Loading {len(filenames)} images from disk...")

                # HEAVY OPERATION: Load all images (runs in background thread)
                image_data_list = []
                file_paths = []
                for i, filename in enumerate(filenames, 1):
                    image_path = plate_path / filename
                    image_data = self.filemanager.load(str(image_path), read_backend)
                    image_data_list.append(image_data)
                    file_paths.append(filename)

                    # Update progress every 5 images
                    if i % 5 == 0 or i == len(filenames):
                        self._update_status_threadsafe(f"Loading images: {i}/{len(filenames)}...")

                logger.info(f"Loaded {len(image_data_list)} images in background thread")

                if not is_already_running:
                    # Viewer is launching - wait for it to be ready before streaming
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

                # Build source from subdirectory name (image viewer context)
                # Use first file path to determine subdirectory
                source = Path(file_paths[0]).parent.name if file_paths else 'unknown_source'

                # Prepare metadata for streaming
                metadata = {
                    'napari_port': viewer.napari_port,
                    'display_config': config,
                    'microscope_handler': self.orchestrator.microscope_handler,
                    'source': source
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

                # Build source from subdirectory name (image viewer context)
                # Use first file path to determine subdirectory
                source = Path(file_paths[0]).parent.name if file_paths else 'unknown_source'

                # Prepare metadata for streaming
                metadata = {
                    'napari_port': viewer.napari_port,
                    'display_config': config,
                    'microscope_handler': self.orchestrator.microscope_handler,
                    'source': source
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
                # Register that we're launching a viewer BEFORE loading (so UI shows it immediately)
                from openhcs.pyqt_gui.widgets.shared.zmq_server_manager import (
                    register_launching_viewer, unregister_launching_viewer
                )

                # Check if viewer is already ready (quick ping with short timeout)
                is_already_running = viewer.wait_for_ready(timeout=0.1)

                if not is_already_running:
                    # Viewer is launching - register it immediately so UI shows it
                    register_launching_viewer(viewer.fiji_port, 'fiji', len(filenames))
                    logger.info(f"Registered launching Fiji viewer on port {viewer.fiji_port} with {len(filenames)} queued images")

                # Show loading status
                self._update_status_threadsafe(f"Loading {len(filenames)} images from disk...")

                # HEAVY OPERATION: Load all images (runs in background thread)
                image_data_list = []
                file_paths = []
                for i, filename in enumerate(filenames, 1):
                    image_path = plate_path / filename
                    image_data = self.filemanager.load(str(image_path), read_backend)
                    image_data_list.append(image_data)
                    file_paths.append(filename)

                    # Update progress every 5 images
                    if i % 5 == 0 or i == len(filenames):
                        self._update_status_threadsafe(f"Loading images: {i}/{len(filenames)}...")

                logger.info(f"Loaded {len(image_data_list)} images in background thread")

                if not is_already_running:
                    # Viewer is launching - wait for it to be ready before streaming
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

                # Build source from subdirectory name (image viewer context)
                # Use first file path to determine subdirectory
                source = Path(file_paths[0]).parent.name if file_paths else 'unknown_source'

                # Prepare metadata for streaming
                metadata = {
                    'fiji_port': viewer.fiji_port,
                    'display_config': config,
                    'microscope_handler': self.orchestrator.microscope_handler,
                    'source': source
                }

                # Stream batch to Fiji
                logger.info(f"🚀 IMAGE BROWSER: Calling save_batch with {len(image_data_list)} images")
                self.filemanager.save_batch(
                    image_data_list,
                    file_paths,
                    BackendEnum.FIJI_STREAM.value,
                    **metadata
                )
                logger.info(f"✅ IMAGE BROWSER: Successfully streamed batch of {len(file_paths)} images to Fiji on port {viewer.fiji_port}")
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

                # Build source from subdirectory name (image viewer context)
                # Use first file path to determine subdirectory
                source = Path(file_paths[0]).parent.name if file_paths else 'unknown_source'

                # Prepare metadata for streaming
                metadata = {
                    'fiji_port': viewer.fiji_port,
                    'display_config': config,
                    'microscope_handler': self.orchestrator.microscope_handler,
                    'source': source
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

    def _stream_rois_to_napari(self, rois: list, roi_json_path: Path):
        """Stream ROIs to Napari viewer."""
        try:
            # Get Napari config using current form values
            from openhcs.config_framework.context_manager import config_context
            from openhcs.config_framework.lazy_factory import resolve_lazy_configurations_for_serialization
            from openhcs.core.config import LazyNapariStreamingConfig

            current_values = self.napari_config_form.get_current_values()
            temp_config = LazyNapariStreamingConfig(**{k: v for k, v in current_values.items() if v is not None})

            with config_context(self.orchestrator.pipeline_config):
                with config_context(temp_config):
                    napari_config = resolve_lazy_configurations_for_serialization(temp_config)

            # Get or create viewer
            viewer = self.orchestrator.get_or_create_visualizer(napari_config)

            # Stream ROIs using filemanager.save() - same as pipeline execution
            # Pass display_config and microscope_handler just like image streaming does
            from openhcs.constants.constants import Backend as BackendEnum
            from pathlib import Path

            # Build source from subdirectory name (image viewer context)
            source = Path(roi_json_path).parent.name

            self.filemanager.save(
                rois,
                roi_json_path,
                BackendEnum.NAPARI_STREAM.value,
                host='localhost',
                port=napari_config.port,
                display_config=napari_config,
                microscope_handler=self.orchestrator.microscope_handler,
                source=source
            )

            logger.info(f"Streamed {len(rois)} ROIs to Napari on port {napari_config.port}")

        except Exception as e:
            logger.error(f"Failed to stream ROIs to Napari: {e}")
            raise

    def _stream_rois_to_fiji(self, rois: list, roi_json_path: Path):
        """Stream ROIs to Fiji viewer."""
        try:
            # Get Fiji config using current form values
            from openhcs.config_framework.context_manager import config_context
            from openhcs.config_framework.lazy_factory import resolve_lazy_configurations_for_serialization
            from openhcs.core.config import LazyFijiStreamingConfig

            current_values = self.fiji_config_form.get_current_values()
            temp_config = LazyFijiStreamingConfig(**{k: v for k, v in current_values.items() if v is not None})

            with config_context(self.orchestrator.pipeline_config):
                with config_context(temp_config):
                    fiji_config = resolve_lazy_configurations_for_serialization(temp_config)

            # Get or create viewer
            viewer = self.orchestrator.get_or_create_visualizer(fiji_config)

            # Stream ROIs using filemanager.save() - same as pipeline execution
            # Pass display_config and microscope_handler just like image streaming does
            from openhcs.constants.constants import Backend as BackendEnum
            from pathlib import Path

            # Build source from subdirectory name (image viewer context)
            source = Path(roi_json_path).parent.name

            self.filemanager.save(
                rois,
                roi_json_path,
                BackendEnum.FIJI_STREAM.value,
                fiji_host='localhost',
                fiji_port=fiji_config.fiji_port,
                display_config=fiji_config,
                microscope_handler=self.orchestrator.microscope_handler,
                source=source
            )

            logger.info(f"Streamed {len(rois)} ROIs to Fiji on port {fiji_config.fiji_port}")

        except Exception as e:
            logger.error(f"Failed to stream ROIs to Fiji: {e}")
            raise

    def _display_csv_file(self, csv_path: Path):
        """Display CSV file in preview area."""
        try:
            import pandas as pd

            # Read CSV
            df = pd.read_csv(csv_path)

            # Format as string (show first 100 rows)
            if len(df) > 100:
                preview_text = f"Showing first 100 of {len(df)} rows:\n\n"
                preview_text += df.head(100).to_string(index=False)
            else:
                preview_text = df.to_string(index=False)

            # Show preview
            self.csv_preview.setPlainText(preview_text)
            self.csv_preview.setVisible(True)

            logger.info(f"Displayed CSV file: {csv_path.name} ({len(df)} rows)")

        except Exception as e:
            logger.error(f"Failed to display CSV file: {e}")
            self.csv_preview.setPlainText(f"Error loading CSV: {e}")
            self.csv_preview.setVisible(True)

    def _display_json_file(self, json_path: Path):
        """Display JSON file in preview area."""
        try:
            import json

            # Read JSON
            with open(json_path, 'r') as f:
                data = json.load(f)

            # Format as pretty JSON
            preview_text = json.dumps(data, indent=2)

            # Show preview
            self.csv_preview.setPlainText(preview_text)
            self.csv_preview.setVisible(True)

            logger.info(f"Displayed JSON file: {json_path.name}")

        except Exception as e:
            logger.error(f"Failed to display JSON file: {e}")
            self.csv_preview.setPlainText(f"Error loading JSON: {e}")
            self.csv_preview.setVisible(True)

    def cleanup(self):
        """Clean up resources before widget destruction."""
        # Stop global ack listener thread
        from openhcs.runtime.zmq_base import stop_global_ack_listener
        stop_global_ack_listener()

        # Cleanup ZMQ server manager widget
        if hasattr(self, 'zmq_manager') and self.zmq_manager:
            self.zmq_manager.cleanup()

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
        """Update plate view with current file data (images + results)."""
        # Extract all well IDs from current files (filter out failures)
        well_ids = set()
        for filename, metadata in self.all_files.items():
            try:
                well_id = self._extract_well_id(metadata)
                well_ids.add(well_id)
            except (KeyError, ValueError):
                # Skip files without well metadata (e.g., plate-level files)
                pass

        # Detect plate dimensions and build coordinate mapping
        plate_dimensions = self._detect_plate_dimensions(well_ids) if well_ids else None

        # Build mapping from (row_index, col_index) to actual well_id
        # This handles different well ID formats (A01 vs R01C01)
        coord_to_well = {}
        parser = self.orchestrator.microscope_handler.parser
        for well_id in well_ids:
            row, col = parser.extract_component_coordinates(well_id)
            # Convert row letter to index (A=1, B=2, etc.)
            row_idx = sum((ord(c.upper()) - ord('A') + 1) * (26 ** i)
                         for i, c in enumerate(reversed(row)))
            coord_to_well[(row_idx, int(col))] = well_id

        # Update plate view with well IDs, dimensions, and coordinate mapping
        self.plate_view_widget.set_available_wells(well_ids, plate_dimensions, coord_to_well)

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

        # Find immediate subdirectories that contain well files
        subdirs_with_wells = set()

        for filename in self.all_files.keys():
            file_path = Path(filename)

            # Check if file is in a subdirectory of base_path
            try:
                relative = file_path.relative_to(base_path)
                parts = relative.parts

                # If file is in a subdirectory (not directly in base_path)
                if len(parts) > 1:
                    subdir_name = parts[0]

                    # Check if this file has well metadata
                    metadata = self.all_files[filename]
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

    def _update_status_threadsafe(self, message: str):
        """Update status label from any thread (thread-safe).

        Args:
            message: Status message to display
        """
        self._status_update_signal.emit(message)

    @pyqtSlot(str)
    def _update_status_label(self, message: str):
        """Update status label (called on main thread via signal)."""
        self.info_label.setText(message)

