"""
Plate Metadata Viewer Dialog

Read-only viewer for plate metadata using generic reflection.
Displays SubdirectoryKeyedMetadata or OpenHCSMetadata directly.
"""

import logging
from pathlib import Path
from typing import Optional, Dict, Any
from dataclasses import asdict

from PyQt6.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QPushButton,
    QScrollArea, QWidget, QLabel, QGroupBox
)
from PyQt6.QtCore import Qt

from openhcs.microscopes.openhcs import SubdirectoryKeyedMetadata, OpenHCSMetadata
from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme

logger = logging.getLogger(__name__)


class MetadataViewerDialog(QDialog):
    """
    Read-only metadata viewer dialog.
    
    Uses ParameterFormManager with generic reflection to display
    SubdirectoryKeyedMetadata or OpenHCSMetadata instances.
    """
    
    def __init__(self, orchestrator, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        """
        Initialize metadata viewer dialog.
        
        Args:
            orchestrator: PipelineOrchestrator instance
            color_scheme: Color scheme for styling
            parent: Parent widget
        """
        super().__init__(parent)
        self.orchestrator = orchestrator
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        
        self.setWindowTitle(f"Plate Metadata - {orchestrator.plate_path.name}")
        self.setMinimumSize(800, 600)
        self.resize(1000, 700)
        
        # Make floating like other OpenHCS windows
        self.setWindowFlags(Qt.WindowType.Dialog)
        
        self._setup_ui()
        self._load_metadata()
    
    def _setup_ui(self):
        """Setup the dialog UI."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(10)
        
        # Title label
        title_label = QLabel(f"<b>Plate:</b> {self.orchestrator.plate_path}")
        title_label.setWordWrap(True)
        layout.addWidget(title_label)
        
        # Scroll area for metadata form
        scroll_area = QScrollArea()
        scroll_area.setWidgetResizable(True)
        scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        
        # Container for the form
        self.form_container = QWidget()
        scroll_area.setWidget(self.form_container)
        layout.addWidget(scroll_area)
        
        # Button row
        button_layout = QHBoxLayout()
        button_layout.addStretch()
        
        close_button = QPushButton("Close")
        close_button.clicked.connect(self.accept)
        close_button.setMinimumWidth(100)
        button_layout.addWidget(close_button)
        
        layout.addLayout(button_layout)
    
    def _load_metadata(self):
        """Load and display metadata using generic reflection."""
        try:
            metadata_handler = self.orchestrator.microscope_handler.metadata_handler
            plate_path = self.orchestrator.plate_path

            # Check if this is OpenHCS format (has subdirectory-keyed metadata)
            if hasattr(metadata_handler, '_load_metadata_dict'):
                # OpenHCS format - read subdirectory-keyed metadata
                metadata_dict = metadata_handler._load_metadata_dict(plate_path)
                subdirs_dict = metadata_dict.get("subdirectories", {})

                if not subdirs_dict:
                    raise ValueError("No subdirectories found in metadata")

                # Create metadata instance based on number of subdirectories
                if len(subdirs_dict) == 1:
                    # Single subdirectory - show OpenHCSMetadata directly
                    subdir_name = next(iter(subdirs_dict.keys()))
                    subdir_data = subdirs_dict[subdir_name]
                    metadata_instance = OpenHCSMetadata(**subdir_data)
                    window_title = f"Metadata - {subdir_name}"
                    self._create_single_metadata_form(metadata_instance)
                else:
                    # Multiple subdirectories - manually create forms for each
                    # ParameterFormManager can't handle Dict[str, dataclass], so we create forms manually
                    subdirs_instances = {
                        name: OpenHCSMetadata(**data)
                        for name, data in subdirs_dict.items()
                    }
                    window_title = f"Metadata - {len(subdirs_dict)} subdirectories"
                    self._create_multi_subdirectory_forms(subdirs_instances)
            else:
                # Other microscope formats - build metadata from handler methods
                # Use parse_metadata() to get component mappings
                component_metadata = metadata_handler.parse_metadata(plate_path)

                # Get basic metadata using handler methods
                grid_dims = metadata_handler._get_with_fallback('get_grid_dimensions', plate_path)
                pixel_size = metadata_handler._get_with_fallback('get_pixel_size', plate_path)

                # Build OpenHCSMetadata structure
                # Note: For non-OpenHCS formats, we don't have image_files list or available_backends
                metadata_instance = OpenHCSMetadata(
                    microscope_handler_name=self.orchestrator.microscope_handler.microscope_type,
                    source_filename_parser_name=self.orchestrator.microscope_handler.parser.__class__.__name__,
                    grid_dimensions=list(grid_dims) if grid_dims else [1, 1],
                    pixel_size=pixel_size if pixel_size else 1.0,
                    image_files=[],  # Not available for non-OpenHCS formats
                    channels=component_metadata.get('channel'),
                    wells=component_metadata.get('well'),
                    sites=component_metadata.get('site'),
                    z_indexes=component_metadata.get('z_index'),
                    timepoints=component_metadata.get('timepoint'),  # Add missing timepoints
                    available_backends={'disk': True},  # Assume disk backend
                    main=None
                )
                window_title = f"Metadata - {self.orchestrator.microscope_handler.microscope_type}"
                self._create_single_metadata_form(metadata_instance)

            # Update window title
            self.setWindowTitle(f"{window_title} - {self.orchestrator.plate_path.name}")
            
            logger.info(f"Loaded metadata for {self.orchestrator.plate_path}")
            
        except Exception as e:
            logger.error(f"Failed to load metadata: {e}", exc_info=True)
            
            # Show error in form container
            error_layout = QVBoxLayout(self.form_container)
            error_label = QLabel(f"<b>Error loading metadata:</b><br>{str(e)}")
            error_label.setWordWrap(True)
            error_label.setStyleSheet("color: red; padding: 10px;")
            error_layout.addWidget(error_label)
            error_layout.addStretch()

    def _create_single_metadata_form(self, metadata_instance: OpenHCSMetadata):
        """Create a single metadata form for one OpenHCSMetadata instance."""
        form_layout = QVBoxLayout(self.form_container)
        form_layout.setContentsMargins(5, 5, 5, 5)

        # Create ParameterFormManager with the metadata instance in read-only mode
        metadata_form = ParameterFormManager(
            object_instance=metadata_instance,
            field_id="metadata_viewer",
            parent=self.form_container,
            read_only=True
        )

        form_layout.addWidget(metadata_form)
        form_layout.addStretch()

    def _create_multi_subdirectory_forms(self, subdirs_instances: dict):
        """Create separate forms for each subdirectory in multi-subdirectory plates."""
        form_layout = QVBoxLayout(self.form_container)
        form_layout.setContentsMargins(5, 5, 5, 5)

        cs = self.color_scheme

        # Create a collapsible group for each subdirectory
        for subdir_name, metadata_instance in subdirs_instances.items():
            # Create group box for this subdirectory
            group_box = QGroupBox(f"Subdirectory: {subdir_name}")
            group_box.setStyleSheet(f"""
                QGroupBox {{
                    font-weight: bold;
                    border: 1px solid {cs.to_hex(cs.border_color)};
                    border-radius: 5px;
                    margin-top: 10px;
                    padding-top: 10px;
                    background-color: {cs.to_hex(cs.panel_bg)};
                    color: {cs.to_hex(cs.text_primary)};
                }}
                QGroupBox::title {{
                    subcontrol-origin: margin;
                    left: 10px;
                    padding: 0 5px 0 5px;
                    color: {cs.to_hex(cs.text_accent)};
                }}
            """)

            group_layout = QVBoxLayout(group_box)
            group_layout.setContentsMargins(10, 10, 10, 10)

            # Create ParameterFormManager for this subdirectory's metadata in read-only mode
            metadata_form = ParameterFormManager(
                object_instance=metadata_instance,
                field_id=f"metadata_viewer_{subdir_name}",
                parent=group_box,
                read_only=True
            )

            group_layout.addWidget(metadata_form)
            form_layout.addWidget(group_box)

        form_layout.addStretch()

