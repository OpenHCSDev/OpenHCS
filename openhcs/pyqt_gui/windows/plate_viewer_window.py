"""
Plate Viewer Window - Tabbed interface for Image Browser and Metadata Viewer.

Combines image browsing and metadata viewing in a single window with tabs.
"""

import logging
from typing import Optional
from pathlib import Path

from PyQt6.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QPushButton,
    QTabWidget, QWidget, QLabel
)
from PyQt6.QtCore import Qt
from PyQt6.QtGui import QFont

from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator

logger = logging.getLogger(__name__)


class PlateViewerWindow(QDialog):
    """
    Tabbed window for viewing plate images and metadata.
    
    Combines:
    - Image Browser (tab 1): Browse and view images in Napari
    - Metadata Viewer (tab 2): View plate metadata
    """
    
    def __init__(self, orchestrator, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        """
        Initialize plate viewer window.
        
        Args:
            orchestrator: PipelineOrchestrator instance
            color_scheme: Color scheme for styling
            parent: Parent widget
        """
        super().__init__(parent)
        self.orchestrator = orchestrator
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.style_gen = StyleSheetGenerator(self.color_scheme)
        
        plate_name = orchestrator.plate_path.name if orchestrator else "Unknown"
        self.setWindowTitle(f"Plate Viewer - {plate_name}")
        self.setMinimumSize(1200, 800)
        self.resize(1400, 900)
        
        # Make floating window
        self.setWindowFlags(Qt.WindowType.Dialog)
        
        self._setup_ui()
    
    def _setup_ui(self):
        """Setup the window UI."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(10)
        
        # Header
        header_layout = QHBoxLayout()

        # Show plate name with full path in parentheses, with elision
        if self.orchestrator:
            plate_name = self.orchestrator.plate_path.name
            full_path = str(self.orchestrator.plate_path)
            title_text = f"Plate: {plate_name} ({full_path})"
        else:
            title_text = "Plate: Unknown"

        title_label = QLabel(title_text)
        title_label.setFont(QFont("Arial", 12, QFont.Weight.Bold))
        title_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};")
        title_label.setWordWrap(False)  # Single line
        title_label.setTextFormat(Qt.TextFormat.PlainText)
        title_label.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)  # Allow copying
        # Enable elision (text will be cut with ... when too long)
        from PyQt6.QtWidgets import QSizePolicy
        title_label.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Preferred)
        header_layout.addWidget(title_label, 1)  # Stretch to fill available space
        
        header_layout.addStretch()
        
        # Close button
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(self.accept)
        close_btn.setStyleSheet(self.style_gen.generate_button_style())
        header_layout.addWidget(close_btn)
        
        layout.addLayout(header_layout)
        
        # Tab widget
        self.tab_widget = QTabWidget()
        # Use inline style (same pattern as dual_editor_window)
        self.tab_widget.setStyleSheet(f"""
            QTabWidget::pane {{
                border: none;
                background-color: {self.color_scheme.to_hex(self.color_scheme.panel_bg)};
            }}
            QTabBar::tab {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.input_bg)};
                color: white;
                padding: 8px 16px;
                margin-right: 2px;
                border-top-left-radius: 4px;
                border-top-right-radius: 4px;
                border: none;
            }}
            QTabBar::tab:selected {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.selection_bg)};
            }}
            QTabBar::tab:hover {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.button_hover_bg)};
            }}
        """)
        
        # Tab 1: Image Browser
        self.image_browser_tab = self._create_image_browser_tab()
        self.tab_widget.addTab(self.image_browser_tab, "Image Browser")
        
        # Tab 2: Metadata Viewer
        self.metadata_viewer_tab = self._create_metadata_viewer_tab()
        self.tab_widget.addTab(self.metadata_viewer_tab, "Metadata")
        
        layout.addWidget(self.tab_widget)
    
    def _create_image_browser_tab(self) -> QWidget:
        """Create the image browser tab."""
        from openhcs.pyqt_gui.widgets.image_browser import ImageBrowserWidget
        
        # Create image browser widget
        browser = ImageBrowserWidget(
            orchestrator=self.orchestrator,
            color_scheme=self.color_scheme,
            parent=self
        )
        
        # Store reference
        self.image_browser = browser
        
        return browser
    
    def _create_metadata_viewer_tab(self) -> QWidget:
        """Create the metadata viewer tab."""
        # Create scroll area for metadata content
        from PyQt6.QtWidgets import QScrollArea
        scroll_area = QScrollArea()
        scroll_area.setWidgetResizable(True)
        scroll_area.setFrameShape(QScrollArea.Shape.NoFrame)

        # Container for metadata forms
        container = QWidget()
        layout = QVBoxLayout(container)
        layout.setContentsMargins(5, 5, 5, 5)

        # Load metadata using the same logic as MetadataViewerDialog
        try:
            metadata_handler = self.orchestrator.microscope_handler.metadata_handler
            plate_path = self.orchestrator.plate_path
            
            # Check if this is OpenHCS format
            if hasattr(metadata_handler, '_load_metadata_dict'):
                # OpenHCS format
                from openhcs.microscopes.openhcs import OpenHCSMetadata
                metadata_dict = metadata_handler._load_metadata_dict(plate_path)
                subdirs_dict = metadata_dict.get("subdirectories", {})

                if not subdirs_dict:
                    raise ValueError("No subdirectories found in metadata")

                # Convert raw dicts to OpenHCSMetadata instances
                subdirs_instances = {}
                for subdir_name, subdir_data in subdirs_dict.items():
                    # Create OpenHCSMetadata from the subdirectory data
                    subdirs_instances[subdir_name] = OpenHCSMetadata(**subdir_data)

                # Create forms for each subdirectory
                self._create_multi_subdirectory_forms(layout, subdirs_instances)
            else:
                # Other microscope formats (ImageXpress, Opera Phenix, etc.)
                from openhcs.microscopes.openhcs import OpenHCSMetadata
                component_metadata = metadata_handler.parse_metadata(plate_path)

                # Get image files list (all handlers have this method)
                image_files = metadata_handler.get_image_files(plate_path)

                # Get optional metadata with fallback
                grid_dims = metadata_handler._get_with_fallback('get_grid_dimensions', plate_path)
                pixel_size = metadata_handler._get_with_fallback('get_pixel_size', plate_path)

                metadata_instance = OpenHCSMetadata(
                    microscope_handler_name=self.orchestrator.microscope_handler.microscope_type,
                    source_filename_parser_name=self.orchestrator.microscope_handler.parser.__class__.__name__,
                    grid_dimensions=list(grid_dims) if grid_dims else [1, 1],
                    pixel_size=pixel_size if pixel_size else 1.0,
                    image_files=image_files,  # Now populated!
                    channels=component_metadata.get('channel'),
                    wells=component_metadata.get('well'),
                    sites=component_metadata.get('site'),
                    z_indexes=component_metadata.get('z_index'),
                    available_backends={'disk': True},
                    main=None
                )

                self._create_single_metadata_form(layout, metadata_instance)
            
        except Exception as e:
            logger.error(f"Failed to load metadata: {e}", exc_info=True)
            error_label = QLabel(f"<b>Error loading metadata:</b><br>{str(e)}")
            error_label.setWordWrap(True)
            error_label.setStyleSheet("color: red; padding: 10px;")
            layout.addWidget(error_label)

        layout.addStretch()

        # Set container as scroll area widget
        scroll_area.setWidget(container)
        return scroll_area
    
    def _create_single_metadata_form(self, layout, metadata_instance):
        """Create a single metadata form."""
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

        metadata_form = ParameterFormManager(
            object_instance=metadata_instance,
            field_id="metadata_viewer",
            parent=None
        )
        self._make_form_readonly(metadata_form)
        layout.addWidget(metadata_form)
    
    def _create_multi_subdirectory_forms(self, layout, subdirs_instances):
        """Create forms for multiple subdirectories."""
        from PyQt6.QtWidgets import QGroupBox, QScrollArea
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        
        for subdir_name, metadata_instance in subdirs_instances.items():
            group_box = QGroupBox(f"Subdirectory: {subdir_name}")
            group_layout = QVBoxLayout(group_box)
            
            metadata_form = ParameterFormManager(
                object_instance=metadata_instance,
                field_id=f"metadata_{subdir_name}",
                parent=None
            )
            self._make_form_readonly(metadata_form)
            group_layout.addWidget(metadata_form)

            layout.addWidget(group_box)

    def _make_form_readonly(self, form_widget):
        """Make all input widgets in a form read-only without greying them out."""
        from PyQt6.QtWidgets import QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox, QCheckBox, QTextEdit, QAbstractSpinBox

        # Find all input widgets and make them read-only
        for widget in form_widget.findChildren(QWidget):
            if isinstance(widget, (QLineEdit, QTextEdit)):
                widget.setReadOnly(True)
                # Keep normal appearance
                widget.setStyleSheet("")
            elif isinstance(widget, (QSpinBox, QDoubleSpinBox)):
                widget.setReadOnly(True)
                widget.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.NoButtons)
            elif isinstance(widget, QComboBox):
                # Disable interaction but keep normal appearance
                widget.setEnabled(False)
                widget.setStyleSheet("QComboBox:disabled { color: white; background-color: #2b2b2b; }")
            elif isinstance(widget, QCheckBox):
                # Make checkbox non-interactive but keep normal appearance
                widget.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
                widget.setFocusPolicy(Qt.FocusPolicy.NoFocus)
    
    def cleanup(self):
        """Clean up resources."""
        if hasattr(self, 'image_browser'):
            self.image_browser.cleanup()

