"""
Well Selector Dialog - Simple dialog for selecting wells from a plate view.

Allows users to visually select wells from a plate grid and returns the selection
as a formatted string suitable for well_filter configuration.
"""

import logging
from typing import Optional, Set
from PyQt6.QtWidgets import QDialog, QVBoxLayout, QHBoxLayout, QPushButton, QLabel
from PyQt6.QtCore import Qt

from openhcs.pyqt_gui.widgets.shared.plate_view_widget import PlateViewWidget
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme

logger = logging.getLogger(__name__)


class WellSelectorDialog(QDialog):
    """
    Dialog for selecting wells using a visual plate grid.
    
    Features:
    - Visual plate grid with clickable wells
    - OK/Cancel buttons
    - Returns selected wells as a formatted string
    """
    
    def __init__(self, orchestrator, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        """
        Initialize well selector dialog.
        
        Args:
            orchestrator: PipelineOrchestrator instance to get available wells
            color_scheme: Color scheme for styling
            parent: Parent widget
        """
        super().__init__(parent)
        self.orchestrator = orchestrator
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.selected_wells = set()
        
        self.setWindowTitle("Select Wells")
        self.setMinimumSize(600, 500)
        self.resize(700, 600)
        
        # Make modal
        self.setModal(True)
        
        self._setup_ui()
        self._populate_wells()
    
    def _setup_ui(self):
        """Set up the dialog UI."""
        layout = QVBoxLayout(self)
        layout.setSpacing(10)
        layout.setContentsMargins(10, 10, 10, 10)
        
        # Title label
        title = QLabel("Click wells to select/deselect. Use Ctrl+Click for multi-select.")
        title.setWordWrap(True)
        layout.addWidget(title)
        
        # Plate view widget
        self.plate_view = PlateViewWidget(color_scheme=self.color_scheme, parent=self)
        self.plate_view.wells_selected.connect(self._on_wells_selected)
        layout.addWidget(self.plate_view)
        
        # Button row
        button_layout = QHBoxLayout()
        button_layout.addStretch()
        
        # Clear button
        clear_btn = QPushButton("Clear Selection")
        clear_btn.clicked.connect(self.plate_view.clear_selection)
        button_layout.addWidget(clear_btn)
        
        # Cancel button
        cancel_btn = QPushButton("Cancel")
        cancel_btn.clicked.connect(self.reject)
        button_layout.addWidget(cancel_btn)
        
        # OK button
        ok_btn = QPushButton("OK")
        ok_btn.setDefault(True)
        ok_btn.clicked.connect(self.accept)
        button_layout.addWidget(ok_btn)
        
        layout.addLayout(button_layout)
    
    def _populate_wells(self):
        """Populate plate view with available wells from orchestrator."""
        try:
            from openhcs.constants import MULTIPROCESSING_AXIS
            
            # Get available wells from orchestrator
            available_wells = self.orchestrator.get_component_keys(MULTIPROCESSING_AXIS)
            
            if not available_wells:
                logger.warning("No wells found in orchestrator")
                return
            
            # Convert to set for plate view
            well_set = set(available_wells)
            
            # Set available wells in plate view
            # The plate view will auto-detect dimensions from well IDs
            self.plate_view.set_available_wells(well_set)
            
            logger.debug(f"Populated well selector with {len(available_wells)} wells")
            
        except Exception as e:
            logger.error(f"Failed to populate wells: {e}", exc_info=True)
    
    def _on_wells_selected(self, wells: Set[str]):
        """Handle well selection changes."""
        self.selected_wells = wells
    
    def get_selected_wells_string(self) -> str:
        """
        Get selected wells as a formatted string.
        
        Returns:
            String representation of selected wells, e.g., "['A01', 'B02', 'C03']"
            Returns empty string if no wells selected.
        """
        if not self.selected_wells:
            return ""
        
        # Sort wells for consistent output
        sorted_wells = sorted(list(self.selected_wells))
        
        # Format as Python list literal string
        return str(sorted_wells)

