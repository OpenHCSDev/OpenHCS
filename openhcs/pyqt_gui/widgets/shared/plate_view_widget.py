"""
Plate View Widget - Visual grid representation of plate wells.

Displays a clickable grid of wells (e.g., A01-H12 for 96-well plate) with visual
states for empty/has-images/selected. Supports multi-select and subdirectory selection.
"""

import logging
from typing import Set, List, Optional, Tuple
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QGridLayout, QPushButton,
    QLabel, QFrame, QButtonGroup
)
from PyQt6.QtCore import Qt, pyqtSignal
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator

logger = logging.getLogger(__name__)


class PlateViewWidget(QWidget):
    """
    Visual plate grid widget with clickable wells.

    Features:
    - Auto-detects plate dimensions from well IDs
    - Clickable well buttons with visual states (empty/has-images/selected)
    - Multi-select support (Ctrl+Click, Shift+Click)
    - Subdirectory selector for multiple plate outputs
    - Clear selection button
    - Detachable to external window

    Signals:
        wells_selected: Emitted when well selection changes (set of well IDs)
        detach_requested: Emitted when user clicks detach button
    """

    wells_selected = pyqtSignal(set)
    detach_requested = pyqtSignal()
    
    def __init__(self, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        super().__init__(parent)
        
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.style_gen = StyleSheetGenerator(self.color_scheme)
        
        # State
        self.well_buttons = {}  # well_id -> QPushButton
        self.wells_with_images = set()  # Set of well IDs that have images
        self.selected_wells = set()  # Currently selected wells
        self.plate_dimensions = (8, 12)  # rows, cols (default 96-well)
        self.subdirs = []  # List of subdirectory names
        self.active_subdir = None  # Currently selected subdirectory
        self.coord_to_well = {}  # (row_index, col_index) -> well_id mapping
        self.well_to_coord = {}  # well_id -> (row_index, col_index) reverse mapping

        # Drag selection state
        self.is_dragging = False
        self.drag_start_well = None
        self.drag_current_well = None
        self.drag_selection_mode = None  # 'select' or 'deselect'
        self.drag_affected_wells = set()  # Wells affected by current drag operation
        self.pre_drag_selection = set()  # Selection state before drag started

        # Column filter sync
        self.well_filter_widget = None  # Reference to ColumnFilterWidget for 'well' column

        # UI components
        self.subdir_buttons = {}  # subdir_name -> QPushButton
        self.subdir_button_group = None
        self.well_grid_layout = None
        self.status_label = None
        
        self._setup_ui()
    
    def _setup_ui(self):
        """Setup the UI layout."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(5, 5, 5, 5)
        layout.setSpacing(5)
        
        # Header with title, detach button, and clear button
        header_layout = QHBoxLayout()
        title_label = QLabel("Plate View")
        title_label.setStyleSheet(f"font-weight: bold; color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};")
        header_layout.addWidget(title_label)

        header_layout.addStretch()

        detach_btn = QPushButton("↗")
        detach_btn.setToolTip("Detach to separate window")
        detach_btn.setFixedWidth(30)
        detach_btn.setStyleSheet(self.style_gen.generate_button_style())
        detach_btn.clicked.connect(lambda: self.detach_requested.emit())
        header_layout.addWidget(detach_btn)

        clear_btn = QPushButton("Clear Selection")
        clear_btn.setStyleSheet(self.style_gen.generate_button_style())
        clear_btn.clicked.connect(self.clear_selection)
        header_layout.addWidget(clear_btn)

        layout.addLayout(header_layout)
        
        # Subdirectory selector (initially hidden)
        self.subdir_frame = QFrame()
        self.subdir_layout = QHBoxLayout(self.subdir_frame)
        self.subdir_layout.setContentsMargins(0, 0, 0, 0)
        self.subdir_layout.setSpacing(5)
        
        subdir_label = QLabel("Plate Output:")
        self.subdir_layout.addWidget(subdir_label)
        
        self.subdir_button_group = QButtonGroup(self)
        self.subdir_button_group.setExclusive(True)
        
        self.subdir_layout.addStretch()
        self.subdir_frame.setVisible(False)
        layout.addWidget(self.subdir_frame)
        
        # Well grid container
        grid_container = QFrame()
        grid_container.setStyleSheet(f"background-color: {self.color_scheme.to_hex(self.color_scheme.panel_bg)}; border-radius: 3px;")
        grid_layout_wrapper = QVBoxLayout(grid_container)
        grid_layout_wrapper.setContentsMargins(10, 10, 10, 10)

        # Create a centered widget for the grid
        grid_center_widget = QWidget()
        grid_center_layout = QHBoxLayout(grid_center_widget)
        grid_center_layout.setContentsMargins(0, 0, 0, 0)

        # Add stretches to center the grid
        grid_center_layout.addStretch()

        # Grid widget with mouse tracking for drag selection
        grid_widget = QWidget()
        grid_widget.setMouseTracking(True)
        self.well_grid_layout = QGridLayout(grid_widget)
        self.well_grid_layout.setSpacing(3)  # Slightly more spacing
        self.well_grid_layout.setContentsMargins(0, 0, 0, 0)
        self.grid_widget = grid_widget  # Store reference

        grid_center_layout.addWidget(grid_widget)
        grid_center_layout.addStretch()

        grid_layout_wrapper.addWidget(grid_center_widget)

        layout.addWidget(grid_container, 1)  # Stretch to fill
        
        # Status label
        self.status_label = QLabel("No wells")
        self.status_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_secondary)};")
        layout.addWidget(self.status_label)

        # Install event filter on grid widget for drag selection
        self.grid_widget.installEventFilter(self)
    
    def set_subdirectories(self, subdirs: List[str]):
        """
        Set available subdirectories for plate outputs.
        
        Args:
            subdirs: List of subdirectory names
        """
        self.subdirs = subdirs
        
        # Clear existing buttons
        for btn in self.subdir_buttons.values():
            self.subdir_button_group.removeButton(btn)
            btn.deleteLater()
        self.subdir_buttons.clear()
        
        if len(subdirs) == 0:
            # No subdirs, hide selector
            self.subdir_frame.setVisible(False)
            self.active_subdir = None
        elif len(subdirs) == 1:
            # Single subdir, auto-select and hide selector
            self.subdir_frame.setVisible(False)
            self.active_subdir = subdirs[0]
        else:
            # Multiple subdirs, show selector
            self.subdir_frame.setVisible(True)
            
            # Create button for each subdir
            for subdir in subdirs:
                btn = QPushButton(subdir)
                btn.setCheckable(True)
                btn.setStyleSheet(self.style_gen.generate_button_style())
                btn.clicked.connect(lambda checked, s=subdir: self._on_subdir_selected(s))
                
                self.subdir_button_group.addButton(btn)
                self.subdir_layout.insertWidget(self.subdir_layout.count() - 1, btn)  # Before stretch
                self.subdir_buttons[subdir] = btn
            
            # Auto-select first subdir
            if subdirs:
                first_btn = self.subdir_buttons[subdirs[0]]
                first_btn.setChecked(True)
                self.active_subdir = subdirs[0]
    
    def _on_subdir_selected(self, subdir: str):
        """Handle subdirectory selection."""
        self.active_subdir = subdir
        # Could emit signal here if needed for filtering by subdir
    
    def set_available_wells(self, well_ids: Set[str], plate_dimensions: Optional[Tuple[int, int]] = None,
                           coord_to_well: Optional[dict] = None):
        """
        Update which wells have images and rebuild grid.

        Args:
            well_ids: Set of well IDs that have images
            plate_dimensions: Optional (rows, cols) tuple. If None, auto-detects from well IDs.
            coord_to_well: Optional mapping from (row_index, col_index) to well_id.
                          Required for non-standard well ID formats (e.g., Opera Phenix R01C01).
        """
        self.wells_with_images = well_ids
        self.coord_to_well = coord_to_well or {}

        # Build reverse mapping (well_id -> coord)
        self.well_to_coord = {well_id: coord for coord, well_id in self.coord_to_well.items()}

        if not well_ids:
            self._clear_grid()
            self.status_label.setText("No wells")
            return

        # Use provided dimensions or auto-detect
        if plate_dimensions is not None:
            self.plate_dimensions = plate_dimensions
        else:
            self.plate_dimensions = self._detect_dimensions(well_ids)

        # Rebuild grid
        self._build_grid()

        # Update status
        self._update_status()
    
    def _detect_dimensions(self, well_ids: Set[str]) -> Tuple[int, int]:
        """
        Auto-detect plate dimensions from well IDs.
        
        Assumes well IDs are already parsed (e.g., 'A01', 'B03').
        Extracts max row letter and max column number.
        
        Args:
            well_ids: Set of well IDs
            
        Returns:
            (rows, cols) tuple
        """
        max_row = 0
        max_col = 0
        
        for well_id in well_ids:
            # Extract row letter(s) and column number(s)
            row_part = ''.join(c for c in well_id if c.isalpha())
            col_part = ''.join(c for c in well_id if c.isdigit())
            
            if row_part:
                # Convert row letter to index (A=1, B=2, AA=27, etc.)
                row_idx = sum((ord(c.upper()) - ord('A') + 1) * (26 ** i) 
                             for i, c in enumerate(reversed(row_part)))
                max_row = max(max_row, row_idx)
            
            if col_part:
                max_col = max(max_col, int(col_part))
        
        return (max_row, max_col)
    
    def _clear_grid(self):
        """Clear the well grid."""
        for btn in self.well_buttons.values():
            btn.deleteLater()
        self.well_buttons.clear()
        
        # Clear layout
        while self.well_grid_layout.count():
            item = self.well_grid_layout.takeAt(0)
            if item.widget():
                item.widget().deleteLater()
    
    def _build_grid(self):
        """Build the well grid based on current dimensions."""
        self._clear_grid()

        rows, cols = self.plate_dimensions

        # Add column headers (1, 2, 3, ...)
        for col in range(1, cols + 1):
            header = QLabel(str(col))
            header.setAlignment(Qt.AlignmentFlag.AlignCenter)
            header.setFixedSize(40, 20)  # Fixed size for consistent spacing
            header.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_secondary)}; font-size: 11px;")
            self.well_grid_layout.addWidget(header, 0, col)

        # Add row headers and well buttons
        for row in range(1, rows + 1):
            # Row header (A, B, C, ...)
            row_letter = self._index_to_row_letter(row)
            header = QLabel(row_letter)
            header.setAlignment(Qt.AlignmentFlag.AlignCenter)
            header.setFixedSize(20, 40)  # Fixed size for consistent spacing
            header.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_secondary)}; font-size: 11px;")
            self.well_grid_layout.addWidget(header, row, 0)

            # Well buttons
            for col in range(1, cols + 1):
                # Use coordinate mapping if available, otherwise construct standard well ID
                well_id = self.coord_to_well.get((row, col), f"{row_letter}{col:02d}")

                btn = QPushButton()
                btn.setFixedSize(40, 40)  # Larger buttons for better visibility
                btn.setCheckable(True)

                # Set initial state
                if well_id in self.wells_with_images:
                    btn.setEnabled(True)
                    btn.setStyleSheet(self._get_well_button_style('has_images'))
                else:
                    btn.setEnabled(False)
                    btn.setStyleSheet(self._get_well_button_style('empty'))

                btn.clicked.connect(lambda checked, wid=well_id: self._on_well_clicked(wid, checked))

                # Store well_id in button for lookup
                btn.setProperty('well_id', well_id)

                self.well_grid_layout.addWidget(btn, row, col)
                self.well_buttons[well_id] = btn

                # Update reverse mapping if not using coord_to_well
                if (row, col) not in self.coord_to_well:
                    self.well_to_coord[well_id] = (row, col)
    
    def _index_to_row_letter(self, index: int) -> str:
        """Convert row index to letter(s) (1=A, 2=B, 27=AA, etc.)."""
        result = ""
        while index > 0:
            index -= 1
            result = chr(ord('A') + (index % 26)) + result
            index //= 26
        return result
    
    def _get_well_button_style(self, state: str) -> str:
        """Generate style for well button based on state."""
        cs = self.color_scheme
        
        if state == 'empty':
            return f"""
                QPushButton {{
                    background-color: {cs.to_hex(cs.button_disabled_bg)};
                    color: {cs.to_hex(cs.button_disabled_text)};
                    border: none;
                    border-radius: 3px;
                }}
            """
        elif state == 'selected':
            return f"""
                QPushButton {{
                    background-color: {cs.to_hex(cs.selection_bg)};
                    color: {cs.to_hex(cs.selection_text)};
                    border: 2px solid {cs.to_hex(cs.border_color)};
                    border-radius: 3px;
                }}
            """
        else:  # has_images
            return f"""
                QPushButton {{
                    background-color: {cs.to_hex(cs.button_normal_bg)};
                    color: {cs.to_hex(cs.button_text)};
                    border: none;
                    border-radius: 3px;
                }}
                QPushButton:hover {{
                    background-color: {cs.to_hex(cs.button_hover_bg)};
                }}
            """
    
    def _on_well_clicked(self, well_id: str, checked: bool):
        """Handle well button click (only for non-drag clicks)."""
        # Skip if this was part of a drag operation
        if self.is_dragging:
            return

        if checked:
            self.selected_wells.add(well_id)
            self.well_buttons[well_id].setStyleSheet(self._get_well_button_style('selected'))
        else:
            self.selected_wells.discard(well_id)
            self.well_buttons[well_id].setStyleSheet(self._get_well_button_style('has_images'))

        self._update_status()
        self.wells_selected.emit(self.selected_wells.copy())
        self.sync_to_well_filter()
    
    def clear_selection(self, emit_signal: bool = True, sync_to_filter: bool = True):
        """
        Clear all selected wells.

        Args:
            emit_signal: Whether to emit wells_selected signal (default True)
            sync_to_filter: Whether to sync to well filter (default True)
        """
        for well_id in list(self.selected_wells):
            if well_id in self.well_buttons:
                btn = self.well_buttons[well_id]
                btn.setChecked(False)
                btn.setStyleSheet(self._get_well_button_style('has_images'))

        self.selected_wells.clear()
        self._update_status()

        if emit_signal:
            self.wells_selected.emit(set())

        if sync_to_filter:
            self.sync_to_well_filter()

    def select_wells(self, well_ids: Set[str], emit_signal: bool = True):
        """
        Programmatically select wells.

        Args:
            well_ids: Set of well IDs to select
            emit_signal: Whether to emit wells_selected signal (default True)
        """
        # Clear without syncing to filter (we'll sync after setting new selection)
        self.clear_selection(emit_signal=False, sync_to_filter=False)

        for well_id in well_ids:
            if well_id in self.well_buttons and well_id in self.wells_with_images:
                self.selected_wells.add(well_id)
                btn = self.well_buttons[well_id]
                btn.setChecked(True)
                btn.setStyleSheet(self._get_well_button_style('selected'))

        self._update_status()
        if emit_signal:
            self.wells_selected.emit(self.selected_wells.copy())
            self.sync_to_well_filter()
    
    def _update_status(self):
        """Update status label."""
        total_wells = len(self.wells_with_images)
        selected_count = len(self.selected_wells)

        if selected_count > 0:
            self.status_label.setText(
                f"{total_wells} wells have images | {selected_count} selected"
            )
        else:
            self.status_label.setText(f"{total_wells} wells have images")

    def eventFilter(self, obj, event):
        """Handle mouse events on grid widget for drag selection."""
        if obj != self.grid_widget:
            return super().eventFilter(obj, event)

        from PyQt6.QtCore import QEvent

        if event.type() == QEvent.Type.MouseButtonPress:
            if event.button() == Qt.MouseButton.LeftButton:
                # Find which button is under the cursor
                child = self.grid_widget.childAt(event.pos())
                if isinstance(child, QPushButton):
                    well_id = child.property('well_id')
                    if well_id and well_id in self.wells_with_images:
                        # Start drag selection - save current selection state
                        self.is_dragging = True
                        self.drag_start_well = well_id
                        self.drag_current_well = well_id
                        self.drag_affected_wells = set()
                        self.pre_drag_selection = self.selected_wells.copy()

                        # Determine selection mode
                        self.drag_selection_mode = 'deselect' if well_id in self.selected_wells else 'select'

                        # Apply to starting well
                        self._toggle_well_selection(well_id, self.drag_selection_mode == 'select')
                        self.drag_affected_wells.add(well_id)

                        # Emit signal immediately
                        self._update_status()
                        self.wells_selected.emit(self.selected_wells.copy())
                        self.sync_to_well_filter()

        elif event.type() == QEvent.Type.MouseMove:
            if self.is_dragging and event.buttons() & Qt.MouseButton.LeftButton:
                # Find which button is under the cursor
                child = self.grid_widget.childAt(event.pos())
                if isinstance(child, QPushButton):
                    well_id = child.property('well_id')
                    if well_id and well_id in self.wells_with_images:
                        if well_id != self.drag_current_well:
                            self.drag_current_well = well_id
                            self._update_drag_selection()

        elif event.type() == QEvent.Type.MouseButtonRelease:
            if event.button() == Qt.MouseButton.LeftButton and self.is_dragging:
                # End drag selection
                self.is_dragging = False
                self.drag_start_well = None
                self.drag_current_well = None
                self.drag_selection_mode = None
                self.drag_affected_wells.clear()

        return super().eventFilter(obj, event)

    def _toggle_well_selection(self, well_id: str, select: bool):
        """Toggle selection state of a single well."""
        if well_id not in self.well_buttons or well_id not in self.wells_with_images:
            return

        btn = self.well_buttons[well_id]

        if select and well_id not in self.selected_wells:
            self.selected_wells.add(well_id)
            btn.setChecked(True)
            btn.setStyleSheet(self._get_well_button_style('selected'))
        elif not select and well_id in self.selected_wells:
            self.selected_wells.discard(well_id)
            btn.setChecked(False)
            btn.setStyleSheet(self._get_well_button_style('has_images'))

    def _update_drag_selection(self):
        """Update selection for all wells in the drag rectangle."""
        if not self.drag_start_well or not self.drag_current_well:
            return

        # Get coordinates
        start_coord = self.well_to_coord.get(self.drag_start_well)
        current_coord = self.well_to_coord.get(self.drag_current_well)

        if not start_coord or not current_coord:
            return

        # Calculate rectangle bounds
        min_row = min(start_coord[0], current_coord[0])
        max_row = max(start_coord[0], current_coord[0])
        min_col = min(start_coord[1], current_coord[1])
        max_col = max(start_coord[1], current_coord[1])

        # Find all wells in current rectangle
        wells_in_rectangle = set()
        for row in range(min_row, max_row + 1):
            for col in range(min_col, max_col + 1):
                well_id = self.coord_to_well.get((row, col))
                if well_id and well_id in self.wells_with_images:
                    wells_in_rectangle.add(well_id)

        # Revert wells that were affected by previous drag but are no longer in rectangle
        # Restore them to their pre-drag state
        wells_to_revert = self.drag_affected_wells - wells_in_rectangle
        for well_id in wells_to_revert:
            was_selected_before_drag = well_id in self.pre_drag_selection
            self._toggle_well_selection(well_id, was_selected_before_drag)

        # Apply selection to all wells in current rectangle
        for well_id in wells_in_rectangle:
            self._toggle_well_selection(well_id, self.drag_selection_mode == 'select')

        # Update affected wells to current rectangle
        self.drag_affected_wells = wells_in_rectangle.copy()

        # Emit signal and sync to well filter
        self._update_status()
        self.wells_selected.emit(self.selected_wells.copy())
        self.sync_to_well_filter()

    def set_well_filter_widget(self, well_filter_widget):
        """
        Set reference to the well column filter widget for bidirectional sync.

        Args:
            well_filter_widget: ColumnFilterWidget instance for the 'well' column
        """
        self.well_filter_widget = well_filter_widget

    def sync_to_well_filter(self):
        """Sync current plate view selection to well filter checkboxes."""
        if not self.well_filter_widget:
            return

        # Update well filter checkboxes to match plate view selection
        # Block signals to prevent circular sync loop
        # If no wells selected in plate view, select all in filter (show all)
        if self.selected_wells:
            self.well_filter_widget.set_selected_values(self.selected_wells, block_signals=True)
        else:
            self.well_filter_widget.select_all(block_signals=True)

    def sync_from_well_filter(self):
        """Sync well filter checkbox selection to plate view."""
        if not self.well_filter_widget:
            return

        # Get selected wells from filter
        selected_in_filter = self.well_filter_widget.get_selected_values()

        # Update plate view to match (without emitting signal to avoid loop)
        self.select_wells(selected_in_filter, emit_signal=False)

