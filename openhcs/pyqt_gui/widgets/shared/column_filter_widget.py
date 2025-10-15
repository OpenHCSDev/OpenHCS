"""
Column filter widget with checkboxes for unique values.

Provides Excel-like column filtering with checkboxes for each unique value.
Multiple columns can be filtered simultaneously with AND logic across columns.
"""

import logging
from typing import Dict, Set, List, Optional, Callable

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QCheckBox, QPushButton,
    QScrollArea, QLabel, QFrame, QSplitter
)
from PyQt6.QtCore import pyqtSignal, Qt

from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.widgets.shared.layout_constants import COMPACT_LAYOUT

logger = logging.getLogger(__name__)


class ColumnFilterWidget(QFrame):
    """
    Filter widget for a single column showing checkboxes for unique values.
    Uses compact styling matching parameter form manager.

    Signals:
        filter_changed: Emitted when filter selection changes
    """

    filter_changed = pyqtSignal()

    def __init__(self, column_name: str, unique_values: List[str],
                 color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        """
        Initialize column filter widget.

        Args:
            column_name: Name of the column being filtered
            unique_values: List of unique values in this column
            color_scheme: Color scheme for styling
            parent: Parent widget
        """
        super().__init__(parent)
        self.column_name = column_name
        self.unique_values = sorted(unique_values)  # Sort for consistent display
        self.checkboxes: Dict[str, QCheckBox] = {}
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.style_gen = StyleSheetGenerator(self.color_scheme)

        # Minimal styling - no frame, no borders
        self.setFrameStyle(QFrame.Shape.NoFrame)

        self._init_ui()
    
    def _init_ui(self):
        """Initialize the UI with minimal spacing."""
        from PyQt6.QtWidgets import QSizePolicy

        layout = QVBoxLayout(self)
        layout.setContentsMargins(2, 2, 2, 2)
        layout.setSpacing(2)

        # Header: Column title on left, buttons on right (same row)
        header_layout = QHBoxLayout()
        header_layout.setContentsMargins(0, 0, 0, 0)
        header_layout.setSpacing(4)

        # Column title label (bold, accent color, minimal)
        title_label = QLabel(self.column_name)
        title_label.setStyleSheet(f"""
            QLabel {{
                font-weight: bold;
                color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};
            }}
        """)
        header_layout.addWidget(title_label)

        header_layout.addStretch()

        # All/None buttons (minimal)
        select_all_btn = QPushButton("All")
        select_all_btn.setMaximumWidth(30)
        select_all_btn.clicked.connect(self.select_all)
        header_layout.addWidget(select_all_btn)

        select_none_btn = QPushButton("None")
        select_none_btn.setMaximumWidth(35)
        select_none_btn.clicked.connect(self.select_none)
        header_layout.addWidget(select_none_btn)

        layout.addLayout(header_layout)

        # Scrollable checkbox list - CRITICAL: proper size policy for splitter
        scroll_area = QScrollArea()
        scroll_area.setWidgetResizable(True)
        scroll_area.setMinimumHeight(40)
        scroll_area.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Expanding)
        scroll_area.setFrameShape(QFrame.Shape.NoFrame)

        checkbox_container = QWidget()
        checkbox_layout = QVBoxLayout(checkbox_container)
        checkbox_layout.setContentsMargins(0, 0, 0, 0)
        checkbox_layout.setSpacing(0)

        # Create checkbox for each unique value (minimal styling)
        for value in self.unique_values:
            checkbox = QCheckBox(str(value))
            checkbox.setChecked(True)  # Start with all selected
            checkbox.stateChanged.connect(self._on_checkbox_changed)
            self.checkboxes[value] = checkbox
            checkbox_layout.addWidget(checkbox)

        checkbox_layout.addStretch()
        scroll_area.setWidget(checkbox_container)
        layout.addWidget(scroll_area, 1)  # Stretch factor 1 for resizing

        # Count label (minimal)
        self.count_label = QLabel()
        self.count_label.setStyleSheet(f"""
            QLabel {{
                font-size: 9px;
                color: {self.color_scheme.to_hex(self.color_scheme.text_disabled)};
            }}
        """)
        self._update_count_label()
        layout.addWidget(self.count_label)
    
    def _on_checkbox_changed(self):
        """Handle checkbox state change."""
        self._update_count_label()
        self.filter_changed.emit()
    
    def _update_count_label(self):
        """Update the count label showing selected/total."""
        selected_count = len(self.get_selected_values())
        total_count = len(self.unique_values)
        self.count_label.setText(f"{selected_count}/{total_count} selected")
    
    def select_all(self):
        """Select all checkboxes."""
        for checkbox in self.checkboxes.values():
            checkbox.setChecked(True)
    
    def select_none(self):
        """Deselect all checkboxes."""
        for checkbox in self.checkboxes.values():
            checkbox.setChecked(False)
    
    def get_selected_values(self) -> Set[str]:
        """Get set of selected values."""
        return {value for value, checkbox in self.checkboxes.items() if checkbox.isChecked()}
    
    def set_selected_values(self, values: Set[str]):
        """Set which values are selected."""
        for value, checkbox in self.checkboxes.items():
            checkbox.setChecked(value in values)


class MultiColumnFilterPanel(QWidget):
    """
    Panel containing filters for multiple columns with resizable splitters.

    Provides column-based filtering with AND logic across columns.
    Each filter can be resized independently using vertical splitters.

    Signals:
        filters_changed: Emitted when any filter changes
    """

    filters_changed = pyqtSignal()

    def __init__(self, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        """Initialize multi-column filter panel."""
        super().__init__(parent)
        self.column_filters: Dict[str, ColumnFilterWidget] = {}
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self._init_ui()

    def _init_ui(self):
        """Initialize the UI with vertical splitter for resizable filters."""
        from PyQt6.QtWidgets import QSizePolicy

        # Use vertical splitter so each filter can be resized
        self.splitter = QSplitter(Qt.Orientation.Vertical)
        self.splitter.setChildrenCollapsible(False)  # Prevent filters from collapsing
        self.splitter.setHandleWidth(3)  # Thinner splitter handle

        # CRITICAL: Proper size policy for splitter to work correctly
        self.splitter.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Expanding)

        main_layout = QVBoxLayout(self)
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)
        main_layout.addWidget(self.splitter)
    
    def add_column_filter(self, column_name: str, unique_values: List[str]):
        """
        Add a filter for a column.

        Args:
            column_name: Name of the column
            unique_values: List of unique values in this column
        """
        from PyQt6.QtWidgets import QSizePolicy

        if column_name in self.column_filters:
            # Remove existing filter
            self.remove_column_filter(column_name)

        # Create filter widget with color scheme
        filter_widget = ColumnFilterWidget(column_name, unique_values, self.color_scheme)
        filter_widget.filter_changed.connect(self._on_filter_changed)

        # CRITICAL: Set size policy for proper splitter behavior
        filter_widget.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Expanding)

        # Add to splitter (each filter is independently resizable)
        self.splitter.addWidget(filter_widget)

        # Set initial stretch factor (equal for all filters)
        index = self.splitter.indexOf(filter_widget)
        self.splitter.setStretchFactor(index, 1)

        self.column_filters[column_name] = filter_widget
    
    def remove_column_filter(self, column_name: str):
        """Remove a column filter."""
        if column_name in self.column_filters:
            widget = self.column_filters[column_name]
            # Remove from splitter
            widget.setParent(None)
            widget.deleteLater()
            del self.column_filters[column_name]
    
    def clear_all_filters(self):
        """Remove all column filters."""
        for column_name in list(self.column_filters.keys()):
            self.remove_column_filter(column_name)
    
    def _on_filter_changed(self):
        """Handle filter change from any column."""
        self.filters_changed.emit()
    
    def get_active_filters(self) -> Dict[str, Set[str]]:
        """
        Get active filters for all columns.
        
        Returns:
            Dictionary mapping column name to set of selected values.
            Only includes columns where not all values are selected.
        """
        active_filters = {}
        for column_name, filter_widget in self.column_filters.items():
            selected = filter_widget.get_selected_values()
            # Only include if not all values are selected (i.e., actually filtering)
            if len(selected) < len(filter_widget.unique_values):
                active_filters[column_name] = selected
        return active_filters
    
    def apply_filters(self, data: List[Dict], column_key_map: Optional[Dict[str, str]] = None) -> List[Dict]:
        """
        Apply filters to a list of data dictionaries.
        
        Args:
            data: List of dictionaries to filter
            column_key_map: Optional mapping from display column names to data keys
                           (e.g., {"Well": "well", "Channel": "channel"})
        
        Returns:
            Filtered list of dictionaries
        """
        active_filters = self.get_active_filters()
        
        if not active_filters:
            return data  # No filters active
        
        # Map column names to data keys
        if column_key_map is None:
            column_key_map = {name: name.lower().replace(' ', '_') for name in active_filters.keys()}
        
        # Filter data with AND logic across columns
        filtered_data = []
        for item in data:
            matches = True
            for column_name, selected_values in active_filters.items():
                data_key = column_key_map.get(column_name, column_name)
                item_value = str(item.get(data_key, ''))
                if item_value not in selected_values:
                    matches = False
                    break
            if matches:
                filtered_data.append(item)
        
        return filtered_data
    
    def reset_all_filters(self):
        """Reset all filters to select all values."""
        for filter_widget in self.column_filters.values():
            filter_widget.select_all()

