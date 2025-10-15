"""
Column filter widget with checkboxes for unique values.

Provides Excel-like column filtering with checkboxes for each unique value.
Multiple columns can be filtered simultaneously with AND logic across columns.
"""

import logging
from typing import Dict, Set, List, Optional, Callable

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QCheckBox, QPushButton,
    QScrollArea, QLabel, QFrame
)
from PyQt6.QtCore import pyqtSignal, Qt

logger = logging.getLogger(__name__)


class ColumnFilterWidget(QWidget):
    """
    Filter widget for a single column showing checkboxes for unique values.
    
    Signals:
        filter_changed: Emitted when filter selection changes
    """
    
    filter_changed = pyqtSignal()
    
    def __init__(self, column_name: str, unique_values: List[str], parent=None):
        """
        Initialize column filter widget.
        
        Args:
            column_name: Name of the column being filtered
            unique_values: List of unique values in this column
            parent: Parent widget
        """
        super().__init__(parent)
        self.column_name = column_name
        self.unique_values = sorted(unique_values)  # Sort for consistent display
        self.checkboxes: Dict[str, QCheckBox] = {}
        
        self._init_ui()
    
    def _init_ui(self):
        """Initialize the UI."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(3, 3, 3, 3)
        layout.setSpacing(3)

        # Header with select all/none buttons
        header_layout = QHBoxLayout()

        select_all_btn = QPushButton("All")
        select_all_btn.setMaximumWidth(40)
        select_all_btn.clicked.connect(self.select_all)
        header_layout.addWidget(select_all_btn)

        select_none_btn = QPushButton("None")
        select_none_btn.setMaximumWidth(40)
        select_none_btn.clicked.connect(self.select_none)
        header_layout.addWidget(select_none_btn)

        header_layout.addStretch()
        layout.addLayout(header_layout)

        # Scrollable checkbox list (no max height - let parent scroll area handle it)
        scroll_area = QScrollArea()
        scroll_area.setWidgetResizable(True)
        scroll_area.setMinimumHeight(80)  # Minimum to show a few items

        checkbox_container = QWidget()
        checkbox_layout = QVBoxLayout(checkbox_container)
        checkbox_layout.setContentsMargins(0, 0, 0, 0)
        checkbox_layout.setSpacing(1)

        # Create checkbox for each unique value
        for value in self.unique_values:
            checkbox = QCheckBox(str(value))
            checkbox.setChecked(True)  # Start with all selected
            checkbox.stateChanged.connect(self._on_checkbox_changed)
            self.checkboxes[value] = checkbox
            checkbox_layout.addWidget(checkbox)

        checkbox_layout.addStretch()
        scroll_area.setWidget(checkbox_container)
        layout.addWidget(scroll_area)

        # Count label
        self.count_label = QLabel()
        self.count_label.setStyleSheet("font-size: 10px; color: gray;")
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
    Panel containing filters for multiple columns.

    Provides column-based filtering with AND logic across columns.

    Signals:
        filters_changed: Emitted when any filter changes
    """

    filters_changed = pyqtSignal()

    def __init__(self, parent=None):
        """Initialize multi-column filter panel."""
        super().__init__(parent)
        self.column_filters: Dict[str, ColumnFilterWidget] = {}
        self._init_ui()

    def _init_ui(self):
        """Initialize the UI."""
        self.main_layout = QVBoxLayout(self)
        self.main_layout.setContentsMargins(5, 5, 5, 5)
        self.main_layout.setSpacing(10)

        # Add stretch at the end to top-align filters
        self.main_layout.addStretch()
    
    def add_column_filter(self, column_name: str, unique_values: List[str]):
        """
        Add a filter for a column.
        
        Args:
            column_name: Name of the column
            unique_values: List of unique values in this column
        """
        if column_name in self.column_filters:
            # Remove existing filter
            self.remove_column_filter(column_name)
        
        # Create filter widget
        filter_widget = ColumnFilterWidget(column_name, unique_values)
        filter_widget.filter_changed.connect(self._on_filter_changed)
        
        # Wrap in a frame with title
        frame = QFrame()
        frame.setFrameStyle(QFrame.Shape.StyledPanel | QFrame.Shadow.Raised)
        frame_layout = QVBoxLayout(frame)
        frame_layout.setContentsMargins(5, 5, 5, 5)
        
        # Column name label
        label = QLabel(column_name.replace('_', ' ').title())
        label.setStyleSheet("font-weight: bold;")
        frame_layout.addWidget(label)
        
        frame_layout.addWidget(filter_widget)
        
        # Insert before the stretch
        self.main_layout.insertWidget(self.main_layout.count() - 1, frame)
        
        self.column_filters[column_name] = filter_widget
    
    def remove_column_filter(self, column_name: str):
        """Remove a column filter."""
        if column_name in self.column_filters:
            widget = self.column_filters[column_name]
            # Remove from layout
            parent_frame = widget.parent()
            if parent_frame:
                self.main_layout.removeWidget(parent_frame)
                parent_frame.deleteLater()
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

