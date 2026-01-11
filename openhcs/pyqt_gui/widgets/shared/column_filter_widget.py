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
from PyQt6.QtCore import pyqtSignal, Qt, QSize

from pyqt_formgen.theming import ColorScheme
from pyqt_formgen.theming import StyleSheetGenerator
from pyqt_formgen.forms.layout_constants import COMPACT_LAYOUT

logger = logging.getLogger(__name__)


class NonCompressingSplitter(QSplitter):
    """
    A QSplitter that maintains its size based on widget sizes, not available space.

    When handles are moved, this splitter grows the total size instead of
    redistributing space among widgets.
    """

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        # Remove maximum height constraint
        self.setMaximumHeight(16777215)  # QWIDGETSIZE_MAX
        # Set a reasonable width
        self.setMinimumWidth(200)
        # Flag to prevent resize event from interfering
        self._in_move = False

    def moveSplitter(self, pos, index):
        """Override to grow total size instead of redistributing space."""
        # Get current sizes before any changes
        old_sizes = self.sizes()
        if not old_sizes or index <= 0 or index > len(old_sizes):
            super().moveSplitter(pos, index)
            return

        # Set flag to prevent resize interference
        self._in_move = True

        # Calculate the position change
        # The handle is between widget[index-1] and widget[index]
        old_pos = sum(old_sizes[:index]) + (index * self.handleWidth())
        delta = pos - old_pos

        # Create new sizes - only change the widget above the handle
        new_sizes = old_sizes.copy()
        new_sizes[index - 1] = max(0, old_sizes[index - 1] + delta)

        # Don't shrink the widget below - keep all other widgets the same size
        # This means the total size will grow/shrink

        # Calculate new total height
        total_height = sum(new_sizes)
        num_handles = max(0, self.count() - 1)
        total_height += num_handles * self.handleWidth()

        # Set the new sizes FIRST before resizing
        # This prevents Qt from redistributing space when we resize
        self.setSizes(new_sizes)

        # Now update minimum height and resize
        self.setMinimumHeight(total_height)
        self.setFixedHeight(total_height)

        self._in_move = False

    def resizeEvent(self, event):
        """Override to prevent automatic size redistribution."""
        if self._in_move:
            # During moveSplitter, don't let Qt redistribute sizes
            super().resizeEvent(event)
            return

        # Normal resize - let Qt handle it
        super().resizeEvent(event)


class ColumnFilterWidget(QFrame):
    """
    Filter widget for a single column showing checkboxes for unique values.
    Uses compact styling matching parameter form manager.

    Signals:
        filter_changed: Emitted when filter selection changes
    """

    filter_changed = pyqtSignal()

    def __init__(self, column_name: str, unique_values: List[str],
                 color_scheme: Optional[ColorScheme] = None, parent=None):
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
        self.color_scheme = color_scheme or ColorScheme()
        self.style_gen = StyleSheetGenerator(self.color_scheme)

        # Apply frame styling
        self.setFrameStyle(QFrame.Shape.StyledPanel | QFrame.Shadow.Raised)
        self.setStyleSheet(f"""
            QFrame {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.panel_bg)};
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_color)};
                border-radius: 3px;
            }}
        """)

        self._init_ui()
    
    def _init_ui(self):
        """Initialize the UI with compact styling matching parameter form manager."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(*COMPACT_LAYOUT.main_layout_margins)
        layout.setSpacing(COMPACT_LAYOUT.main_layout_spacing)

        # Header: Column title on left, buttons on right (same row)
        header_layout = QHBoxLayout()
        header_layout.setContentsMargins(0, 0, 0, 0)
        header_layout.setSpacing(COMPACT_LAYOUT.parameter_row_spacing)

        # Column title label (bold, accent color)
        title_label = QLabel(self.column_name)
        title_label.setStyleSheet(f"""
            QLabel {{
                font-weight: bold;
                color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};
                font-size: 11px;
            }}
        """)
        header_layout.addWidget(title_label)

        header_layout.addStretch()

        # All/None buttons (compact, matching parameter form buttons)
        select_all_btn = QPushButton("All")
        select_all_btn.setMaximumWidth(35)
        select_all_btn.setMaximumHeight(20)
        select_all_btn.setStyleSheet(self.style_gen.generate_button_style())
        select_all_btn.clicked.connect(self.select_all)
        header_layout.addWidget(select_all_btn)

        select_none_btn = QPushButton("None")
        select_none_btn.setMaximumWidth(35)
        select_none_btn.setMaximumHeight(20)
        select_none_btn.setStyleSheet(self.style_gen.generate_button_style())
        select_none_btn.clicked.connect(self.select_none)
        header_layout.addWidget(select_none_btn)

        layout.addLayout(header_layout)

        # Scrollable checkbox list - each filter has its own scroll area
        from PyQt6.QtWidgets import QSizePolicy
        scroll_area = QScrollArea()
        scroll_area.setWidgetResizable(True)
        scroll_area.setMinimumHeight(60)  # Minimum to show a few items
        scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        scroll_area.setStyleSheet(f"""
            QScrollArea {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.window_bg)};
                border: none;
            }}
        """)

        checkbox_container = QWidget()
        checkbox_layout = QVBoxLayout(checkbox_container)
        checkbox_layout.setContentsMargins(0, 0, 0, 0)
        checkbox_layout.setSpacing(COMPACT_LAYOUT.content_layout_spacing)

        # Create checkbox for each unique value (compact styling)
        for value in self.unique_values:
            checkbox = QCheckBox(str(value))
            checkbox.setChecked(True)  # Start with all selected
            checkbox.setStyleSheet(f"""
                QCheckBox {{
                    color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
                    spacing: 4px;
                    font-size: 11px;
                }}
                QCheckBox::indicator {{
                    width: 14px;
                    height: 14px;
                }}
            """)
            checkbox.stateChanged.connect(self._on_checkbox_changed)
            self.checkboxes[value] = checkbox
            checkbox_layout.addWidget(checkbox)

        checkbox_layout.addStretch()
        scroll_area.setWidget(checkbox_container)
        # Add scroll area with stretch factor so it takes up available space
        layout.addWidget(scroll_area, 1)

        # Count label (compact, secondary text color)
        self.count_label = QLabel()
        self.count_label.setStyleSheet(f"""
            QLabel {{
                font-size: 10px;
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
    
    def select_all(self, block_signals: bool = False):
        """
        Select all checkboxes.

        Args:
            block_signals: If True, block signals while updating checkboxes
        """
        for checkbox in self.checkboxes.values():
            if block_signals:
                checkbox.blockSignals(True)
            checkbox.setChecked(True)
            if block_signals:
                checkbox.blockSignals(False)

        if block_signals:
            self._update_count_label()

    def select_none(self, block_signals: bool = False):
        """
        Deselect all checkboxes.

        Args:
            block_signals: If True, block signals while updating checkboxes
        """
        for checkbox in self.checkboxes.values():
            if block_signals:
                checkbox.blockSignals(True)
            checkbox.setChecked(False)
            if block_signals:
                checkbox.blockSignals(False)

        if block_signals:
            self._update_count_label()
    
    def get_selected_values(self) -> Set[str]:
        """Get set of selected values."""
        return {value for value, checkbox in self.checkboxes.items() if checkbox.isChecked()}
    
    def set_selected_values(self, values: Set[str], block_signals: bool = False):
        """
        Set which values are selected.

        Args:
            values: Set of values to select
            block_signals: If True, block signals while updating checkboxes to prevent loops
        """
        for value, checkbox in self.checkboxes.items():
            if block_signals:
                checkbox.blockSignals(True)
            checkbox.setChecked(value in values)
            if block_signals:
                checkbox.blockSignals(False)

        # Update count label manually if signals were blocked
        if block_signals:
            self._update_count_label()


class MultiColumnFilterPanel(QWidget):
    """
    Panel containing filters for multiple columns with resizable splitters.

    Provides column-based filtering with AND logic across columns.
    Each filter can be resized independently using vertical splitters.

    Signals:
        filters_changed: Emitted when any filter changes
    """

    filters_changed = pyqtSignal()

    def __init__(self, color_scheme: Optional[ColorScheme] = None, parent=None):
        """Initialize multi-column filter panel."""
        super().__init__(parent)
        self.column_filters: Dict[str, ColumnFilterWidget] = {}
        self.color_scheme = color_scheme or ColorScheme()
        self._init_ui()

    def _init_ui(self):
        """Initialize the UI with vertical splitter for resizable filters in a scroll area."""
        from PyQt6.QtWidgets import QSizePolicy, QScrollArea

        # Use custom non-compressing splitter so each filter can be resized
        self.splitter = NonCompressingSplitter(Qt.Orientation.Vertical)
        self.splitter.setChildrenCollapsible(False)  # Prevent filters from collapsing
        self.splitter.setHandleWidth(5)  # Make handle more visible and easier to grab

        # Wrap splitter in scroll area so the whole group can scroll
        self.scroll_area = QScrollArea()
        # CRITICAL: setWidgetResizable(False) prevents scroll area from forcing splitter to fit
        self.scroll_area.setWidgetResizable(False)
        self.scroll_area.setWidget(self.splitter)
        self.scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.scroll_area.setFrameShape(QFrame.Shape.NoFrame)

        main_layout = QVBoxLayout(self)
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)
        main_layout.addWidget(self.scroll_area)

    def resizeEvent(self, event):
        """Handle resize to update splitter width."""
        super().resizeEvent(event)
        # Update splitter width to match scroll area viewport width
        viewport_width = self.scroll_area.viewport().width()
        if viewport_width > 0:
            self.splitter.setFixedWidth(viewport_width)

    def showEvent(self, event):
        """Handle show event to ensure proper initial sizing."""
        super().showEvent(event)
        # When first shown, ensure splitter has correct width and recalculate sizes
        viewport_width = self.scroll_area.viewport().width()
        if viewport_width > 0:
            self.splitter.setFixedWidth(viewport_width)
            # Recalculate sizes now that we have proper dimensions
            if self.column_filters:
                self._update_splitter_sizes()
    
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

        # Create filter widget with color scheme
        filter_widget = ColumnFilterWidget(column_name, unique_values, self.color_scheme)
        filter_widget.filter_changed.connect(self._on_filter_changed)

        # Add to splitter (each filter is independently resizable)
        self.splitter.addWidget(filter_widget)

        self.column_filters[column_name] = filter_widget

        # Update sizes after adding widget
        self._update_splitter_sizes()
    
    def _update_splitter_sizes(self):
        """Update splitter sizes based on each filter's content."""
        num_filters = len(self.column_filters)
        if num_filters > 0:
            # Force layout update first to get accurate size hints
            for filter_widget in self.column_filters.values():
                filter_widget.updateGeometry()

            # Size each filter based on its actual content (sizeHint)
            sizes = []
            for filter_widget in self.column_filters.values():
                # Get the widget's preferred size
                hint = filter_widget.sizeHint()
                # Use the height hint, with a minimum of 100px
                sizes.append(max(100, hint.height()))

            self.splitter.setSizes(sizes)

            # Set initial minimum height
            total_height = sum(sizes)
            num_handles = max(0, num_filters - 1)
            total_height += num_handles * self.splitter.handleWidth()
            self.splitter.setMinimumHeight(total_height)

            # Resize to the calculated height
            self.splitter.setFixedHeight(total_height)

            # Schedule a deferred update to fix layout after widgets are fully rendered
            from PyQt6.QtCore import QTimer
            QTimer.singleShot(0, self._deferred_size_update)

    def _deferred_size_update(self):
        """Deferred size update after widgets are fully rendered."""
        num_filters = len(self.column_filters)
        if num_filters > 0:
            # Force synchronous event processing to ensure layout is complete
            from PyQt6.QtWidgets import QApplication
            QApplication.processEvents()

            # Force a full layout pass first
            self.splitter.updateGeometry()
            for filter_widget in self.column_filters.values():
                filter_widget.layout().activate()
                filter_widget.updateGeometry()

            # Process events again after geometry updates
            QApplication.processEvents()

            # Recalculate sizes now that widgets are rendered
            sizes = []
            for filter_widget in self.column_filters.values():
                hint = filter_widget.sizeHint()
                sizes.append(max(100, hint.height()))

            self.splitter.setSizes(sizes)

            total_height = sum(sizes)
            num_handles = max(0, num_filters - 1)
            total_height += num_handles * self.splitter.handleWidth()
            self.splitter.setMinimumHeight(total_height)
            self.splitter.setFixedHeight(total_height)

            # Force a repaint to ensure proper rendering
            self.splitter.update()

    def remove_column_filter(self, column_name: str):
        """Remove a column filter."""
        if column_name in self.column_filters:
            widget = self.column_filters[column_name]
            # Remove from splitter
            widget.setParent(None)
            widget.deleteLater()
            del self.column_filters[column_name]
            # Update sizes after removing
            self._update_splitter_sizes()
    
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

