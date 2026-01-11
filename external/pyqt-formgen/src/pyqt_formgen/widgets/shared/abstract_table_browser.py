"""
Abstract base class for table-based browser widgets.

Provides common infrastructure for widgets that display searchable, filterable
table views of item collections. Subclasses implement the abstract methods
to customize column layout, row population, and event handling.
"""

from abc import abstractmethod
from dataclasses import dataclass
from typing import Dict, List, Optional, Generic, TypeVar, Literal

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QLineEdit, QTableWidget, QTableWidgetItem,
    QHeaderView, QAbstractItemView, QLabel
)
from PyQt6.QtCore import Qt, pyqtSignal

from pyqt_formgen.theming import ColorScheme

from pyqt_formgen.services.search_service import SearchService
from pyqt_formgen.theming import StyleSheetGenerator

T = TypeVar('T')

SelectionMode = Literal['single', 'multi']


@dataclass
class ColumnDef:
    """Declarative column configuration for table browsers."""
    name: str
    key: str
    width: Optional[int] = None
    sortable: bool = True
    resizable: bool = True


class AbstractTableBrowser(QWidget, Generic[T]):
    """
    Abstract base class for table-based browser widgets.

    Provides:
    - Table widget with configurable columns (static or dynamic)
    - Search input with SearchService integration
    - Status label showing item counts
    - Row selection handling (single or multi-select)

    Subclasses must implement abstract methods to customize behavior.
    """

    # Signals for selection events
    item_selected = pyqtSignal(str, object)  # key, item
    item_double_clicked = pyqtSignal(str, object)  # key, item
    items_selected = pyqtSignal(list)  # list of keys (for multi-select)

    def __init__(
        self,
        color_scheme: Optional[ColorScheme] = None,
        selection_mode: SelectionMode = 'single',
        parent=None
    ):
        super().__init__(parent)

        self.color_scheme = color_scheme or ColorScheme()
        self.style_gen = StyleSheetGenerator(self.color_scheme)
        self._selection_mode = selection_mode

        # Data storage
        self.all_items: Dict[str, T] = {}
        self.filtered_items: Dict[str, T] = {}

        # Will be set by subclass or set_items()
        self._search_service: Optional[SearchService[T]] = None

        # Create UI components
        self._setup_ui()
        self._setup_connections()

    def _setup_ui(self):
        """Set up the base UI components."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(5, 5, 5, 5)
        layout.setSpacing(5)
        
        # Search input
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText(self.get_search_placeholder())
        layout.addWidget(self.search_input)
        
        # Status label
        self.status_label = QLabel("No items loaded")
        layout.addWidget(self.status_label)
        
        # Table widget
        self.table_widget = QTableWidget()
        self._configure_table()
        layout.addWidget(self.table_widget, 1)  # Stretch to fill
        
        # Apply styling
        self.table_widget.setStyleSheet(self.style_gen.generate_table_widget_style())

    def _configure_table(self):
        """Configure table based on column definitions."""
        columns = self.get_columns()
        self._apply_column_config(columns)

        # Configure selection mode
        self.table_widget.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        qt_mode = (
            QAbstractItemView.SelectionMode.ExtendedSelection
            if self._selection_mode == 'multi'
            else QAbstractItemView.SelectionMode.SingleSelection
        )
        self.table_widget.setSelectionMode(qt_mode)
        self.table_widget.setSortingEnabled(True)

    def _apply_column_config(self, columns: List[ColumnDef]):
        """Apply column configuration to table. Called by _configure_table and reconfigure_columns."""
        self.table_widget.setColumnCount(len(columns))
        self.table_widget.setHorizontalHeaderLabels([col.name for col in columns])

        # Configure header
        header = self.table_widget.horizontalHeader()
        header.setSectionsMovable(True)

        for i, col in enumerate(columns):
            mode = QHeaderView.ResizeMode.Interactive if col.resizable else QHeaderView.ResizeMode.Fixed
            header.setSectionResizeMode(i, mode)
            if col.width:
                self.table_widget.setColumnWidth(i, col.width)

    def reconfigure_columns(self):
        """Reconfigure table columns. Call when get_columns() returns different values."""
        columns = self.get_columns()
        self._apply_column_config(columns)

    def _setup_connections(self):
        """Connect signals to slots."""
        self.search_input.textChanged.connect(self._on_search_changed)
        self.table_widget.itemSelectionChanged.connect(self._on_selection_changed)
        self.table_widget.itemDoubleClicked.connect(self._on_double_click)

    def _on_search_changed(self, search_term: str):
        """Handle search input changes."""
        # _search_service is set by set_items() which must be called before use
        self.filtered_items = self._search_service.filter(search_term)
        self.populate_table(self.filtered_items)
        self._update_status()

    def _on_selection_changed(self):
        """Handle table selection changes."""
        selected_keys = self.get_selected_keys()
        if not selected_keys:
            return  # Valid: user clicked empty area

        if self._selection_mode == 'multi':
            # Multi-select: emit list of keys
            self.items_selected.emit(selected_keys)
            self.on_items_selected(selected_keys)
        else:
            # Single-select: emit first key and item
            key = selected_keys[0]
            item = self.filtered_items[key]
            self.item_selected.emit(key, item)
            self.on_item_selected(key, item)

    def _on_double_click(self, table_item: QTableWidgetItem):
        """Handle double-click on table row."""
        row = table_item.row()
        key_item = self.table_widget.item(row, 0)
        key = key_item.data(Qt.ItemDataRole.UserRole)

        # Key in table → item in filtered_items (invariant)
        item = self.filtered_items[key]
        self.item_double_clicked.emit(key, item)
        self.on_item_double_clicked(key, item)

    def get_selected_keys(self) -> List[str]:
        """Return list of selected item keys. Works for both single and multi-select."""
        selected_rows = set()
        for table_item in self.table_widget.selectedItems():
            selected_rows.add(table_item.row())

        keys = []
        for row in sorted(selected_rows):
            key_item = self.table_widget.item(row, 0)
            keys.append(key_item.data(Qt.ItemDataRole.UserRole))
        return keys

    def _update_status(self):
        """Update status label with current counts."""
        total = len(self.all_items)
        filtered = len(self.filtered_items)
        self.status_label.setText(f"Showing {filtered}/{total} items")

    def set_items(self, items: Dict[str, T]):
        """Set the items to display in the table."""
        self.all_items = items
        self.filtered_items = items.copy()

        # Initialize or update search service
        self._search_service = SearchService(
            all_items=self.all_items,
            searchable_text_extractor=self.get_searchable_text
        )

        self.populate_table(self.filtered_items)
        self._update_status()

    def populate_table(self, items: Dict[str, T]):
        """Populate the table with the given items."""
        self.table_widget.setSortingEnabled(False)
        self.table_widget.setRowCount(len(items))

        columns = self.get_columns()

        for row, (key, item) in enumerate(items.items()):
            row_data = self.extract_row_data(item)

            for col, value in enumerate(row_data):
                table_item = QTableWidgetItem(str(value))

                # Store key in first column for lookup
                if col == 0:
                    table_item.setData(Qt.ItemDataRole.UserRole, key)

                self.table_widget.setItem(row, col, table_item)

        self.table_widget.setSortingEnabled(True)

    def refresh(self):
        """Refresh the table display."""
        self.populate_table(self.filtered_items)
        self._update_status()

    # =========================================================================
    # Abstract methods - subclasses must implement
    # =========================================================================

    @abstractmethod
    def get_columns(self) -> List[ColumnDef]:
        """Return column definitions for the table."""
        raise NotImplementedError

    @abstractmethod
    def extract_row_data(self, item: T) -> List[str]:
        """Extract display values for a table row from an item."""
        raise NotImplementedError

    @abstractmethod
    def get_searchable_text(self, item: T) -> str:
        """Return searchable text for an item."""
        raise NotImplementedError

    # =========================================================================
    # Optional hooks - subclasses can override
    # =========================================================================

    def get_search_placeholder(self) -> str:
        """Return placeholder text for search input."""
        return "Search..."

    def on_item_selected(self, key: str, item: T):
        """Called when an item is selected (single-select mode). Override to handle."""
        pass

    def on_items_selected(self, keys: List[str]):
        """Called when items are selected (multi-select mode). Override to handle."""
        pass

    def on_item_double_clicked(self, key: str, item: T):
        """Called when an item is double-clicked. Override to handle action."""
        pass
