"""
Function Selector Dialog for PyQt6 GUI.

Mirrors the Textual TUI FunctionSelectorWindow functionality using the same
FunctionRegistryService and business logic.
"""

import logging
from typing import Callable, Optional, Dict, List, Tuple

from PyQt6.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QLineEdit, QTableWidget,
    QTableWidgetItem, QPushButton, QLabel, QHeaderView, QAbstractItemView,
    QTreeWidget, QTreeWidgetItem, QSplitter, QWidget, QSizePolicy
)
from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QFont

# REUSE the actual working Textual TUI services
from openhcs.textual_tui.services.function_registry_service import FunctionRegistryService
from openhcs.processing.backends.lib_registry.unified_registry import FunctionMetadata

logger = logging.getLogger(__name__)


class FunctionSelectorDialog(QDialog):
    """
    Enhanced function selector dialog with table-based interface and rich metadata.

    Uses unified metadata from FunctionRegistryService for consistent display
    of both OpenHCS and external library functions.
    """

    # Class-level cache for expensive metadata discovery
    _metadata_cache: Optional[Dict[str, FunctionMetadata]] = None

    # Signals
    function_selected = pyqtSignal(object)  # Selected function

    def __init__(self, current_function: Optional[Callable] = None, parent=None):
        """
        Initialize function selector dialog.

        Args:
            current_function: Currently selected function (for highlighting)
            parent: Parent widget
        """
        super().__init__(parent)

        self.current_function = current_function
        self.selected_function = None

        # Load enhanced function metadata
        self.all_functions_metadata: Dict[str, FunctionMetadata] = {}
        self.filtered_functions: Dict[str, FunctionMetadata] = {}
        self._load_function_data()

        self.setup_ui()
        self.setup_connections()
        self.populate_module_tree()
        self.populate_function_table()

        logger.debug(f"Function selector initialized with {len(self.all_functions_metadata)} functions")

    def _load_function_data(self) -> None:
        """Load function data efficiently using existing FUNC_REGISTRY."""
        # Check if we have cached metadata
        if FunctionSelectorDialog._metadata_cache is not None:
            logger.debug("Using cached function metadata")
            self.all_functions_metadata = FunctionSelectorDialog._metadata_cache
            self.filtered_functions = self.all_functions_metadata.copy()
            return

        # Use the fast existing FUNC_REGISTRY instead of expensive discovery
        logger.info("Loading functions from existing registry (fast path)")

        # Import FUNC_REGISTRY directly for maximum speed
        from openhcs.processing.func_registry import FUNC_REGISTRY

        # Get functions by backend (this is instant - uses existing cached data)
        functions_by_backend = {}
        for memory_type, functions in FUNC_REGISTRY.items():
            backend_name = memory_type.replace('_', ' ').title()
            functions_by_backend[backend_name] = [(func, func.__name__) for func in functions]

        # Convert to metadata format quickly
        self.all_functions_metadata = {}

        for backend, functions in functions_by_backend.items():
            for func, display_name in functions:
                # Create basic metadata without expensive discovery
                metadata = self._create_basic_metadata(func, display_name, backend)
                self.all_functions_metadata[display_name] = metadata

        # Cache the results for future use
        FunctionSelectorDialog._metadata_cache = self.all_functions_metadata
        logger.info(f"Loaded {len(self.all_functions_metadata)} functions efficiently")

        self.filtered_functions = self.all_functions_metadata.copy()

    def _create_basic_metadata(self, func: Callable, display_name: str, backend: str):
        """Create basic metadata without expensive discovery."""
        # Create a simple metadata object for fast loading
        # We'll use a dict instead of FunctionMetadata to avoid import issues
        return {
            'name': display_name,
            'func': func,
            'module': getattr(func, '__module__', 'unknown'),
            'contract': getattr(func, '__processing_contract__', None),
            'tags': [backend.lower()],
            'doc': (getattr(func, '__doc__', '') or '').strip()
        }

    def populate_module_tree(self):
        """Populate the module tree with hierarchical function organization."""
        self.module_tree.clear()

        # Organize functions by library and module
        library_modules = self._organize_by_library_and_module()

        # Build tree structure
        for library_name, modules in library_modules.items():
            library_item = QTreeWidgetItem(self.module_tree)
            library_item.setText(0, f"{library_name} ({sum(len(funcs) for funcs in modules.values())} functions)")
            library_item.setData(0, Qt.ItemDataRole.UserRole, {"type": "library", "name": library_name})
            library_item.setExpanded(True)

            for module_path, functions in modules.items():
                module_item = QTreeWidgetItem(library_item)
                module_item.setText(0, f"{module_path} ({len(functions)} functions)")
                module_item.setData(0, Qt.ItemDataRole.UserRole, {
                    "type": "module",
                    "library": library_name,
                    "module": module_path,
                    "functions": functions
                })

    def _organize_by_library_and_module(self):
        """Organize functions by library and module structure."""
        library_modules = {}

        for func_name, metadata in self.all_functions_metadata.items():
            # Determine library from tags or module
            library = self._determine_library(metadata)

            # Extract meaningful module path
            module_path = self._extract_module_path(metadata)

            # Initialize library if not exists
            if library not in library_modules:
                library_modules[library] = {}

            # Initialize module if not exists
            if module_path not in library_modules[library]:
                library_modules[library][module_path] = []

            # Add function to module
            library_modules[library][module_path].append(func_name)

        return library_modules

    def _determine_library(self, metadata):
        """Determine library name from metadata."""
        module = metadata.get('module', '')
        tags = metadata.get('tags', [])

        if 'openhcs' in module:
            return 'OpenHCS'
        elif 'skimage' in module:
            return 'scikit-image'
        elif 'pyclesperanto' in module or 'cle' in module:
            return 'pyclesperanto'
        elif 'cupy' in module.lower() or 'gpu' in tags:
            return 'CuPy'
        else:
            return 'Unknown'

    def _extract_module_path(self, metadata):
        """Extract meaningful module path for display."""
        module = metadata.get('module', '')

        # For OpenHCS functions, show the backend structure
        if 'openhcs' in module:
            parts = module.split('.')
            # Find the backends part and show from there
            try:
                backends_idx = parts.index('backends')
                return '.'.join(parts[backends_idx+1:])  # Skip 'backends'
            except ValueError:
                return module.split('.')[-1]  # Just the last part

        # For external libraries, show the meaningful part
        elif 'skimage' in module:
            parts = module.split('.')
            try:
                skimage_idx = parts.index('skimage')
                return '.'.join(parts[skimage_idx+1:]) or 'core'
            except ValueError:
                return module.split('.')[-1]

        elif 'pyclesperanto' in module or 'cle' in module:
            return 'pyclesperanto_prototype'

        elif 'cupy' in module.lower():
            parts = module.split('.')
            try:
                cupy_idx = next(i for i, part in enumerate(parts) if 'cupy' in part.lower())
                return '.'.join(parts[cupy_idx+1:]) or 'core'
            except (StopIteration, IndexError):
                return module.split('.')[-1]

        return module.split('.')[-1]

    @classmethod
    def clear_metadata_cache(cls) -> None:
        """Clear the cached metadata to force re-discovery."""
        cls._metadata_cache = None
        logger.info("Function metadata cache cleared")
    
    def setup_ui(self):
        """Setup the dual-pane user interface with tree and table."""
        self.setWindowTitle("Select Function - Dual Pane View")
        self.setModal(True)
        self.resize(1200, 700)  # Larger size for dual panes
        self.setMinimumSize(800, 500)  # Ensure minimum usable size

        layout = QVBoxLayout(self)

        # Title
        title_label = QLabel("Select Function - Dual Pane View")
        title_font = QFont()
        title_font.setBold(True)
        title_font.setPointSize(12)
        title_label.setFont(title_font)
        layout.addWidget(title_label)

        # Search input with enhanced placeholder
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("Search functions by name, module, contract, or tags...")
        layout.addWidget(self.search_input)

        # Function count label
        self.function_count_label = QLabel(f"Functions: {len(self.all_functions_metadata)}")
        layout.addWidget(self.function_count_label)

        # Create splitter for dual-pane layout (horizontal split = side-by-side panes)
        splitter = QSplitter(Qt.Orientation.Horizontal)
        splitter.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        splitter.setHandleWidth(5)  # Make splitter handle more visible

        # Left pane: Module tree
        left_widget = QWidget()
        left_layout = QVBoxLayout(left_widget)
        left_layout.setContentsMargins(0, 0, 0, 0)

        tree_title = QLabel("Module Structure")
        tree_title.setStyleSheet("font-weight: bold; background-color: #e0e0e0; padding: 5px;")
        left_layout.addWidget(tree_title)

        self.module_tree = QTreeWidget()
        self.module_tree.setHeaderLabel("Libraries and Modules")
        self.module_tree.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        left_layout.addWidget(self.module_tree)

        splitter.addWidget(left_widget)

        # Right pane: Function table
        right_widget = QWidget()
        right_layout = QVBoxLayout(right_widget)
        right_layout.setContentsMargins(0, 0, 0, 0)

        table_title = QLabel("Function Details")
        table_title.setStyleSheet("font-weight: bold; background-color: #e0e0e0; padding: 5px;")
        right_layout.addWidget(table_title)

        # Function table with enhanced columns
        self.function_table = QTableWidget()
        self.function_table.setColumnCount(6)
        self.function_table.setHorizontalHeaderLabels([
            "Name", "Module", "Backend", "Contract", "Tags", "Description"
        ])

        # Configure table behavior
        self.function_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.function_table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.function_table.setSortingEnabled(True)
        self.function_table.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)

        # Configure column widths for better readability
        header = self.function_table.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)  # Name
        header.setSectionResizeMode(1, QHeaderView.ResizeMode.Interactive)       # Module (allow manual resize)
        header.setSectionResizeMode(2, QHeaderView.ResizeMode.ResizeToContents)  # Backend
        header.setSectionResizeMode(3, QHeaderView.ResizeMode.ResizeToContents)  # Contract
        header.setSectionResizeMode(4, QHeaderView.ResizeMode.ResizeToContents)  # Tags
        header.setSectionResizeMode(5, QHeaderView.ResizeMode.Stretch)           # Description

        # Set minimum column widths for better display
        self.function_table.setColumnWidth(1, 250)  # Module column - wider for full paths
        self.function_table.setColumnWidth(5, 200)  # Description column - minimum width

        right_layout.addWidget(self.function_table)
        splitter.addWidget(right_widget)

        # Set splitter proportions (40% tree, 60% table)
        splitter.setSizes([400, 600])

        # Add splitter to layout with stretch factor to fill available space
        layout.addWidget(splitter, 1)  # Stretch factor of 1 to expand
        
        # Buttons (mirrors Textual TUI dialog-buttons)
        button_layout = QHBoxLayout()
        button_layout.addStretch()
        
        self.select_btn = QPushButton("Select")
        self.select_btn.setEnabled(False)
        self.select_btn.setDefault(True)
        button_layout.addWidget(self.select_btn)
        
        cancel_btn = QPushButton("Cancel")
        button_layout.addWidget(cancel_btn)
        
        button_layout.addStretch()
        layout.addLayout(button_layout)
        
        # Connect buttons
        self.select_btn.clicked.connect(self.accept_selection)
        cancel_btn.clicked.connect(self.reject)
    
    def setup_connections(self):
        """Setup signal/slot connections."""
        # Search functionality
        self.search_input.textChanged.connect(self.filter_functions)

        # Tree selection for filtering
        self.module_tree.itemSelectionChanged.connect(self.on_tree_selection_changed)

        # Table selection
        self.function_table.itemSelectionChanged.connect(self.on_table_selection_changed)
        self.function_table.itemDoubleClicked.connect(self.on_table_double_click)
    
    def populate_function_table(self, functions_metadata: Optional[Dict[str, FunctionMetadata]] = None):
        """Populate function table with enhanced metadata."""
        if functions_metadata is None:
            functions_metadata = self.filtered_functions

        self.function_table.setRowCount(len(functions_metadata))
        self.function_table.setSortingEnabled(False)  # Disable during population

        for row, (func_name, metadata) in enumerate(functions_metadata.items()):
            # Extract backend from function attributes or use tags
            backend = metadata.get('tags', ['unknown'])[0] if metadata.get('tags') else 'unknown'

            # Format tags as comma-separated string
            tags_str = ", ".join(metadata.get('tags', [])) if metadata.get('tags') else ""

            # Truncate description for table display (more generous)
            doc = metadata.get('doc', '')
            description = doc[:150] + "..." if len(doc) > 150 else doc

            # Create table items
            name_item = QTableWidgetItem(metadata.get('name', func_name))
            # Show full module path, not just the last part
            full_module = metadata.get('module', 'unknown')
            module_item = QTableWidgetItem(full_module)
            backend_item = QTableWidgetItem(backend.title())

            # Handle contract display
            contract = metadata.get('contract')
            contract_name = contract.name if hasattr(contract, 'name') else str(contract) if contract else "unknown"
            contract_item = QTableWidgetItem(contract_name)

            tags_item = QTableWidgetItem(tags_str)
            description_item = QTableWidgetItem(description)

            # Store function reference in name item
            name_item.setData(Qt.ItemDataRole.UserRole, {"func": metadata.get('func'), "metadata": metadata})

            # Set items in table
            self.function_table.setItem(row, 0, name_item)
            self.function_table.setItem(row, 1, module_item)
            self.function_table.setItem(row, 2, backend_item)
            self.function_table.setItem(row, 3, contract_item)
            self.function_table.setItem(row, 4, tags_item)
            self.function_table.setItem(row, 5, description_item)

            # Highlight current function if it matches
            if self.current_function and metadata.func == self.current_function:
                self.function_table.selectRow(row)

        self.function_table.setSortingEnabled(True)  # Re-enable sorting
    
    def filter_functions(self, search_term: str):
        """Filter functions based on search term across multiple fields."""
        if not search_term.strip():
            # Show all functions
            self.filtered_functions = self.all_functions_metadata.copy()
        else:
            # Filter functions across multiple fields
            search_lower = search_term.lower()
            self.filtered_functions = {}

            for func_name, metadata in self.all_functions_metadata.items():
                # Search in name, module, contract, tags, and description
                contract = metadata.get('contract')
                contract_name = contract.name if hasattr(contract, 'name') else str(contract) if contract else ""

                searchable_text = " ".join([
                    metadata.get('name', '').lower(),
                    metadata.get('module', '').lower(),
                    contract_name.lower(),
                    " ".join(metadata.get('tags', [])).lower(),
                    metadata.get('doc', '').lower()
                ])

                if search_lower in searchable_text:
                    self.filtered_functions[func_name] = metadata

        # Update table and count
        self.populate_function_table(self.filtered_functions)
        self.function_count_label.setText(f"Functions: {len(self.filtered_functions)}/{len(self.all_functions_metadata)}")

        # Clear selection when filtering
        self.selected_function = None
        self.select_btn.setEnabled(False)

    def on_tree_selection_changed(self):
        """Handle tree selection changes to filter table."""
        selected_items = self.module_tree.selectedItems()
        if not selected_items:
            return

        item = selected_items[0]
        data = item.data(0, Qt.ItemDataRole.UserRole)

        if data:
            node_type = data.get("type")

            if node_type == "module":
                # Filter table to show only functions from this module
                module_functions = data.get("functions", [])
                self.filtered_functions = {
                    name: metadata for name, metadata in self.all_functions_metadata.items()
                    if name in module_functions
                }

                # Update table and count
                self.populate_function_table(self.filtered_functions)
                self.function_count_label.setText(
                    f"Functions: {len(self.filtered_functions)}/{len(self.all_functions_metadata)} (filtered by module)"
                )

            elif node_type == "library":
                # Filter table to show only functions from this library
                library_name = data.get("name")
                self.filtered_functions = {
                    name: metadata for name, metadata in self.all_functions_metadata.items()
                    if self._determine_library(metadata) == library_name
                }

                # Update table and count
                self.populate_function_table(self.filtered_functions)
                self.function_count_label.setText(
                    f"Functions: {len(self.filtered_functions)}/{len(self.all_functions_metadata)} (filtered by library)"
                )

        # Clear function selection when tree selection changes
        self.selected_function = None
        self.select_btn.setEnabled(False)
    
    def on_table_selection_changed(self):
        """Handle table selection changes."""
        selected_items = self.function_table.selectedItems()
        if selected_items:
            # Get the first item in the selected row (name column)
            row = selected_items[0].row()
            name_item = self.function_table.item(row, 0)

            if name_item:
                data = name_item.data(Qt.ItemDataRole.UserRole)
                if data and data.get("func"):
                    self.selected_function = data["func"]
                    self.select_btn.setEnabled(True)
                else:
                    self.selected_function = None
                    self.select_btn.setEnabled(False)
            else:
                self.selected_function = None
                self.select_btn.setEnabled(False)
        else:
            self.selected_function = None
            self.select_btn.setEnabled(False)

    def on_table_double_click(self, item):
        """Handle table double-click."""
        if item:
            row = item.row()
            name_item = self.function_table.item(row, 0)

            if name_item:
                data = name_item.data(Qt.ItemDataRole.UserRole)
                if data and data.get("func"):
                    self.selected_function = data["func"]
                    self.accept_selection()
    
    def accept_selection(self):
        """Accept the selected function."""
        if self.selected_function:
            self.function_selected.emit(self.selected_function)
            self.accept()
    
    def get_selected_function(self) -> Optional[Callable]:
        """Get the selected function."""
        return self.selected_function
    
    @staticmethod
    def select_function(current_function: Optional[Callable] = None, parent=None) -> Optional[Callable]:
        """
        Static method to show function selector and return selected function.
        
        Args:
            current_function: Currently selected function (for highlighting)
            parent: Parent widget
            
        Returns:
            Selected function or None if cancelled
        """
        dialog = FunctionSelectorDialog(current_function, parent)
        if dialog.exec() == QDialog.DialogCode.Accepted:
            return dialog.get_selected_function()
        return None
