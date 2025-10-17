"""
Function Selector Dialog for PyQt6 GUI.

Mirrors the Textual TUI FunctionSelectorWindow functionality using the same
FunctionRegistryService and business logic.
"""

import logging
from typing import Callable, Optional, Dict, Any

from PyQt6.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QLineEdit, QTableWidget,
    QTableWidgetItem, QPushButton, QLabel, QHeaderView, QAbstractItemView,
    QTreeWidget, QTreeWidgetItem, QSplitter, QWidget, QSizePolicy
)
from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QFont

# Use the registry service from correct location
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.processing.backends.lib_registry.unified_registry import FunctionMetadata
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator

logger = logging.getLogger(__name__)


# Direct registry-based library detection (robust, no pattern matching)
class LibraryDetector:
    """Direct library detection using registry ownership data."""

    # Class-level cache for efficient lookup (OpenHCS caching pattern)
    _registry_functions: Optional[Dict[str, str]] = None
    _registry_display_names: Optional[Dict[str, str]] = None

    @classmethod
    def get_function_library(cls, func_name: str, module_path: str) -> str:
        """Get library for a function using direct registry ownership (robust approach)."""
        if cls._registry_functions is None:
            cls._build_registry_ownership_cache()

        # Direct lookup by function name (most reliable)
        if func_name in cls._registry_functions:
            return cls._registry_functions[func_name]

        # Fallback: check by registry library name in module path
        for registry_name, display_name in cls._registry_display_names.items():
            if registry_name.lower() in module_path.lower():
                return display_name

        return 'Unknown'

    @classmethod
    def _build_registry_ownership_cache(cls):
        """Build cache of function ownership using FunctionRegistryService."""
        cls._registry_functions = {}
        cls._registry_display_names = {}

        # Use existing RegistryService (already has discovery and caching)
        unified_functions = RegistryService.get_all_functions_with_metadata()

        # Build ownership cache from unified metadata
        for func_name, metadata in unified_functions.items():
            # Extract library name from tags or module
            library_name = cls._extract_library_name(metadata)
            cls._registry_functions[func_name] = library_name

    @classmethod
    def _extract_library_name(cls, metadata) -> str:
        """Extract library name from function metadata."""
        # Use tags first (most reliable)
        if metadata.tags:
            primary_tag = metadata.tags[0]
            return primary_tag.title()

        # Fallback to module path analysis
        module_path = metadata.module.lower()
        if 'openhcs' in module_path:
            return 'OpenHCS'
        elif 'cupy' in module_path:
            return 'CuPy'
        elif 'pyclesperanto' in module_path or 'cle' in module_path:
            return 'Pyclesperanto'
        elif 'skimage' in module_path:
            return 'scikit-image'

        return 'Unknown'


class FunctionSelectorDialog(QDialog):
    """
    Enhanced function selector dialog with table-based interface and rich metadata.

    Uses unified metadata from FunctionRegistryService for consistent display
    of both OpenHCS and external library functions.
    """

    # Class-level cache for expensive metadata discovery
    _metadata_cache: Optional[Dict[str, FunctionMetadata]] = None

    @classmethod
    def clear_cache(cls):
        """Clear the function metadata cache. Call this when function registry is reloaded."""
        cls._metadata_cache = None
        logger.debug("Function selector dialog cache cleared")

    # UI Constants (RST principle: eliminate magic numbers)
    DEFAULT_WIDTH = 1200
    DEFAULT_HEIGHT = 700
    MIN_WIDTH = 800
    MIN_HEIGHT = 500
    MODULE_COLUMN_WIDTH = 250
    DESCRIPTION_COLUMN_WIDTH = 200
    TREE_PROPORTION = 300  # Reduced from 400 to take up less width
    TABLE_PROPORTION = 700  # Increased from 600 to give more space to table

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

        # Initialize color scheme and style generator
        self.color_scheme = PyQt6ColorScheme()
        self.style_generator = StyleSheetGenerator(self.color_scheme)

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
        """Load ALL functions from registries (not just FUNC_REGISTRY subset)."""
        # Check if we have cached metadata
        if FunctionSelectorDialog._metadata_cache is not None:
            logger.debug("Using cached function metadata")
            self.all_functions_metadata = FunctionSelectorDialog._metadata_cache
            self.filtered_functions = self.all_functions_metadata.copy()
            return

        # Load ALL functions from registries directly
        logger.info("Loading ALL functions from registries")

        # Use existing RegistryService (already has caching and discovery)
        unified_functions = RegistryService.get_all_functions_with_metadata()

        self.all_functions_metadata = {}

        # Convert FunctionMetadata to dict format for UI compatibility
        # Handle composite keys (backend:function_name) from registry service
        for composite_key, metadata in unified_functions.items():
            # Extract backend and function name from composite key
            if ':' in composite_key:
                backend, func_name = composite_key.split(':', 1)
            else:
                # Fallback for non-composite keys
                backend = metadata.registry.library_name if metadata.registry else 'unknown'
                func_name = composite_key

            self.all_functions_metadata[composite_key] = {
                'name': metadata.name,
                'func': metadata.func,
                'module': metadata.module,
                'contract': metadata.contract,
                'tags': metadata.tags,
                'doc': metadata.doc,
                'backend': metadata.get_memory_type(),  # Actual memory type (cupy, numpy, etc.)
                'registry': metadata.get_registry_name(),  # Registry source (openhcs, skimage, etc.)
                'metadata': metadata  # Store full metadata for access to new methods
            }

        # Cache the results for future use
        FunctionSelectorDialog._metadata_cache = self.all_functions_metadata
        logger.info(f"Loaded {len(self.all_functions_metadata)} functions from all registries")



        self.filtered_functions = self.all_functions_metadata.copy()

    def populate_module_tree(self):
        """Populate the module tree with hierarchical function organization based purely on module paths."""
        self.module_tree.clear()

        # Build hierarchical structure directly from module paths
        module_hierarchy = {}
        for func_name, metadata in self.all_functions_metadata.items():
            module_path = self._extract_module_path(metadata)
            # Build hierarchical structure by splitting module path on '.'
            self._add_function_to_hierarchy(module_hierarchy, module_path, func_name)

        # Build tree structure directly from module hierarchy (no library grouping)
        self._build_module_hierarchy_tree(self.module_tree, module_hierarchy, [], is_root=True)

    def _update_filtered_view(self, filtered_functions: Dict[str, Any], filter_description: str = ""):
        """Mathematical simplification: factor out common filter update pattern (RST principle)."""
        self.filtered_functions = filtered_functions
        self.populate_function_table(self.filtered_functions)

        # Create unified count display
        total_count = len(self.all_functions_metadata)
        filtered_count = len(self.filtered_functions)
        count_text = f"Functions: {filtered_count}/{total_count}"
        if filter_description:
            count_text += f" ({filter_description})"

        self.function_count_label.setText(count_text)

        # Clear selection when filtering
        self._set_selection_state(None, False)

    def _set_selection_state(self, function: Optional[Callable], enabled: bool):
        """Mathematical simplification: factor out common button state logic (RST principle)."""
        self.selected_function = function
        self.select_btn.setEnabled(enabled)

    def _extract_function_from_item(self, item) -> Optional[Callable]:
        """Mathematical simplification: factor out common data extraction pattern (RST principle)."""
        if not item:
            return None
        data = item.data(Qt.ItemDataRole.UserRole)
        return data.get("func") if data else None

    def _create_pane_widget(self, title: str, main_widget) -> QWidget:
        """Mathematical simplification: factor out common pane setup pattern (RST principle)."""
        pane_widget = QWidget()
        layout = QVBoxLayout(pane_widget)
        layout.setContentsMargins(0, 0, 0, 0)

        # Create title with consistent styling using color scheme
        title_label = QLabel(title)
        title_label.setStyleSheet(f"""
            font-weight: bold;
            background-color: {self.color_scheme.to_hex(self.color_scheme.input_bg)};
            color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
            padding: 5px;
        """)
        layout.addWidget(title_label)

        # Add main widget
        layout.addWidget(main_widget)

        return pane_widget

    def _determine_library(self, metadata) -> str:
        """Direct library determination using registry ownership (robust approach)."""
        func_name = metadata.get('name', '')
        module = metadata.get('module', '')

        # Use direct registry ownership lookup (eliminates pattern matching fragility)
        return LibraryDetector.get_function_library(func_name, module)

    def _extract_module_path(self, metadata) -> str:
        """Extract full module path from metadata for hierarchical tree building."""
        module = metadata.get('module', '')
        if not module:
            return 'unknown'

        # Return the full module path for hierarchical tree building
        return module

    def _add_function_to_hierarchy(self, hierarchy: dict, module_path: str, func_name: str):
        """Add a function to the hierarchical module structure."""
        if module_path == 'unknown':
            # Handle unknown modules
            if 'functions' not in hierarchy:
                hierarchy['functions'] = []
            hierarchy['functions'].append(func_name)
            return

        # Split module path and build hierarchy
        parts = module_path.split('.')
        current_level = hierarchy

        for part in parts:
            if part not in current_level:
                current_level[part] = {}
            current_level = current_level[part]

        # Add function to the deepest level
        if 'functions' not in current_level:
            current_level['functions'] = []
        current_level['functions'].append(func_name)

    def _count_functions_in_hierarchy(self, hierarchy: dict) -> int:
        """Count total functions in a hierarchical structure."""
        count = 0
        for key, value in hierarchy.items():
            if key == 'functions':
                count += len(value)
            elif isinstance(value, dict):
                count += self._count_functions_in_hierarchy(value)
        return count

    def _build_module_hierarchy_tree(self, parent_container, hierarchy: dict,
                                   module_path_parts: list, is_root: bool = False):
        """Recursively build the hierarchical module tree."""
        for key, value in hierarchy.items():
            if key == 'functions':
                # This level has functions - create a module node if there are functions
                if value:  # Only create node if there are functions
                    current_path = '.'.join(module_path_parts) if module_path_parts else 'unknown'
                    if is_root:
                        # For root level, add directly to tree widget
                        module_item = QTreeWidgetItem(parent_container)
                    else:
                        # For nested levels, add to parent item
                        module_item = QTreeWidgetItem(parent_container)
                    module_item.setText(0, f"{current_path} ({len(value)} functions)")
                    module_item.setData(0, Qt.ItemDataRole.UserRole, {
                        "type": "module",
                        "module": current_path,
                        "functions": value
                    })
            elif isinstance(value, dict):
                # This is a module part - create a tree node and recurse
                new_path_parts = module_path_parts + [key]

                # Count functions in this subtree
                subtree_function_count = self._count_functions_in_hierarchy(value)

                if is_root:
                    # For root level, add directly to tree widget
                    module_part_item = QTreeWidgetItem(parent_container)
                else:
                    # For nested levels, add to parent item
                    module_part_item = QTreeWidgetItem(parent_container)

                module_part_item.setText(0, f"{key} ({subtree_function_count} functions)")
                module_part_item.setData(0, Qt.ItemDataRole.UserRole, {
                    "type": "module_part",
                    "module_part": key,
                    "full_path": '.'.join(new_path_parts)
                })
                # Start collapsed - users can expand as needed
                module_part_item.setExpanded(False)

                # Recursively build subtree
                self._build_module_hierarchy_tree(module_part_item, value, new_path_parts, is_root=False)

    @classmethod
    def clear_metadata_cache(cls) -> None:
        """Clear the cached metadata to force re-discovery."""
        cls._metadata_cache = None
        RegistryService.clear_metadata_cache()
        logger.info("Function metadata cache cleared")
    
    def setup_ui(self):
        """Setup the dual-pane user interface with tree and table."""
        self.setWindowTitle("Select Function - Dual Pane View")
        self.setModal(True)
        self.resize(self.DEFAULT_WIDTH, self.DEFAULT_HEIGHT)
        self.setMinimumSize(self.MIN_WIDTH, self.MIN_HEIGHT)

        layout = QVBoxLayout(self)

        # Title
        title_label = QLabel("Select Function - Dual Pane View")
        title_font = QFont()
        title_font.setBold(True)
        title_font.setPointSize(12)
        title_label.setFont(title_font)
        title_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};")
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

        # Create tree widget with configuration
        self.module_tree = QTreeWidget()
        self.module_tree.setHeaderLabel("Module Structure")
        self.module_tree.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)

        # Enable deselection by clicking in empty space
        self.module_tree.mousePressEvent = self._tree_mouse_press_event

        # Create panes using factored pattern (RST principle)
        left_widget = self._create_pane_widget("Module Structure", self.module_tree)
        splitter.addWidget(left_widget)

        # Function table with enhanced columns - Backend shows memory type, Registry shows source
        self.function_table = QTableWidget()
        self.function_table.setColumnCount(7)
        self.function_table.setHorizontalHeaderLabels([
            "Name", "Module", "Backend", "Registry", "Contract", "Tags", "Description"
        ])

        # Configure table behavior
        self.function_table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.function_table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.function_table.setSortingEnabled(True)
        self.function_table.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)

        # Configure column widths - make all columns resizable and movable
        header = self.function_table.horizontalHeader()
        header.setSectionsMovable(True)  # Allow column reordering
        resize_modes = [
            QHeaderView.ResizeMode.Interactive,  # Name - resizable
            QHeaderView.ResizeMode.Interactive,  # Module - resizable
            QHeaderView.ResizeMode.Interactive,  # Backend - resizable
            QHeaderView.ResizeMode.Interactive,  # Contract - resizable
            QHeaderView.ResizeMode.Interactive,  # Tags - resizable
            QHeaderView.ResizeMode.Interactive   # Description - resizable (changed from Stretch)
        ]
        for col, mode in enumerate(resize_modes):
            header.setSectionResizeMode(col, mode)

        # Set specific column widths using constants (RST principle)
        column_widths = {1: self.MODULE_COLUMN_WIDTH, 5: self.DESCRIPTION_COLUMN_WIDTH}
        for col, width in column_widths.items():
            self.function_table.setColumnWidth(col, width)

        # Create right pane using factored pattern (RST principle)
        right_widget = self._create_pane_widget("Function Details", self.function_table)
        splitter.addWidget(right_widget)

        # Set splitter proportions using constants
        splitter.setSizes([self.TREE_PROPORTION, self.TABLE_PROPORTION])

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

        # Apply centralized styling
        self.setStyleSheet(
            self.style_generator.generate_dialog_style() + "\n" +
            self.style_generator.generate_tree_widget_style() + "\n" +
            self.style_generator.generate_table_widget_style() + "\n" +
            self.style_generator.generate_button_style()
        )

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

        for row, (composite_key, metadata) in enumerate(functions_metadata.items()):
            # Get backend (memory type) and registry separately
            backend = metadata.get('backend', 'unknown')
            registry = metadata.get('registry', 'unknown')

            # Format tags as comma-separated string
            tags_str = ", ".join(metadata.get('tags', [])) if metadata.get('tags') else ""

            # Truncate description for table display (more generous)
            doc = metadata.get('doc', '')
            description = doc[:150] + "..." if len(doc) > 150 else doc

            # Mathematical simplification: consolidate table item creation (RST principle)
            contract = metadata.get('contract')
            contract_name = contract.name if hasattr(contract, 'name') else str(contract) if contract else "unknown"

            # Create all table items using factored pattern - Backend shows memory type, Registry shows source
            items_data = [
                metadata.get('name', metadata.get('name', composite_key.split(':')[-1] if ':' in composite_key else composite_key)),
                metadata.get('module', 'unknown'),
                backend.title(),  # Memory type (cupy, numpy, etc.)
                registry.title(),  # Registry source (openhcs, skimage, etc.)
                contract_name,
                tags_str,
                description
            ]

            items = [QTableWidgetItem(data) for data in items_data]
            items[0].setData(Qt.ItemDataRole.UserRole, {"func": metadata.get('func'), "metadata": metadata})

            # Set all items in table using enumeration
            for col, item in enumerate(items):
                self.function_table.setItem(row, col, item)

            # Highlight current function if it matches
            if self.current_function and metadata.get('func') == self.current_function:
                self.function_table.selectRow(row)

        self.function_table.setSortingEnabled(True)  # Re-enable sorting
    
    def filter_functions(self, search_term: str):
        """Filter functions using shared search service (canonical code path)."""
        # Use shared search service for consistent behavior
        from openhcs.ui.shared.search_service import SearchService

        # Create searchable text extractor
        def create_searchable_text(metadata):
            """Create searchable text using functional approach."""
            contract = metadata.get('contract')
            contract_name = contract.name if hasattr(contract, 'name') else str(contract) if contract else ""

            # Functional approach: map fields to searchable strings
            searchable_fields = [
                metadata.get('name', ''),
                metadata.get('module', ''),
                contract_name,
                " ".join(metadata.get('tags', [])),
                metadata.get('doc', '')
            ]
            return " ".join(field for field in searchable_fields)

        # Create search service if not exists
        if not hasattr(self, '_search_service'):
            self._search_service = SearchService(
                all_items=self.all_functions_metadata,
                searchable_text_extractor=create_searchable_text
            )

        # Perform search using shared service
        filtered = self._search_service.filter(search_term)

        # Update view
        if len(search_term.strip()) == 0:
            self._update_filtered_view(filtered)
        elif len(search_term.strip()) >= SearchService.MIN_SEARCH_CHARS:
            self._update_filtered_view(filtered, f"search: '{search_term}'")

    def on_tree_selection_changed(self):
        """Handle tree selection using mathematical simplification (RST principle)."""
        selected_items = self.module_tree.selectedItems()

        # If no items selected, show all functions
        if not selected_items:
            self._update_filtered_view(self.all_functions_metadata, "showing all functions")
            return

        item = selected_items[0]
        data = item.data(0, Qt.ItemDataRole.UserRole)

        if data:
            node_type = data.get("type")

            # Mathematical simplification: factor out filtering logic
            if node_type == "module":
                module_functions = data.get("functions", [])
                filtered = {
                    name: metadata for name, metadata in self.all_functions_metadata.items()
                    if name in module_functions
                }
                self._update_filtered_view(filtered, "filtered by module")

            elif node_type == "module_part":
                # Filter by module part - find all functions whose modules start with this path
                module_part_path = data.get("full_path", "")
                filtered = {
                    name: metadata for name, metadata in self.all_functions_metadata.items()
                    if self._extract_module_path(metadata).startswith(module_part_path)
                }
                self._update_filtered_view(filtered, f"filtered by module part: {module_part_path}")
        else:
            # No data means show all functions
            self._update_filtered_view(self.all_functions_metadata, "showing all functions")

    def _tree_mouse_press_event(self, event):
        """Handle mouse press events on the tree to allow deselection."""
        # Get the item at the click position
        item = self.module_tree.itemAt(event.pos())

        if item is None:
            # Clicked in empty space - clear selection
            self.module_tree.clearSelection()
        else:
            # Clicked on an item - use default behavior
            QTreeWidget.mousePressEvent(self.module_tree, event)

    def on_table_selection_changed(self):
        """Handle table selection changes."""
        selected_items = self.function_table.selectedItems()
        if selected_items:
            # Get the first item in the selected row (name column)
            row = selected_items[0].row()
            name_item = self.function_table.item(row, 0)

            # Use factored extraction and state setting
            func = self._extract_function_from_item(name_item)
            self._set_selection_state(func, func is not None)
        else:
            self._set_selection_state(None, False)

    def on_table_double_click(self, item):
        """Handle table double-click using factored extraction (RST principle)."""
        if item:
            row = item.row()
            name_item = self.function_table.item(row, 0)
            func = self._extract_function_from_item(name_item)

            if func:
                self.selected_function = func
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
