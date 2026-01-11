"""
Image table browser widget using AbstractTableBrowser.

Displays file metadata in a searchable table with dynamic columns.
Used as the table portion of ImageBrowserWidget.
"""

from typing import Any, Dict, List, Optional

from pyqt_formgen.theming import ColorScheme
from pyqt_formgen.widgets.shared.abstract_table_browser import (
    AbstractTableBrowser, ColumnDef
)


class ImageTableBrowser(AbstractTableBrowser[Dict[str, Any]]):
    """
    Table browser for image/file metadata.
    
    Dynamic columns: Filename + metadata keys from file parser.
    Multi-select mode for batch streaming operations.
    """
    
    def __init__(self, color_scheme: Optional[ColorScheme] = None, parent=None):
        # Columns are dynamic - start with just Filename
        self._metadata_keys: List[str] = []
        super().__init__(color_scheme=color_scheme, selection_mode='multi', parent=parent)
    
    def set_metadata_keys(self, metadata_keys: List[str]):
        """Set the metadata keys that define dynamic columns. Call before set_items()."""
        self._metadata_keys = metadata_keys
        self.reconfigure_columns()
    
    def get_columns(self) -> List[ColumnDef]:
        """Dynamic column definitions based on metadata keys."""
        columns = [ColumnDef(name="Filename", key="filename", width=200)]
        
        for key in self._metadata_keys:
            display_name = key.replace('_', ' ').title()
            columns.append(ColumnDef(name=display_name, key=key))
        
        return columns
    
    def extract_row_data(self, item: Dict[str, Any]) -> List[str]:
        """Extract display values from file metadata dict."""
        # First column is filename (stored as key, passed via item)
        row = [item.get('filename', 'unknown')]
        
        # Remaining columns are metadata values
        for key in self._metadata_keys:
            value = item.get(key, 'N/A')
            row.append(self._format_value(key, value))
        
        return row
    
    def _format_value(self, key: str, value: Any) -> str:
        """Format a metadata value for display."""
        if value is None:
            return 'N/A'
        return str(value)
    
    def get_searchable_text(self, item: Dict[str, Any]) -> str:
        """Return searchable text for file metadata."""
        parts = [item.get('filename', '')]
        
        for key in self._metadata_keys:
            value = item.get(key)
            if value is not None:
                parts.append(str(value))
        
        return " ".join(parts)
    
    def get_search_placeholder(self) -> str:
        return "Search files..."
