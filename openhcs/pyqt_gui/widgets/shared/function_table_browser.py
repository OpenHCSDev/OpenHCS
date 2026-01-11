"""
Function table browser widget using AbstractTableBrowser.

Displays function metadata in a searchable table with static columns.
Used as the table portion of FunctionSelectorDialog.
"""

from typing import Any, Dict, List, Optional

from pyqt_formgen.theming import ColorScheme
from pyqt_formgen.widgets.shared.abstract_table_browser import (
    AbstractTableBrowser, ColumnDef
)


class FunctionTableBrowser(AbstractTableBrowser[Dict[str, Any]]):
    """
    Table browser for function metadata.
    
    Static columns: Name, Module, Backend, Registry, Contract, Tags, Description
    Single-select mode.
    """
    
    # Column widths
    MODULE_WIDTH = 250
    DESCRIPTION_WIDTH = 300
    
    def __init__(self, color_scheme: Optional[ColorScheme] = None, parent=None):
        super().__init__(color_scheme=color_scheme, selection_mode='single', parent=parent)
    
    def get_columns(self) -> List[ColumnDef]:
        """Static column definitions for function table."""
        return [
            ColumnDef(name="Name", key="name", width=150),
            ColumnDef(name="Module", key="module", width=self.MODULE_WIDTH),
            ColumnDef(name="Backend", key="backend", width=80),
            ColumnDef(name="Registry", key="registry", width=80),
            ColumnDef(name="Contract", key="contract", width=100),
            ColumnDef(name="Tags", key="tags", width=100),
            ColumnDef(name="Description", key="doc", width=self.DESCRIPTION_WIDTH),
        ]
    
    def extract_row_data(self, item: Dict[str, Any]) -> List[str]:
        """Extract display values from function metadata dict."""
        # Get contract name
        contract = item.get('contract')
        contract_name = contract.name if hasattr(contract, 'name') else str(contract) if contract else "unknown"
        
        # Format tags
        tags = item.get('tags', [])
        tags_str = ", ".join(tags) if tags else ""
        
        # Truncate description
        doc = item.get('doc', '')
        description = doc[:150] + "..." if len(doc) > 150 else doc
        
        return [
            item.get('name', 'unknown'),
            item.get('module', 'unknown'),
            item.get('backend', 'unknown').title(),
            item.get('registry', 'unknown').title(),
            contract_name,
            tags_str,
            description,
        ]
    
    def get_searchable_text(self, item: Dict[str, Any]) -> str:
        """Return searchable text for function metadata."""
        contract = item.get('contract')
        contract_name = contract.name if hasattr(contract, 'name') else str(contract) if contract else ""
        
        tags = item.get('tags', [])
        
        return " ".join([
            item.get('name', ''),
            item.get('module', ''),
            contract_name,
            " ".join(tags),
            item.get('doc', ''),
        ])
    
    def get_search_placeholder(self) -> str:
        return "Search functions by name, module, contract, or tags..."
