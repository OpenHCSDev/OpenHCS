"""
Shared reorderable QListWidget for drag-and-drop reordering.

Single source of truth for reorderable list widgets across PipelineEditor,
PlateManager, and other widgets.
"""

from PyQt6.QtWidgets import QListWidget
from PyQt6.QtCore import pyqtSignal, Qt


class ReorderableListWidget(QListWidget):
    """Custom QListWidget that properly handles drag and drop reordering.
    
    Emits a signal when items are moved so the parent can update the data model.
    This is a shared implementation used by both PipelineEditor and PlateManager.
    """
    
    items_reordered = pyqtSignal(int, int)  # from_index, to_index
    
    def __init__(self, parent=None):
        """Initialize reorderable list widget.
        
        Args:
            parent: Parent widget
        """
        super().__init__(parent)
        self.setDragDropMode(QListWidget.DragDropMode.InternalMove)
        self.setDefaultDropAction(Qt.DropAction.MoveAction)
        self.setSelectionMode(QListWidget.SelectionMode.ExtendedSelection)
        
        # Enable word wrap for multiline items
        self.setWordWrap(True)
        self.setTextElideMode(Qt.TextElideMode.ElideNone)
    
    def dropEvent(self, event):
        """Handle drop event and emit signal with indices."""
        # Get the source index before the drop
        source_items = self.selectedItems()
        if not source_items:
            super().dropEvent(event)
            return
        
        source_index = self.row(source_items[0])
        
        # Perform the drop
        super().dropEvent(event)
        
        # Get the target index after the drop
        target_index = self.row(source_items[0])
        
        # Only emit signal if position actually changed
        if source_index != target_index:
            self.items_reordered.emit(source_index, target_index)

