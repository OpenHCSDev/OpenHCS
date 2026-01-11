"""
Shared helper for making splitters collapsible with double-click toggle.

Used by ConfigWindow and StepParameterEditor to provide consistent
tree panel collapse/expand behavior.
"""

import logging
from PyQt6.QtCore import QEvent, QObject
from PyQt6.QtWidgets import QSplitter

logger = logging.getLogger(__name__)


class CollapsibleSplitterHelper:
    """Helper for adding double-click toggle to splitter handles."""
    
    def __init__(self, splitter: QSplitter, left_panel_index: int = 0):
        """
        Initialize the collapsible splitter helper.
        
        Args:
            splitter: The QSplitter to make collapsible
            left_panel_index: Index of the left panel (default 0)
        """
        self.splitter = splitter
        self.left_panel_index = left_panel_index
        self._tree_visible = True
        self._tree_last_size = 300  # Default last size
        
        # Install event filter on splitter handle
        self._install_handle_filter()
    
    def _install_handle_filter(self):
        """Install event filter on splitter handle for double-click toggle."""
        class SplitterHandleFilter(QObject):
            """Event filter for splitter handle to detect double-clicks."""
            def __init__(self, helper):
                super().__init__()
                self.helper = helper
            
            def eventFilter(self, obj, event):
                if event.type() == QEvent.Type.MouseButtonDblClick:
                    self.helper.toggle_visibility()
                    return True
                return False
        
        # Get the splitter handle (index 1 is the handle between widgets 0 and 1)
        handle = self.splitter.handle(1)
        if handle:
            self._handle_filter = SplitterHandleFilter(self)
            handle.installEventFilter(self._handle_filter)
    
    def toggle_visibility(self):
        """Toggle left panel visibility by collapsing/expanding."""
        sizes = self.splitter.sizes()
        
        if self._tree_visible and sizes[self.left_panel_index] > 0:
            # Panel is visible - collapse it
            self._tree_last_size = sizes[self.left_panel_index]  # Remember current size
            total = sum(sizes)
            new_sizes = [0] * len(sizes)
            new_sizes[self.left_panel_index] = 0
            # Give all space to other panels
            remaining = total
            for i in range(len(sizes)):
                if i != self.left_panel_index:
                    new_sizes[i] = remaining
                    break
            self.splitter.setSizes(new_sizes)
            self._tree_visible = False
            logger.debug("Collapsed left panel")
        else:
            # Panel is collapsed - expand it
            total = sum(sizes)
            new_left_size = min(self._tree_last_size, total - 100)  # Ensure right panel has at least 100px
            new_sizes = [0] * len(sizes)
            new_sizes[self.left_panel_index] = new_left_size
            # Give remaining space to other panels
            remaining = total - new_left_size
            for i in range(len(sizes)):
                if i != self.left_panel_index:
                    new_sizes[i] = remaining
                    break
            self.splitter.setSizes(new_sizes)
            self._tree_visible = True
            logger.debug(f"Expanded left panel to {new_left_size}px")
    
    def set_initial_size(self, size: int):
        """Set the initial size to remember when collapsed."""
        self._tree_last_size = size

