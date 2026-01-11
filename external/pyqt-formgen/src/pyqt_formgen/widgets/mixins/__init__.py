"""
PyQt6 Widget Utilities

Shared utility functions for PyQt6 widgets, mirroring patterns from the Textual TUI.
"""

from pyqt_formgen.widgets.mixins.selection_preservation_mixin import (
    preserve_selection_during_update,
    restore_selection_by_id,
    handle_selection_change_with_prevention
)
from pyqt_formgen.widgets.mixins.cross_window_preview_mixin import (
    CrossWindowPreviewMixin,
)

__all__ = [
    "preserve_selection_during_update",
    "restore_selection_by_id",
    "handle_selection_change_with_prevention",
    "CrossWindowPreviewMixin",
]
