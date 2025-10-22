"""
OpenHCS PyQt6 Windows

Window components for the OpenHCS PyQt6 GUI application.
All windows migrated from Textual TUI with full feature parity.
"""

from openhcs.pyqt_gui.windows.base_form_dialog import BaseFormDialog
from openhcs.pyqt_gui.windows.config_window import ConfigWindow
from openhcs.pyqt_gui.windows.help_window import HelpWindow
from openhcs.pyqt_gui.windows.dual_editor_window import DualEditorWindow
from openhcs.pyqt_gui.windows.file_browser_window import FileBrowserWindow
from openhcs.pyqt_gui.windows.synthetic_plate_generator_window import SyntheticPlateGeneratorWindow

__all__ = [
    "BaseFormDialog",
    "ConfigWindow",
    "HelpWindow",
    "DualEditorWindow",
    "FileBrowserWindow",
    "SyntheticPlateGeneratorWindow"
]
