"""
OpenHCS PyQt6 GUI Implementation

Complete PyQt6 migration of the OpenHCS Textual TUI with full feature parity.
Provides native desktop integration while preserving all existing functionality.
"""

import sys
import logging

# CRITICAL: Check for SILENT mode BEFORE any OpenHCS imports
# This must be at MODULE LEVEL to run before main.py is imported
if '--log-level' in sys.argv:
    log_level_idx = sys.argv.index('--log-level')
    if log_level_idx + 1 < len(sys.argv) and sys.argv[log_level_idx + 1] == 'SILENT':
        # Disable ALL logging before any imports
        logging.disable(logging.CRITICAL)
        root_logger = logging.getLogger()
        root_logger.setLevel(logging.CRITICAL + 1)

__version__ = "1.0.0"
__author__ = "OpenHCS Development Team"

from openhcs.pyqt_gui.main import OpenHCSMainWindow
from openhcs.pyqt_gui.app import OpenHCSPyQtApp

__all__ = [
    "OpenHCSMainWindow",
    "OpenHCSPyQtApp"
]
