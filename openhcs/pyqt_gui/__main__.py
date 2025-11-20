#!/usr/bin/env python3
"""
OpenHCS PyQt6 GUI - Module Entry Point

Allows running the PyQt6 GUI directly with:
    python -m openhcs.pyqt_gui

This is a convenience wrapper around the launch script.
"""

import sys
import logging

# CRITICAL: Check for SILENT mode BEFORE any other imports
# This must be at MODULE LEVEL to run before launch.py is imported
if '--log-level' in sys.argv:
    log_level_idx = sys.argv.index('--log-level')
    if log_level_idx + 1 < len(sys.argv) and sys.argv[log_level_idx + 1] == 'SILENT':
        # Disable ALL logging before any imports
        logging.disable(logging.CRITICAL)
        root_logger = logging.getLogger()
        root_logger.setLevel(logging.CRITICAL + 1)

def main():
    """Main entry point with graceful error handling for missing GUI dependencies."""
    try:
        # Import the main function from launch script
        from openhcs.pyqt_gui.launch import main as launch_main
        return launch_main()
    except ImportError as e:
        if 'PyQt6' in str(e) or 'pyqt_gui' in str(e):
            print("ERROR: PyQt6 GUI dependencies not installed.", file=sys.stderr)
            print("", file=sys.stderr)
            print("To install GUI dependencies, run:", file=sys.stderr)
            print("  pip install openhcs[gui]", file=sys.stderr)
            print("", file=sys.stderr)
            print("Or for full installation with viewers:", file=sys.stderr)
            print("  pip install openhcs[gui,viz]", file=sys.stderr)
            return 1
        else:
            raise


if __name__ == "__main__":
    sys.exit(main())
