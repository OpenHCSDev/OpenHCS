#!/usr/bin/env python3
"""
OpenHCS PyQt6 GUI - Module Entry Point

Allows running the PyQt6 GUI directly with:
    python -m openhcs.pyqt_gui

This is a convenience wrapper around the launch script.
"""

import sys


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
