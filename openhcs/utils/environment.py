"""
Environment detection utilities for OpenHCS.

Provides functions for detecting runtime environment characteristics
like headless mode, CI environments, and other context-specific settings.
"""
import os


def is_headless_mode() -> bool:
    """
    Detect headless/CI contexts where viz deps should not be required at import time.

    CPU-only mode does NOT imply headless - you can run CPU mode with napari.
    Only CI or explicit OPENHCS_HEADLESS flag triggers headless mode.

    Returns:
        True if running in headless mode (CI or explicitly set), False otherwise
    """
    try:
        if os.getenv('CI', '').lower() == 'true':
            return True
        if os.getenv('OPENHCS_HEADLESS', '').lower() == 'true':
            return True
    except Exception:
        pass
    return False

