"""
OpenHCS: A library for stitching microscopy images.

This module provides the public API for OpenHCS.
It re-exports only the intended public symbols from openhcs.ez.api
and does NOT import from internal modules in a way that triggers
registrations or other side-effects.
"""

import logging
import os
import sys
import platform
from pathlib import Path

__version__ = "0.5.0"

# Configure polystore defaults for OpenHCS integration
os.environ.setdefault("POLYSTORE_METADATA_FILENAME", "openhcs_metadata.json")
os.environ.setdefault("POLYSTORE_ZMQ_APP_NAME", "openhcs")
os.environ.setdefault("POLYSTORE_ZMQ_IPC_PREFIX", "openhcs-zmq")
os.environ.setdefault("POLYSTORE_ZMQ_IPC_DIR", "ipc")
os.environ.setdefault("POLYSTORE_ZMQ_IPC_EXT", ".sock")
os.environ.setdefault("POLYSTORE_ZMQ_CONTROL_OFFSET", "1000")
os.environ.setdefault("POLYSTORE_ZMQ_DEFAULT_PORT", "7777")
os.environ.setdefault("POLYSTORE_ZMQ_ACK_PORT", "7555")
if os.getenv("OPENHCS_SUBPROCESS_NO_GPU") == "1":
    os.environ.setdefault("POLYSTORE_SUBPROCESS_NO_GPU", "1")

# Prefer local external package checkouts when running from source
_repo_root = Path(__file__).resolve().parent.parent
_external_root = _repo_root / "external"
if _external_root.exists():
    for _pkg_dir in sorted(_external_root.iterdir()):
        if not _pkg_dir.is_dir():
            continue
        _src_dir = _pkg_dir / "src"
        if not _src_dir.is_dir():
            continue
        # Only add src dirs that look like packages (contain at least one __init__.py)
        if not any((p / "__init__.py").is_file() for p in _src_dir.iterdir() if p.is_dir()):
            continue
        _src_str = str(_src_dir)
        if _src_str not in sys.path:
            sys.path.insert(0, _src_str)

# Force UTF-8 encoding for stdout/stderr on Windows
# This ensures emoji and Unicode characters work in console output
if platform.system() == 'Windows':
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8')
    if hasattr(sys.stderr, 'reconfigure'):
        sys.stderr.reconfigure(encoding='utf-8')

# Monkey patch logging.FileHandler to default to UTF-8 encoding
# This ensures all log files support emojis and Unicode characters
_original_file_handler_init = logging.FileHandler.__init__

def _utf8_file_handler_init(self, filename, mode='a', encoding='utf-8', delay=False, errors=None):
    """FileHandler.__init__ with UTF-8 encoding as default."""
    return _original_file_handler_init(self, filename, mode, encoding, delay, errors)

logging.FileHandler.__init__ = _utf8_file_handler_init

# Set up basic logging configuration if none exists
# This ensures INFO level logging works when testing outside the TUI
def _ensure_basic_logging():
    """Ensure basic logging is configured if no configuration exists."""
    root_logger = logging.getLogger()

    # Only configure if no handlers exist and level is too high
    if not root_logger.handlers and root_logger.level > logging.INFO:
        # Set up basic console logging at INFO level
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        )

# Configure basic logging on import
_ensure_basic_logging()

# Re-export public API
#from openhcs.ez.api import (
#    # Core functions
#    initialize,
#    create_config,
#    run_pipeline,
#    stitch_images,
#
#    # Key types
#    PipelineConfig,
#    BackendConfig,
#    MISTConfig,
#    VirtualPath,
#    PhysicalPath,
#)
#
__all__ = [
    # Core functions
    "initialize",
    "create_config",
    "run_pipeline",
    "stitch_images",

    # Key types
    "PipelineConfig",
    "BackendConfig",
    "MISTConfig",
    "VirtualPath",
    "PhysicalPath",
]
