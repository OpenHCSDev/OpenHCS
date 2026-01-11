"""
Core Log Utilities for pyqt-formgen.

Unified log discovery, classification, and monitoring utilities
shared between UI implementations.
"""

import logging
import time
from pathlib import Path
from typing import Optional, List
from dataclasses import dataclass

from pyqt_formgen.protocols import get_form_config

logger = logging.getLogger(__name__)


def _get_log_dir() -> Path:
    """Return configured log directory or default."""
    config = get_form_config()
    if config.log_dir:
        return Path(config.log_dir)
    return Path.home() / ".local" / "share" / "pyqt_formgen" / "logs"


def _get_log_prefixes() -> List[str]:
    """Return configured log prefixes or default."""
    config = get_form_config()
    return config.log_prefixes or ["pyqt_formgen_"]


def _match_prefixed(file_name: str, suffix: str) -> Optional[str]:
    """Return matching prefix for a file name if it starts with prefix+suffix."""
    for prefix in _get_log_prefixes():
        if file_name.startswith(f"{prefix}{suffix}"):
            return prefix
    return None


def get_current_log_file_path() -> str:
    """Get the current log file path from the logging system."""
    try:
        # Get the root logger and find the FileHandler
        root_logger = logging.getLogger()
        for handler in root_logger.handlers:
            if isinstance(handler, logging.FileHandler):
                return handler.baseFilename

        # Fallback: try to get from configured logger name
        config = get_form_config()
        if config.log_root_logger_name:
            root_named_logger = logging.getLogger(config.log_root_logger_name)
            for handler in root_named_logger.handlers:
                if isinstance(handler, logging.FileHandler):
                    return handler.baseFilename

        # Last resort: create a default path
        log_dir = _get_log_dir()
        log_dir.mkdir(parents=True, exist_ok=True)
        prefix = (_get_log_prefixes() or ["pyqt_formgen_"])[0]
        return str(log_dir / f"{prefix}subprocess_{int(time.time())}.log")

    except Exception as e:
        logger.error(f"Failed to get current log file path: {e}")
        raise RuntimeError(f"Could not determine log file path: {e}")


@dataclass
class LogFileInfo:
    """Information about a discovered log file."""
    path: Path
    log_type: str  # "tui", "main", "worker", "unknown"
    worker_id: Optional[str] = None
    display_name: Optional[str] = None

    def __post_init__(self):
        """Generate display name if not provided."""
        if not self.display_name:
            if self.log_type == "tui":
                self.display_name = "Main Process"
            elif self.log_type == "main":
                self.display_name = "Main Subprocess"
            elif self.log_type == "worker" and self.worker_id:
                self.display_name = f"Worker {self.worker_id}"
            else:
                self.display_name = self.path.name


def discover_logs(base_log_path: Optional[str] = None, include_main_log: bool = True,
                 log_directory: Optional[Path] = None) -> List[LogFileInfo]:
    """
    Discover application log files and return as classified LogFileInfo objects.

    Args:
        base_log_path: Base path for specific subprocess logs (optional)
        include_main_log: Whether to include the current main process log
        log_directory: Directory to search (defaults to configured log directory)

    Returns:
        List of LogFileInfo objects for discovered log files
    """
    discovered_logs = []

    # Include current main process log if requested
    if include_main_log:
        try:
            main_log_path = get_current_log_file_path()
            main_log = Path(main_log_path)
            if main_log.exists():
                log_info = classify_log_file(main_log, base_log_path, include_main_log)
                discovered_logs.append(log_info)
        except Exception:
            pass  # Main log not available, continue

    # Discover subprocess logs if base_log_path is provided
    if base_log_path:
        base_path = Path(base_log_path)
        log_dir = base_path.parent
        if log_dir.exists():
            for log_file in log_dir.glob("*.log"):
                if is_relevant_log_file(log_file, base_log_path):
                    log_info = classify_log_file(log_file, base_log_path, include_main_log)
                    discovered_logs.append(log_info)

    # Discover all logs if no specific base_log_path
    elif log_directory or not base_log_path:
        if log_directory is None:
            log_directory = _get_log_dir()

        if log_directory.exists():
            for log_file in log_directory.glob("*.log"):
                if is_app_log_file(log_file) and log_file not in [log.path for log in discovered_logs]:
                    # Infer base_log_path for proper classification
                    inferred_base = infer_base_log_path(log_file) if 'subprocess_' in log_file.name else None
                    log_info = classify_log_file(log_file, inferred_base, include_main_log)
                    discovered_logs.append(log_info)

    return discovered_logs


def classify_log_file(log_path: Path, base_log_path: Optional[str] = None, include_tui_log: bool = True) -> LogFileInfo:
    """
    Pure function: Classify a log file and extract metadata.

    Args:
        log_path: Path to log file
        base_log_path: Base path for subprocess log files
        include_tui_log: Whether to check for TUI log classification

    Returns:
        LogFileInfo with classification and metadata
    """
    file_name = log_path.name

    # Check if it's the current TUI log
    if include_tui_log:
        try:
            tui_log_path = get_current_log_file_path()
            if log_path == Path(tui_log_path):
                return LogFileInfo(log_path, "tui", display_name="Main Process")
        except RuntimeError:
            pass  # TUI log not found, continue with other classification

    # Check for ZMQ server logs (<prefix>zmq_server_port_{port}_{timestamp}.log)
    prefix = _match_prefixed(file_name, "zmq_server_port_")
    if prefix:
        # Extract port from filename
        parts = file_name.replace(f'{prefix}zmq_server_port_', '').replace('.log', '').split('_')
        port = parts[0] if parts else 'unknown'
        return LogFileInfo(log_path, "zmq_server", display_name=f"ZMQ Server (port {port})")

    # Check for ZMQ worker logs
    if file_name.startswith('zmq_worker_exec_'):
        # Extract execution ID and worker PID
        parts = file_name.replace('zmq_worker_exec_', '').replace('.log', '').split('_worker_')
        if len(parts) == 2:
            exec_id_short = parts[0][:8]  # First 8 chars of UUID
            worker_pid = parts[1].split('_')[0]  # PID is first part after _worker_
            return LogFileInfo(log_path, "zmq_worker", worker_pid, display_name=f"ZMQ Worker {worker_pid}")

    # Check for Napari viewer logs
    if file_name.startswith('napari_detached_port_'):
        port = file_name.replace('napari_detached_port_', '').replace('.log', '')
        return LogFileInfo(log_path, "napari", display_name=f"Napari Viewer (port {port})")

    # Check subprocess logs if base_log_path is provided
    if base_log_path:
        base_name = Path(base_log_path).name

        # Check if it's the main subprocess log: exact match
        if file_name == f"{base_name}.log":
            return LogFileInfo(log_path, "main", display_name="Main Subprocess")

        # Check if it's a worker log: {base_name}_worker_*.log
        if file_name.startswith(f"{base_name}_worker_") and file_name.endswith('.log'):
            # Extract worker ID (everything between _worker_ and .log)
            worker_part = file_name[len(f"{base_name}_worker_"):-4]  # Remove .log suffix
            worker_id = worker_part.split('_')[0]  # Take first part before any additional underscores
            return LogFileInfo(log_path, "worker", worker_id, display_name=f"Worker {worker_id}")

    # Unknown or malformed log file
    logger.debug(f"Unrecognized log file pattern: {file_name}")
    return LogFileInfo(log_path, "unknown")


def is_relevant_log_file(file_path: Path, base_log_path: Optional[str]) -> bool:
    """
    Check if file is a relevant log file for monitoring.

    Args:
        file_path: Path to file to check
        base_log_path: Base path for subprocess log files

    Returns:
        bool: True if file is relevant for monitoring
    """
    if not base_log_path:
        return False

    base_name = Path(base_log_path).name
    file_name = file_path.name

    # Check if it matches our patterns
    if file_name == f"{base_name}.log":
        return True

    if file_name.startswith(f"{base_name}_worker_") and file_name.endswith('.log'):
        return True

    return False


def is_app_log_file(file_path: Path) -> bool:
    """
    Check if a file is a recognized application log file.

    Args:
        file_path: Path to file to check

    Returns:
        bool: True if file matches configured log prefixes
    """
    if not file_path.name.endswith('.log'):
        return False

    file_name = file_path.name

    # App log patterns based on configured prefixes, plus common auxiliary logs
    prefixes = _get_log_prefixes()
    extra_patterns = [
        "pyqt_gui_subprocess_",
        "zmq_worker_",
        "napari_detached_",
    ]
    patterns = [*prefixes, *extra_patterns]

    return any(file_name.startswith(pattern) for pattern in patterns)


def infer_base_log_path(file_path: Path) -> str:
    """
    Infer the base log path from a subprocess log file name.

    Args:
        file_path: Path to subprocess log file

    Returns:
        str: Inferred base log path
    """
    file_name = file_path.name

    # Handle worker logs: remove _worker_* suffix
    if '_worker_' in file_name:
        base_name = file_name.split('_worker_')[0]
    else:
        # Handle main subprocess logs: remove .log extension
        base_name = file_path.stem

    return str(file_path.parent / base_name)


# Backward compatibility alias
is_openhcs_log_file = is_app_log_file
