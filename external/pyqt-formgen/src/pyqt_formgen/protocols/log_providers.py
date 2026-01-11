"""Protocols for log discovery and server scanning."""

from typing import Protocol, Optional, List
from pathlib import Path

from pyqt_formgen.core.log_utils import LogFileInfo


class LogDiscoveryProvider(Protocol):
    """Protocol for discovering log files and current log path."""

    def get_current_log_path(self) -> Path:
        """Return current log file path."""
        ...

    def discover_logs(
        self,
        base_log_path: Optional[str] = None,
        include_main_log: bool = True,
        log_directory: Optional[Path] = None,
    ) -> List[LogFileInfo]:
        """Return discovered logs."""
        ...


class ServerScanProvider(Protocol):
    """Protocol for discovering server logs (e.g., via port scans)."""

    def scan_for_server_logs(self) -> List[LogFileInfo]:
        """Return logs discovered from live servers."""
        ...


_log_discovery_provider: Optional[LogDiscoveryProvider] = None
_server_scan_provider: Optional[ServerScanProvider] = None


def register_log_discovery_provider(provider: LogDiscoveryProvider) -> None:
    """Register a global log discovery provider."""
    global _log_discovery_provider
    _log_discovery_provider = provider


def get_log_discovery_provider() -> Optional[LogDiscoveryProvider]:
    """Get the registered log discovery provider."""
    return _log_discovery_provider


def register_server_scan_provider(provider: ServerScanProvider) -> None:
    """Register a global server scan provider."""
    global _server_scan_provider
    _server_scan_provider = provider


def get_server_scan_provider() -> Optional[ServerScanProvider]:
    """Get the registered server scan provider."""
    return _server_scan_provider

