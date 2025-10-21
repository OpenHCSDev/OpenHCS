"""
Shared UI components and services.

This module provides framework-agnostic UI utilities and services
that can be used across different UI frameworks (PyQt, Textual, etc.).
"""

# Avoid circular imports - don't import SignatureAnalyzer at module level
from openhcs.ui.shared.pattern_data_manager import PatternDataManager
from openhcs.ui.shared.system_monitor_core import SystemMonitorCore
from openhcs.ui.shared.pattern_file_service import PatternFileService

__all__ = [
    'PatternDataManager',
    'SystemMonitorCore',
    'PatternFileService',
]

