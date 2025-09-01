"""
Experimental analysis backend system for OpenHCS.

This module provides a unified, registry-based system for processing experimental
analysis data from multiple microscope formats (CX5, MetaXpress) with automatic
format detection, configuration management, and statistical analysis.

Key components:
- Format registry system for automatic microscope format detection
- Unified analysis engine with configurable processing pipelines
- Integration with OpenHCS configuration and registry systems
- Backward compatibility with existing experimental analysis workflows
"""

from .format_registry import MicroscopeFormatRegistryBase, MicroscopeFormatConfig
from .format_registry_service import FormatRegistryService
from .unified_analysis_engine import ExperimentalAnalysisEngine

__all__ = [
    'MicroscopeFormatRegistryBase',
    'MicroscopeFormatConfig', 
    'FormatRegistryService',
    'ExperimentalAnalysisEngine'
]
