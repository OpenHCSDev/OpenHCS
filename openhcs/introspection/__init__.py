"""
OpenHCS Introspection Package

Pure Python reflection and introspection utilities for analyzing:
- Function and method signatures
- Dataclass fields and types
- Parameter information extraction
- Docstring parsing
- Type hint resolution

This package is framework-agnostic and has minimal dependencies on OpenHCS-specific
code (only lazy imports for config type resolution). It can be used by:
- config_framework (for cache warming)
- UI layers (for form generation)
- Processing backends (for function annotation enhancement)
- Any code that needs to introspect Python objects

Key Components:
- SignatureAnalyzer: Extract parameter info from functions/dataclasses
- UnifiedParameterAnalyzer: Unified interface for all parameter sources
"""

from openhcs.introspection.signature_analyzer import (
    SignatureAnalyzer,
    ParameterInfo,
    DocstringInfo,
    DocstringExtractor,
)
from openhcs.introspection.unified_parameter_analyzer import (
    UnifiedParameterAnalyzer,
    UnifiedParameterInfo,
)

__all__ = [
    # Signature analysis
    'SignatureAnalyzer',
    'ParameterInfo',
    'DocstringInfo',
    'DocstringExtractor',
    # Unified analysis
    'UnifiedParameterAnalyzer',
    'UnifiedParameterInfo',
]

