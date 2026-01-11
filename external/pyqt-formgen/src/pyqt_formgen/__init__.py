"""
pyqt-formgen: React-quality reactive form generation framework for PyQt6.

A comprehensive UI framework for building type-safe, reactive forms with PyQt6.
Extracted from OpenHCS for general-purpose use.

Architecture:
- Tier 1 (Core): Pure PyQt6 utilities with zero external deps beyond PyQt6
- Tier 2 (Protocols): Widget ABCs and adapters
- Tier 3 (Services): Reusable service layer
- Tier 4 (Forms): ParameterFormManager with ObjectState integration

Key Features:
- Type-based widget creation from dataclasses
- ObjectState integration for lazy configuration
- ABC-based widget protocols (no duck typing)
- Game-engine inspired flash animation system
- React-style lifecycle hooks
- Cross-window reactive updates
"""

__version__ = "0.1.0"

# Public API will be populated as modules are added
__all__ = [
    "__version__",
]
