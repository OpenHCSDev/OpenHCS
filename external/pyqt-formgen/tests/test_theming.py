"""Tests for theming system."""

import pytest


def test_color_scheme_creation():
    """Test ColorScheme instantiation."""
    from pyqt_formgen.theming import ColorScheme
    
    scheme = ColorScheme()
    assert scheme is not None
    assert hasattr(scheme, 'to_hex')


def test_palette_manager(qapp):
    """Test PaletteManager creation."""
    from pyqt_formgen.theming import PaletteManager, ColorScheme
    
    scheme = ColorScheme()
    manager = PaletteManager(scheme)
    assert manager is not None
