"""Tests for widget protocols."""

import pytest


def test_line_edit_adapter(qapp):
    """Test LineEditAdapter implements protocols."""
    from pyqt_formgen.protocols import LineEditAdapter, ValueGettable, ValueSettable
    
    adapter = LineEditAdapter()
    assert isinstance(adapter, ValueGettable)
    assert isinstance(adapter, ValueSettable)
    
    # Test value roundtrip
    adapter.set_value("test")
    assert adapter.get_value() == "test"
