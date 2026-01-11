"""Tests for core utilities."""

import pytest


def test_debounce_timer_basic(qapp):
    """Test DebounceTimer basic functionality."""
    from pyqt_formgen.core import DebounceTimer
    
    called = []
    def handler():
        called.append(1)
    
    timer = DebounceTimer(delay_ms=50, handler=handler)
    assert len(called) == 0
    
    # Basic test - timer exists
    assert timer is not None


def test_reorderable_list_widget(qapp):
    """Test ReorderableListWidget creation."""
    from pyqt_formgen.core import ReorderableListWidget
    
    widget = ReorderableListWidget()
    assert widget is not None
