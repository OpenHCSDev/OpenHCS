"""pytest configuration and fixtures for pyqt-formgen tests."""

import pytest
from PyQt6.QtWidgets import QApplication


@pytest.fixture(scope="session")
def qapp():
    """Create QApplication instance for tests."""
    app = QApplication.instance() or QApplication([])
    yield app
    # Don't quit - may cause issues with other tests
