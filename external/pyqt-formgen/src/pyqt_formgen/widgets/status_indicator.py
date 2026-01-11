"""Reusable status indicator widget with colored dot, label, and refresh button."""

from enum import Enum
from typing import Optional, Callable, Tuple
from PyQt6.QtWidgets import QWidget, QHBoxLayout, QLabel, QPushButton
from PyQt6.QtGui import QFont

from pyqt_formgen.core import BackgroundTaskManager
from pyqt_formgen.theming import ColorScheme

# --- Module-level constants ---
DEFAULT_DEBOUNCE_MS = 2000  # Debounce for connection checks


class StatusState(Enum):
    """Status indicator states — colors resolved from color scheme at runtime."""
    UNKNOWN = "Unknown"
    CHECKING = "Checking..."
    CONNECTED = "connected"      # No default message - uses check result
    DISCONNECTED = "disconnected"
    WARNING = "warning"

    @property
    def default_message(self) -> Optional[str]:
        # Only UNKNOWN and CHECKING have user-visible default messages
        if self in (StatusState.UNKNOWN, StatusState.CHECKING):
            return self.value
        return None


def get_status_color(state: StatusState, color_scheme: ColorScheme) -> str:
    """Resolve status state to color from scheme."""
    import logging
    logger = logging.getLogger(__name__)
    COLOR_MAP = {
        StatusState.UNKNOWN: color_scheme.text_secondary,
        StatusState.CHECKING: color_scheme.status_warning,
        StatusState.CONNECTED: color_scheme.status_success,
        StatusState.DISCONNECTED: color_scheme.status_error,
        StatusState.WARNING: color_scheme.status_warning,
    }
    color_tuple = COLOR_MAP[state]
    logger.info(f"get_status_color: state={state}, color_tuple={color_tuple}, status_success={color_scheme.status_success}")
    return color_scheme.to_hex(color_tuple)


class StatusIndicator(QWidget):
    """
    Reusable status indicator with colored dot, label, and refresh button.

    Usage:
        indicator = StatusIndicator(
            check_fn=lambda: my_service.test_connection(),
            color_scheme=self.color_scheme,
            parent=self
        )
        layout.addWidget(indicator)

        # check_fn returns Tuple[bool, str]: (is_ok, status_message)
        # True → CONNECTED state, False → DISCONNECTED state
    """

    def __init__(
        self,
        check_fn: Callable[[], Tuple[bool, str]] = None,
        color_scheme: ColorScheme = None,
        show_refresh: bool = True,
        debounce_ms: int = DEFAULT_DEBOUNCE_MS,
        parent=None
    ):
        super().__init__(parent)
        self._check_fn = check_fn
        self._color_scheme = color_scheme or ColorScheme()
        self._debounce_ms = debounce_ms
        self._task_manager = BackgroundTaskManager()

        self._setup_ui(show_refresh)

    def _setup_ui(self, show_refresh: bool):
        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(4)

        # Colored dot
        self._dot = QLabel("●")
        self._dot.setFixedWidth(12)
        layout.addWidget(self._dot)

        # Status text
        self._label = QLabel("Unknown")
        self._label.setFont(QFont("Arial", 8))
        layout.addWidget(self._label)

        # Refresh button (optional)
        if show_refresh:
            self._refresh_btn = QPushButton("↻")
            self._refresh_btn.setFixedSize(20, 20)
            self._refresh_btn.setToolTip("Refresh status")
            self._refresh_btn.clicked.connect(self.refresh)
            layout.addWidget(self._refresh_btn)
        else:
            self._refresh_btn = None

        self.set_state(StatusState.UNKNOWN)

    def set_state(self, state: StatusState, message: str = None):
        """Update visual state."""
        import logging
        logger = logging.getLogger(__name__)
        logger.info(f"StatusIndicator.set_state: state={state}, message={message}")
        color = get_status_color(state, self._color_scheme)
        logger.info(f"StatusIndicator.set_state: color={color}")
        self._dot.setStyleSheet(f"color: {color};")
        self._label.setText(message or state.default_message or "")

        if self._refresh_btn:
            self._refresh_btn.setEnabled(state != StatusState.CHECKING)

    def refresh(self, force: bool = False):
        """Trigger async status check."""
        if self._check_fn is None:
            return

        # Only set CHECKING if task actually starts (not debounced)
        task = self._task_manager.run(
            target=self._check_fn,
            on_success=self._on_check_complete,
            on_error=self._on_check_error,
            debounce_ms=0 if force else self._debounce_ms  # No debounce on force
        )
        if task is not None:
            self.set_state(StatusState.CHECKING)

    def _on_check_complete(self, result: Tuple[bool, str]):
        """Handle check result."""
        import logging
        logger = logging.getLogger(__name__)
        logger.info(f"StatusIndicator._on_check_complete received: {result}")
        is_ok, message = result
        state = StatusState.CONNECTED if is_ok else StatusState.DISCONNECTED
        logger.info(f"StatusIndicator setting state to: {state}, message: {message}")
        self.set_state(state, message)

    def _on_check_error(self, error: Exception):
        """Handle check error."""
        self.set_state(StatusState.DISCONNECTED, f"Error: {str(error)}")

    def showEvent(self, event):
        """Auto-refresh on show (no debounce for initial check)."""
        super().showEvent(event)
        self.refresh(force=True)

    def closeEvent(self, event):
        """Cleanup on close."""
        self._task_manager.cleanup()
        super().closeEvent(event)

