"""Reusable trailing debounce timer."""

from typing import Callable, Optional
from PyQt6.QtCore import QTimer


class DebounceTimer:
    """
    Reusable trailing debounce timer.

    Restarts timer on each call. Handler fires only after delay_ms of inactivity.

    Usage:
        self._debounce = DebounceTimer(delay_ms=200, handler=self._do_update)

        def on_text_changed(self):
            self._debounce.trigger()  # Restarts timer
    """

    def __init__(self, delay_ms: int, handler: Callable[[], None]):
        self._delay_ms = delay_ms
        self._handler = handler
        self._timer: Optional[QTimer] = None

    def trigger(self):
        """Trigger debounce — restarts timer."""
        if self._timer is not None:
            self._timer.stop()

        self._timer = QTimer()
        self._timer.setSingleShot(True)
        self._timer.timeout.connect(self._handler)
        self._timer.start(self._delay_ms)

    def cancel(self):
        """Cancel pending trigger."""
        if self._timer is not None:
            self._timer.stop()
            self._timer = None

    def force(self):
        """Cancel timer and fire handler immediately."""
        self.cancel()
        self._handler()

