"""Unified background task with cancellation, debounce, and cleanup."""

from typing import Callable, Any, Optional, Tuple
from PyQt6.QtCore import QThread, pyqtSignal
from PyQt6.QtWidgets import QPushButton
import time

# --- Module-level constants ---
CANCEL_WAIT_MS = 100      # Wait time when cancelling previous task
CLEANUP_WAIT_MS = 200     # Wait time during widget close cleanup


class BackgroundTask(QThread):
    """
    Unified background task with cancellation, debounce, and cleanup.

    Usage:
        task = BackgroundTask(target=my_func, args=(a, b))
        task.result_ready.connect(on_success)
        task.error_occurred.connect(on_error)  # Receives Exception, not str
        task.start()

        # Later:
        task.cancel()  # Safe cancellation

    Error handling:
        def on_error(e: Exception):
            logger.exception("Failed", exc_info=e)  # Full traceback
            show_message(str(e))  # User-friendly string
            if isinstance(e, TimeoutError): ...  # Type checking
    """

    result_ready = pyqtSignal(object)
    error_occurred = pyqtSignal(Exception)  # Full exception, caller decides

    def __init__(
        self,
        target: Callable[..., Any],
        args: Tuple = (),
        kwargs: dict = None,
        debounce_ms: int = 0,
        parent=None
    ):
        super().__init__(parent)
        self._target = target
        self._args = args
        self._kwargs = kwargs or {}
        self._debounce_ms = debounce_ms
        self.cancelled = False

    def run(self):
        """Execute target in background, respecting cancellation."""
        try:
            result = self._target(*self._args, **self._kwargs)
            if not self.cancelled:
                self.result_ready.emit(result)
        except Exception as e:
            if not self.cancelled:
                self.error_occurred.emit(e)  # Full exception object

    def cancel(self):
        """Cancel task — signals won't emit after this."""
        self.cancelled = True


class BackgroundTaskManager:
    """
    Manages background task lifecycle for a widget.

    Handles:
    - Cancelling previous task before starting new one
    - Cleanup on widget close
    - Debounce across rapid calls
    - Button state management (disable during operation, auto-restore)

    Usage in widget:
        self._task_manager = BackgroundTaskManager()

        def refresh_data(self):
            self._task_manager.run(
                target=self.service.fetch_data,
                args=(self.query,),
                button=self.refresh_button,
                button_loading_text="Loading...",
                on_success=self._on_data_ready,
                on_error=self._on_error,
                debounce_ms=200
            )

        def closeEvent(self, event):
            self._task_manager.cleanup()
            super().closeEvent(event)
    """

    def __init__(self):
        self._current_task: Optional[BackgroundTask] = None
        self._last_run_time: float = 0.0

    def run(
        self,
        target: Callable[..., Any],
        args: Tuple = (),
        kwargs: dict = None,
        on_success: Callable[[Any], None] = None,
        on_error: Callable[[Exception], None] = None,
        debounce_ms: int = 0,
        button: QPushButton = None,
        button_loading_text: str = None,
    ) -> Optional[BackgroundTask]:
        """
        Run a background task, cancelling any previous one.

        Args:
            target: Function to execute in background
            args: Positional arguments for target
            kwargs: Keyword arguments for target
            on_success: Callback for successful result
            on_error: Callback for error (receives Exception, not str)
            debounce_ms: Minimum time between runs (skip if too soon)
            button: Button to disable during operation (auto-restored on complete)
            button_loading_text: Text while loading (default: original + "...")

        Returns:
            BackgroundTask if started, None if debounced out
        """
        # Debounce check - return None so caller knows we didn't start
        if debounce_ms > 0:
            now = time.time() * 1000
            if now - self._last_run_time < debounce_ms:
                return None
            self._last_run_time = now

        # Cancel previous task
        if self._current_task is not None and self._current_task.isRunning():
            self._current_task.cancel()
            self._current_task.wait(CANCEL_WAIT_MS)

        # Button state management — restore on BOTH success and error
        original_button_text = None
        if button:
            original_button_text = button.text()
            button.setEnabled(False)
            button.setText(button_loading_text or f"{original_button_text}...")

        def restore_button():
            if button:
                button.setEnabled(True)
                button.setText(original_button_text)

        # Wrap callbacks to restore button first
        def wrapped_success(result):
            restore_button()
            if on_success:
                on_success(result)

        def wrapped_error(error):
            restore_button()
            if on_error:
                on_error(error)

        # Create and configure new task
        task = BackgroundTask(target=target, args=args, kwargs=kwargs)
        task.result_ready.connect(wrapped_success)
        task.error_occurred.connect(wrapped_error)

        self._current_task = task
        task.start()
        return task

    def cleanup(self):
        """Cancel and wait for current task. Call from closeEvent."""
        if self._current_task is not None and self._current_task.isRunning():
            self._current_task.cancel()
            self._current_task.wait(CLEANUP_WAIT_MS)
        self._current_task = None

