from PyQt6.QtCore import QObject, QEvent, QTimer
from PyQt6.QtCore import Qt
from PyQt6.QtWidgets import QApplication, QWidget


def ensure_window_on_screen(w: QWidget) -> None:
    """Clamp a window to screen bounds (call once at open)."""
    if not w:
        return
    top = w.window() if hasattr(w, "window") else w
    if not isinstance(top, QWidget):
        return

    screen = top.screen() or QApplication.screenAt(top.frameGeometry().center()) or QApplication.primaryScreen()
    if not screen:
        return
    
    sg = screen.availableGeometry()
    wg = top.frameGeometry()
    
    # Skip if geometry not ready
    if wg.width() <= 1 or wg.height() <= 1:
        return

    # Shrink if larger than work area
    max_w = max(100, sg.width() - 20)
    max_h = max(100, sg.height() - 20)
    if wg.width() > max_w or wg.height() > max_h:
        top.resize(min(wg.width(), max_w), min(wg.height(), max_h))
        wg = top.frameGeometry()

    # Clamp position to screen
    nx = max(sg.left(), min(wg.x(), sg.right() - wg.width()))
    ny = max(sg.top(), min(wg.y(), sg.bottom() - wg.height()))
    
    if (nx, ny) != (wg.x(), wg.y()):
        top.move(nx, ny)


class _ClampWindowsFilter(QObject):
    """Clamp windows into screen space on initial show"""
    
    def eventFilter(self, obj, event):
        # Only act on Show events
        if event.type() != QEvent.Type.Show:
            return False
        
        # Get top-level window
        top = obj.window() if hasattr(obj, "window") else obj
        if not isinstance(top, QWidget):
            return False
        
        # Check for window flags
        has_window_flag = bool(top.windowFlags() & (Qt.WindowType.Window | Qt.WindowType.Dialog))
        
        if not (top.isWindow() or has_window_flag):
            return False
        
        # Only clamp once per window
        if top.property("_openhcs_clamped"):
            return False
        
        # Mark as clamped immediately to prevent re-entry
        top.setProperty("_openhcs_clamped", True)
        
        # Clamp after geometry is finalized
        def clamp_once():
            try:
                if top and not top.property("_openhcs_deleted"):
                    ensure_window_on_screen(top)
            except RuntimeError:
                pass
        
        QTimer.singleShot(100, clamp_once)
        return False


def install_global_window_bounds_filter(app: QApplication):
    """Install filter once on QApplication (call early in setup_application)."""
    window_filter = _ClampWindowsFilter(app)
    app.installEventFilter(window_filter)
    setattr(app, "_openhcs_window_bounds_filter", window_filter)
    return window_filter
