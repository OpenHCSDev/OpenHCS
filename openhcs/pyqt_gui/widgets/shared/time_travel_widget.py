"""
Time-Travel Debugging Widget for ObjectStateRegistry.

Provides a compact slider UI for scrubbing through the ENTIRE system history.
All ObjectStates across all scopes are captured together for coherent time-travel.
"""

import logging
from typing import Optional, List, Dict, Any

from PyQt6.QtWidgets import (
    QWidget, QHBoxLayout, QSlider, QLabel, QPushButton, QToolTip, QFrame
)
from PyQt6.QtCore import Qt, pyqtSignal, QPoint, QTimer
from PyQt6.QtGui import QFont

from openhcs.config_framework.object_state import ObjectStateRegistry

logger = logging.getLogger(__name__)


class TimeTravelWidget(QWidget):
    """Compact time-travel debugging widget for ObjectStateRegistry.

    Tracks the ENTIRE system state (all ObjectStates) at each point in time.
    When you scrub, ALL config windows update simultaneously.

    Features:
    - Slider to scrub through global history
    - Back/Forward buttons
    - Label showing current snapshot info
    - Tooltip showing num states captured
    """

    # Emitted when time-travel position changes
    position_changed = pyqtSignal(int)  # (index)

    def __init__(self, parent=None):
        super().__init__(parent)
        self._setup_ui()

        # Auto-refresh timer to catch new snapshots
        self._refresh_timer = QTimer(self)
        self._refresh_timer.timeout.connect(self._update_ui)
        self._refresh_timer.start(500)  # Refresh every 500ms

    def _setup_ui(self):
        """Build the compact UI."""
        layout = QHBoxLayout(self)
        layout.setContentsMargins(4, 0, 4, 0)
        layout.setSpacing(4)

        # Time-travel icon/label
        self.icon_label = QLabel("⏱️")
        self.icon_label.setToolTip("Time-Travel Debugging (All States)")
        layout.addWidget(self.icon_label)

        # Back button
        self.back_btn = QPushButton("◀")
        self.back_btn.setFixedWidth(24)
        self.back_btn.setToolTip("Step back in history")
        self.back_btn.clicked.connect(self._on_back)
        layout.addWidget(self.back_btn)

        # Slider
        self.slider = QSlider(Qt.Orientation.Horizontal)
        self.slider.setMinimum(0)
        self.slider.setMaximum(0)
        self.slider.setFixedWidth(150)
        self.slider.setToolTip("Scrub through system state history")
        self.slider.valueChanged.connect(self._on_slider_changed)
        self.slider.sliderMoved.connect(self._show_tooltip_at_position)
        layout.addWidget(self.slider)

        # Forward button
        self.forward_btn = QPushButton("▶")
        self.forward_btn.setFixedWidth(24)
        self.forward_btn.setToolTip("Step forward in history")
        self.forward_btn.clicked.connect(self._on_forward)
        layout.addWidget(self.forward_btn)

        # Head button (return to present)
        self.head_btn = QPushButton("⏭")
        self.head_btn.setFixedWidth(24)
        self.head_btn.setToolTip("Return to present (latest state)")
        self.head_btn.clicked.connect(self._on_head)
        layout.addWidget(self.head_btn)

        # Status label
        self.status_label = QLabel("No history")
        self.status_label.setMinimumWidth(180)
        font = QFont()
        font.setPointSize(9)
        self.status_label.setFont(font)
        layout.addWidget(self.status_label)

        # Separator
        separator = QFrame()
        separator.setFrameShape(QFrame.Shape.VLine)
        separator.setFrameShadow(QFrame.Shadow.Sunken)
        layout.addWidget(separator)

        self._update_ui()

    def _update_ui(self):
        """Update slider and labels from registry history."""
        history = ObjectStateRegistry.get_history_info()

        if not history:
            self.slider.setMaximum(0)
            self.slider.setEnabled(False)
            self.back_btn.setEnabled(False)
            self.forward_btn.setEnabled(False)
            self.head_btn.setEnabled(False)
            self.status_label.setText("No history yet")
            return

        self.slider.setEnabled(True)
        self.slider.setMaximum(len(history) - 1)

        # Find current position
        current_idx = next((h['index'] for h in history if h['is_current']), len(history) - 1)
        self.slider.blockSignals(True)
        self.slider.setValue(current_idx)
        self.slider.blockSignals(False)

        # Update status
        current = history[current_idx]
        is_head = current_idx == len(history) - 1
        is_traveling = ObjectStateRegistry.is_time_traveling()

        status = f"{current['timestamp']} | {current['label'][:30]}"
        if is_traveling:
            status += f" ({current_idx + 1}/{len(history)})"
        else:
            status += " (HEAD)"

        self.status_label.setText(status)

        # Enable/disable buttons
        self.back_btn.setEnabled(current_idx > 0)
        self.forward_btn.setEnabled(current_idx < len(history) - 1)
        self.head_btn.setEnabled(is_traveling)

        # Visual indicator when time-traveling
        if is_traveling:
            self.icon_label.setText("⏪")
            self.icon_label.setStyleSheet("color: orange;")
        else:
            self.icon_label.setText("⏱️")
            self.icon_label.setStyleSheet("")

    def _on_slider_changed(self, value: int):
        """Handle slider value change."""
        ObjectStateRegistry.time_travel_to(value)
        self._update_ui()
        self.position_changed.emit(value)

    def _on_back(self):
        """Step back in history."""
        ObjectStateRegistry.time_travel_back()
        self._update_ui()

    def _on_forward(self):
        """Step forward in history."""
        ObjectStateRegistry.time_travel_forward()
        self._update_ui()

    def _on_head(self):
        """Return to present."""
        ObjectStateRegistry.time_travel_to_head()
        self._update_ui()

    def _show_tooltip_at_position(self, value: int):
        """Show tooltip with snapshot details while dragging."""
        history = ObjectStateRegistry.get_history_info()
        if value < 0 or value >= len(history):
            return

        h = history[value]
        tooltip = f"<b>{h['timestamp']}</b><br>{h['label']}<br>States captured: {h['num_states']}"
        pos = self.slider.mapToGlobal(QPoint(self.slider.width() // 2, -30))
        QToolTip.showText(pos, tooltip)

    def refresh(self):
        """Refresh UI from registry (call after external changes)."""
        self._update_ui()

