"""Mixin for scope-based window border rendering."""

from typing import Optional, Tuple, List
from PyQt6.QtGui import QPainter, QPen, QColor
from PyQt6.QtCore import Qt
import logging

logger = logging.getLogger(__name__)


class ScopedBorderMixin:
    """Mixin that renders scope-based borders on QDialog/QWidget subclasses."""

    BORDER_TINT_FACTORS: Tuple[float, ...] = (0.7, 1.0, 1.4)
    BORDER_PATTERNS = {
        "solid": (Qt.PenStyle.SolidLine, None),
        "dashed": (Qt.PenStyle.DashLine, [8, 6]),
        "dotted": (Qt.PenStyle.DotLine, [2, 6]),
    }

    _scope_color_scheme = None
    _step_index: Optional[int] = None  # For border pattern based on actual position

    def _init_scope_border(self) -> None:
        """Initialize scope-based border. Call after scope_id is set.

        If _step_index is set, uses it for border pattern instead of
        extracting from scope_id. This allows windows to match their
        list item's border based on actual position in pipeline.
        """
        scope_id = getattr(self, "scope_id", None)
        if not scope_id:
            return

        from openhcs.pyqt_gui.widgets.shared.scope_color_utils import get_scope_color_scheme

        # Use explicit step_index if set (for windows matching list item position)
        step_index = getattr(self, "_step_index", None)
        self._scope_color_scheme = get_scope_color_scheme(scope_id, step_index=step_index)
        border_style = self._scope_color_scheme.to_stylesheet_step_window_border()
        current_style = self.styleSheet() if hasattr(self, "styleSheet") else ""
        self.setStyleSheet(f"{current_style}\nQDialog {{ {border_style} }}")

        self._subscribe_to_color_changes()
        if hasattr(self, "update"):
            self.update()

    def _subscribe_to_color_changes(self) -> None:
        from openhcs.pyqt_gui.widgets.shared.services.scope_color_service import ScopeColorService

        service = ScopeColorService.instance()
        scope_id = getattr(self, "scope_id", None)
        if scope_id:
            service.color_changed.connect(self._on_scope_color_changed)
            service.all_colors_reset.connect(self._on_all_colors_reset)

    def _on_scope_color_changed(self, changed_scope_id: str) -> None:
        scope_id = getattr(self, "scope_id", None)
        if scope_id and (
            scope_id == changed_scope_id or scope_id.startswith(f"{changed_scope_id}::")
        ):
            self._refresh_scope_border()

    def _on_all_colors_reset(self) -> None:
        self._refresh_scope_border()

    def _refresh_scope_border(self) -> None:
        self._scope_color_scheme = None
        self._init_scope_border()

    def paintEvent(self, event) -> None:
        super().paintEvent(event)
        if not self._scope_color_scheme:
            return
        layers = getattr(self._scope_color_scheme, "step_border_layers", None)
        if not layers:
            return
        self._paint_border_layers(layers)

    def _paint_border_layers(self, layers: List[Tuple]) -> None:
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)

        rect = self.rect()
        inset = 0
        base_rgb = self._scope_color_scheme.base_color_rgb

        for layer in layers:
            width, tint_idx, pattern = (layer + ("solid",))[:3]
            tint = self.BORDER_TINT_FACTORS[tint_idx]
            color = QColor(*(min(255, int(c * tint)) for c in base_rgb)).darker(120)

            pen = QPen(color, width)
            style, dash_pattern = self.BORDER_PATTERNS.get(
                pattern, self.BORDER_PATTERNS["solid"]
            )
            pen.setStyle(style)
            if dash_pattern:
                pen.setDashPattern(dash_pattern)

            offset = int(inset + width / 2)
            painter.setPen(pen)
            painter.drawRect(rect.adjusted(offset, offset, -offset - 1, -offset - 1))
            inset += width

        painter.end()
