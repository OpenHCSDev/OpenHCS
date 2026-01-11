"""Mixin for scope-based window border rendering."""

from typing import Optional, Tuple, List
from PyQt6.QtGui import QPainter, QPen, QColor
from PyQt6.QtCore import Qt
import logging

from pyqt_formgen.widgets.shared.scope_color_utils import (
    tint_color_perceptual,
    get_scope_color_scheme,
)
from pyqt_formgen.services.scope_color_service import ScopeColorService

logger = logging.getLogger(__name__)


class ScopedBorderMixin:
    """Mixin that renders scope-based borders on QDialog/QWidget subclasses.

    Also provides scope accent colors for UI elements like buttons, tree selection,
    and titles to create visual consistency with the scope border color.
    """

    BORDER_PATTERNS = {
        "solid": (Qt.PenStyle.SolidLine, None),
        "dashed": (Qt.PenStyle.DashLine, [8, 6]),
        "dotted": (Qt.PenStyle.DotLine, [2, 6]),
        "dashdot": (Qt.PenStyle.DashDotLine, [8, 4, 2, 4]),
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

        # Use explicit step_index if set (for windows matching list item position)
        step_index = getattr(self, "_step_index", None)
        self._scope_color_scheme = get_scope_color_scheme(scope_id, step_index=step_index)
        border_style = self._scope_color_scheme.to_stylesheet_step_window_border()
        current_style = self.styleSheet() if hasattr(self, "styleSheet") else ""
        self.setStyleSheet(f"{current_style}\nQDialog {{ {border_style} }}")

        self._subscribe_to_color_changes()

        # Apply accent styling to UI elements (hook for subclasses)
        self._apply_scope_accent_styling()

        if hasattr(self, "update"):
            self.update()

    def _apply_scope_accent_styling(self) -> None:
        """Apply scope accent color to UI elements.

        Override in subclasses to style buttons, tree selection, title, etc.
        Called after _scope_color_scheme is set.
        """
        pass  # Default: no accent styling

    def get_scope_accent_color(self) -> Optional[QColor]:
        """Get the scope accent color (matching border/flash color).

        Returns None if no scope color scheme is set.
        Uses the same tint index as the border layers for consistency.
        """
        if not self._scope_color_scheme:
            return None
        # Use the same tint_idx from step_border_layers as border/flash rendering
        base_rgb = self._scope_color_scheme.base_color_rgb
        layers = getattr(self._scope_color_scheme, 'step_border_layers', None)
        if layers:
            _, tint_idx, _ = (layers[0] + ("solid",))[:3]
            return tint_color_perceptual(base_rgb, tint_idx).darker(120)
        # Fallback for schemes without layers
        return tint_color_perceptual(base_rgb, 1).darker(120)

    def get_scope_accent_stylesheet(self, for_button: bool = True) -> str:
        """Generate stylesheet for scope-accented buttons.

        Args:
            for_button: If True, generates QPushButton stylesheet

        Returns:
            Stylesheet string or empty string if no scope color
        """
        color = self.get_scope_accent_color()
        if not color:
            return ""

        hex_color = color.name()
        # Lighter version for hover
        lighter = color.lighter(115)
        hex_lighter = lighter.name()
        # Darker version for pressed
        darker = color.darker(115)
        hex_darker = darker.name()

        if for_button:
            return f"""
                QPushButton {{
                    background-color: {hex_color};
                    color: white;
                    border: none;
                    border-radius: 3px;
                    padding: 8px;
                }}
                QPushButton:hover {{
                    background-color: {hex_lighter};
                }}
                QPushButton:pressed {{
                    background-color: {hex_darker};
                }}
            """
        return ""

    def get_scope_tree_selection_stylesheet(self) -> str:
        """Generate stylesheet for tree selection matching scope color.

        Returns:
            Stylesheet string or empty string if no scope color
        """
        color = self.get_scope_accent_color()
        if not color:
            return ""

        hex_color = color.name()
        # Slightly transparent for hover
        hover_color = QColor(color)
        hover_color.setAlphaF(0.3)

        return f"""
            QTreeWidget::item:selected {{
                background-color: {hex_color};
                color: white;
            }}
            QTreeWidget::item:hover:!selected {{
                background-color: rgba({color.red()}, {color.green()}, {color.blue()}, 76);
            }}
        """

    def _subscribe_to_color_changes(self) -> None:
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
            color = tint_color_perceptual(base_rgb, tint_idx).darker(120)

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
