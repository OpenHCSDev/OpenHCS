"""Mixin for scope-based window border rendering.

Provides automatic border styling based on scope_id:
- Simple solid borders for orchestrator-level scopes
- Layered patterned borders for step-level scopes (with tints + patterns)
- Reactive updates via ScopeColorService signals
"""

from typing import Optional, Tuple, List
from PyQt6.QtGui import QPainter, QPen, QColor
from PyQt6.QtCore import Qt
import logging

logger = logging.getLogger(__name__)


class ScopedBorderMixin:
    """Mixin that renders scope-based borders on QDialog/QWidget subclasses.

    Subclasses declare scope via:
        self.scope_id: str  # Required - determines color scheme
        self.step_position: Optional[int]  # Optional - for step windows (layered borders)

    Then call self._init_scope_border() after scope_id is set.
    
    The mixin automatically:
    - Gets color scheme from ScopeColorService
    - Reserves border space via stylesheet
    - Renders layered borders in paintEvent (if step scope with layers)
    - Subscribes to color change signals for reactive updates
    """

    # Class-level config (override in subclass if needed)
    BORDER_TINT_FACTORS: Tuple[float, ...] = (0.7, 1.0, 1.4)
    BORDER_PATTERNS = {
        'solid': (Qt.PenStyle.SolidLine, None),
        'dashed': (Qt.PenStyle.DashLine, [8, 6]),
        'dotted': (Qt.PenStyle.DotLine, [2, 6]),
    }

    _scope_color_scheme = None  # Set by _init_scope_border

    def _init_scope_border(self) -> None:
        """Initialize scope-based border. Call after scope_id is set."""
        scope_id = getattr(self, 'scope_id', None)
        if not scope_id:
            return

        from openhcs.pyqt_gui.widgets.shared.scope_color_utils import get_scope_color_scheme
        self._scope_color_scheme = get_scope_color_scheme(scope_id)

        # Reserve border space via stylesheet
        border_style = self._scope_color_scheme.to_stylesheet_step_window_border()
        current_style = self.styleSheet() if hasattr(self, 'styleSheet') else ''
        # Apply to QDialog (for BaseFormDialog subclasses)
        self.setStyleSheet(f"{current_style}\nQDialog {{ {border_style} }}")

        # Subscribe to color change signals for reactive updates
        self._subscribe_to_color_changes()

        if hasattr(self, 'update'):
            self.update()  # Trigger repaint

    def _subscribe_to_color_changes(self) -> None:
        """Subscribe to ScopeColorService signals for reactive updates."""
        from openhcs.pyqt_gui.widgets.shared.services.scope_color_service import ScopeColorService
        service = ScopeColorService.instance()
        
        # Connect signals (check if not already connected)
        scope_id = getattr(self, 'scope_id', None)
        if scope_id:
            service.color_changed.connect(self._on_scope_color_changed)
            service.all_colors_reset.connect(self._on_all_colors_reset)

    def _on_scope_color_changed(self, changed_scope_id: str) -> None:
        """Handle color change for specific scope."""
        scope_id = getattr(self, 'scope_id', None)
        if scope_id and (scope_id == changed_scope_id or scope_id.startswith(f"{changed_scope_id}::")):
            self._refresh_scope_border()

    def _on_all_colors_reset(self) -> None:
        """Handle bulk color reset (strategy change)."""
        self._refresh_scope_border()

    def _refresh_scope_border(self) -> None:
        """Refresh border with current color scheme."""
        self._scope_color_scheme = None  # Clear cached scheme
        self._init_scope_border()

    def paintEvent(self, event) -> None:
        """Render layered scope borders. Calls super().paintEvent first."""
        super().paintEvent(event)

        if not self._scope_color_scheme:
            return

        layers = getattr(self._scope_color_scheme, 'step_border_layers', None)
        if not layers:
            return

        self._paint_border_layers(layers)

    def _paint_border_layers(self, layers: List[Tuple]) -> None:
        """Paint multi-layer borders with tints and patterns."""
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)

        rect = self.rect()
        inset = 0
        base_rgb = self._scope_color_scheme.base_color_rgb

        for layer in layers:
            # Unpack layer tuple: (width, tint_idx, pattern)
            width, tint_idx, pattern = (layer + ('solid',))[:3]

            # Tinted color
            tint = self.BORDER_TINT_FACTORS[tint_idx]
            color = QColor(*(min(255, int(c * tint)) for c in base_rgb)).darker(120)

            # Create pen with pattern
            pen = QPen(color, width)
            style, dash_pattern = self.BORDER_PATTERNS.get(pattern, self.BORDER_PATTERNS['solid'])
            pen.setStyle(style)
            if dash_pattern:
                pen.setDashPattern(dash_pattern)

            # Draw layer
            offset = int(inset + width / 2)
            painter.setPen(pen)
            painter.drawRect(rect.adjusted(offset, offset, -offset - 1, -offset - 1))
            inset += width

        painter.end()

