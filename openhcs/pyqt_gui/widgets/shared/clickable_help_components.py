"""PyQt6 clickable help components - clean architecture without circular imports."""

import logging
from typing import Union, Callable, Optional
from PyQt6.QtWidgets import QLabel, QPushButton, QWidget, QHBoxLayout, QGroupBox, QVBoxLayout
from PyQt6.QtCore import Qt, pyqtSignal, pyqtProperty, QRect, QRectF
from PyQt6.QtGui import QFont, QCursor, QColor, QPainter, QPen

from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme

logger = logging.getLogger(__name__)


class FlashableGroupBox(QGroupBox):
    """QGroupBox that supports flash animation via overlay.

    GAME ENGINE ARCHITECTURE: Flash effects are rendered by a single
    WindowFlashOverlay per window, NOT by individual groupbox paintEvents.
    This scales O(1) per window regardless of how many items are animating.

    The groupbox just stores its flash_key for the overlay to look up.
    """

    def __init__(self, title: str = "", parent: Optional[QWidget] = None,
                 flash_key: str = "", flash_manager=None):
        super().__init__(title, parent)
        self._flash_key = flash_key  # Key for overlay to look up geometry
        self._flash_manager = flash_manager  # Kept for backwards compat

    # NOTE: paintEvent flash rendering REMOVED - now handled by WindowFlashOverlay
    # This eliminates O(n) paintEvent calls per frame


class ClickableHelpLabel(QLabel):
    """PyQt6 clickable label that shows help information - reuses Textual TUI help logic."""
    
    help_requested = pyqtSignal()
    
    def __init__(self, text: str, help_target: Union[Callable, type] = None,
                 param_name: str = None, param_description: str = None,
                 param_type: type = None, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        """Initialize clickable help label.

        Args:
            text: Display text for the label
            help_target: Function or class to show help for (for function help)
            param_name: Parameter name (for parameter help)
            param_description: Parameter description (for parameter help)
            param_type: Parameter type (for parameter help)
            color_scheme: Color scheme for styling (optional, uses default if None)
        """
        # Add help indicator to text
        display_text = f"{text} (?)"
        super().__init__(display_text, parent)

        # Initialize color scheme
        self.color_scheme = color_scheme or PyQt6ColorScheme()

        self.help_target = help_target
        self.param_name = param_name
        self.param_description = param_description
        self.param_type = param_type

        # Style as clickable
        self.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        self.setStyleSheet(f"""
            QLabel {{
                color: {self.color_scheme.to_hex(self.color_scheme.selection_bg)};
                text-decoration: underline;
            }}
            QLabel:hover {{
                color: {self.color_scheme.to_hex(self.color_scheme.selection_bg)};
            }}
        """)
        
    def mousePressEvent(self, event):
        """Handle mouse press to show help - reuses Textual TUI help manager pattern."""
        if event.button() == Qt.MouseButton.LeftButton:
            try:
                # Import inside method to avoid circular imports (same pattern as Textual TUI)
                from openhcs.pyqt_gui.windows.help_windows import HelpWindowManager

                if self.help_target:
                    # Show function/class help using unified manager
                    HelpWindowManager.show_docstring_help(self.help_target, parent=self)
                elif self.param_name:
                    # Show parameter help using the description passed from parameter analysis
                    HelpWindowManager.show_parameter_help(
                        self.param_name, self.param_description or "No description available", self.param_type, parent=self
                    )

                self.help_requested.emit()

            except Exception as e:
                logger.error(f"Failed to show help: {e}")
                raise

        super().mousePressEvent(event)




class ClickableFunctionTitle(ClickableHelpLabel):
    """PyQt6 clickable function title that shows function documentation - mirrors Textual TUI."""

    def __init__(self, func: Callable, index: int = None, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        func_name = getattr(func, '__name__', 'Unknown Function')
        module_name = getattr(func, '__module__', '').split('.')[-1] if func else ''

        # Build title text
        title = f"{index + 1}: {func_name}" if index is not None else func_name
        if module_name:
            title += f" ({module_name})"

        super().__init__(
            text=title,
            help_target=func,
            color_scheme=color_scheme,
            parent=parent
        )

        # Make title bold
        font = QFont()
        font.setBold(True)
        self.setFont(font)


class ClickableParameterLabel(ClickableHelpLabel):
    """PyQt6 clickable parameter label that shows parameter documentation - mirrors Textual TUI."""

    def __init__(self, param_name: str, param_description: str = None,
                 param_type: type = None, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        # Format parameter name nicely
        display_name = param_name.replace('_', ' ').title()

        super().__init__(
            text=display_name,
            param_name=param_name,
            param_description=param_description or "No description available",
            param_type=param_type,
            color_scheme=color_scheme,
            parent=parent
        )


class HelpIndicator(QLabel):
    """PyQt6 simple help indicator that can be added next to any widget - mirrors Textual TUI."""
    
    help_requested = pyqtSignal()
    
    def __init__(self, help_target: Union[Callable, type] = None,
                 param_name: str = None, param_description: str = None,
                 param_type: type = None, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        super().__init__("(?)", parent)

        # Initialize color scheme
        self.color_scheme = color_scheme or PyQt6ColorScheme()

        self.help_target = help_target
        self.param_name = param_name
        self.param_description = param_description
        self.param_type = param_type
        
        # Style as clickable help indicator
        self.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        self.setStyleSheet(f"""
            QLabel {{
                color: {self.color_scheme.to_hex(self.color_scheme.border_light)};
                font-size: 10px;
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_light)};
                border-radius: 8px;
                padding: 2px 4px;
                background-color: {self.color_scheme.to_hex(self.color_scheme.window_bg)};
            }}
            QLabel:hover {{
                color: {self.color_scheme.to_hex(self.color_scheme.selection_bg)};
                border-color: {self.color_scheme.to_hex(self.color_scheme.selection_bg)};
                background-color: {self.color_scheme.to_hex(self.color_scheme.selection_bg)};
            }}
        """)
        
        # Set fixed size for consistent appearance
        self.setFixedSize(20, 16)
        self.setAlignment(Qt.AlignmentFlag.AlignCenter)
        
    def set_scope_accent_color(self, color) -> None:
        """Set scope accent color (QColor). Called by parent window for scope styling."""
        if hasattr(color, 'name'):
            hex_color = color.name()
        else:
            hex_color = self.color_scheme.to_hex(color)

        self.setStyleSheet(f"""
            QLabel {{
                color: {self.color_scheme.to_hex(self.color_scheme.border_light)};
                font-size: 10px;
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_light)};
                border-radius: 8px;
                padding: 2px 4px;
                background-color: {self.color_scheme.to_hex(self.color_scheme.window_bg)};
            }}
            QLabel:hover {{
                color: white;
                border-color: {hex_color};
                background-color: {hex_color};
            }}
        """)

    def mousePressEvent(self, event):
        """Handle mouse press to show help - reuses Textual TUI help manager pattern."""
        if event.button() == Qt.MouseButton.LeftButton:
            try:
                # Import inside method to avoid circular imports (same pattern as Textual TUI)
                from openhcs.pyqt_gui.windows.help_windows import HelpWindowManager

                if self.help_target:
                    # Show function/class help using unified manager
                    HelpWindowManager.show_docstring_help(self.help_target, parent=self)
                elif self.param_name:
                    # Show parameter help using the description passed from parameter analysis
                    HelpWindowManager.show_parameter_help(
                        self.param_name, self.param_description or "No description available", self.param_type, parent=self
                    )

                self.help_requested.emit()

            except Exception as e:
                logger.error(f"Failed to show help: {e}")
                raise

        super().mousePressEvent(event)




class HelpButton(QPushButton):
    """PyQt6 help button for adding help functionality to any widget - mirrors Textual TUI."""

    def __init__(self, help_target: Union[Callable, type] = None,
                 param_name: str = None, param_description: str = None,
                 param_type: type = None, text: str = "Help",
                 color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        super().__init__(text, parent)

        # Initialize color scheme
        self.color_scheme = color_scheme or PyQt6ColorScheme()

        self.help_target = help_target
        self.param_name = param_name
        self.param_description = param_description
        self.param_type = param_type

        # Connect click to help display
        self.clicked.connect(self.show_help)

        # Style as help button
        self.setMaximumWidth(60)
        self._apply_color(self.color_scheme.selection_bg)

    def _apply_color(self, color) -> None:
        """Apply a color to this button (for scope accent styling)."""
        if hasattr(color, 'name'):
            # QColor
            hex_color = color.name()
            hex_lighter = color.lighter(115).name()
            hex_darker = color.darker(115).name()
        else:
            # Tuple or color scheme color
            hex_color = self.color_scheme.to_hex(color)
            hex_lighter = hex_color  # Can't lighten without QColor
            hex_darker = hex_color

        self.setStyleSheet(f"""
            QPushButton {{
                background-color: {hex_color};
                color: white;
                border: none;
                padding: 4px 8px;
                border-radius: 3px;
                font-weight: bold;
            }}
            QPushButton:hover {{
                background-color: {hex_lighter};
            }}
            QPushButton:pressed {{
                background-color: {hex_darker};
            }}
        """)

    def set_scope_accent_color(self, color) -> None:
        """Set scope accent color (QColor). Called by parent window for scope styling."""
        self._apply_color(color)

    def show_help(self):
        """Show help using the unified help manager - reuses Textual TUI logic."""
        try:
            # Import inside method to avoid circular imports (same pattern as Textual TUI)
            from openhcs.pyqt_gui.windows.help_windows import HelpWindowManager

            if self.help_target:
                # Show function/class help using unified manager
                HelpWindowManager.show_docstring_help(self.help_target, parent=self)
            elif self.param_name:
                # Show parameter help using the description passed from parameter analysis
                HelpWindowManager.show_parameter_help(
                    self.param_name, self.param_description or "No description available", self.param_type, parent=self
                )

        except Exception as e:
            logger.error(f"Failed to show help: {e}")
            raise




class LabelWithHelp(QWidget):
    """PyQt6 widget that combines a label with a help indicator - mirrors Textual TUI pattern."""

    def __init__(self, text: str, help_target: Union[Callable, type] = None,
                 param_name: str = None, param_description: str = None,
                 param_type: type = None, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        super().__init__(parent)

        # Initialize color scheme
        self.color_scheme = color_scheme or PyQt6ColorScheme()

        # Fixed size policy prevents horizontal stretching
        # This fixes flash area blocking for widgets to the right (e.g., checkbox groups)
        from PyQt6.QtWidgets import QSizePolicy
        self.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)

        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(5)

        # Main label - store as instance variable for font weight updates
        self._label = QLabel(text)
        layout.addWidget(self._label)

        # Help indicator
        help_indicator = HelpIndicator(
            help_target=help_target,
            param_name=param_name,
            param_description=param_description,
            param_type=param_type,
            color_scheme=self.color_scheme
        )
        layout.addWidget(help_indicator)

        layout.addStretch()

    def set_underline(self, underline: bool) -> None:
        """Set label underline based on whether value is concrete (not None/placeholder)."""
        font = self._label.font()
        font.setUnderline(underline)
        self._label.setFont(font)


class FunctionTitleWithHelp(QWidget):
    """PyQt6 function title with integrated help - mirrors Textual TUI ClickableFunctionTitle."""

    def __init__(self, func: Callable, index: int = None,
                 color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        super().__init__(parent)

        # Initialize color scheme
        self.color_scheme = color_scheme or PyQt6ColorScheme()

        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(10)

        # Function title
        func_name = getattr(func, '__name__', 'Unknown Function')
        module_name = getattr(func, '__module__', '').split('.')[-1] if func else ''

        title = f"{index + 1}: {func_name}" if index is not None else func_name
        if module_name:
            title += f" ({module_name})"

        title_label = QLabel(title)
        title_font = QFont()
        title_font.setBold(True)
        title_label.setFont(title_font)
        layout.addWidget(title_label)

        # Help button
        help_btn = HelpButton(help_target=func, text="?", color_scheme=self.color_scheme)
        help_btn.setMaximumWidth(25)
        help_btn.setMaximumHeight(20)
        layout.addWidget(help_btn)

        layout.addStretch()


class GroupBoxWithHelp(FlashableGroupBox):
    """PyQt6 group box with integrated help for dataclass titles - mirrors Textual TUI pattern.

    Inherits from FlashableGroupBox to support smooth flash animations.
    Uses PAINT-TIME color computation via manager.get_flash_color_for_key().
    Supports scope-based borders matching window border patterns.
    """

    # Border patterns matching ScopedBorderMixin
    BORDER_PATTERNS = {
        "solid": (Qt.PenStyle.SolidLine, None),
        "dashed": (Qt.PenStyle.DashLine, [8, 6]),
        "dotted": (Qt.PenStyle.DotLine, [2, 6]),
        "dashdot": (Qt.PenStyle.DashDotLine, [8, 4, 2, 4]),
    }

    def __init__(self, title: str, help_target: Union[Callable, type] = None,
                 color_scheme: Optional[PyQt6ColorScheme] = None, parent=None,
                 flash_key: str = "", flash_manager=None):
        super().__init__("", parent, flash_key=flash_key, flash_manager=flash_manager)

        # Initialize color scheme
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.help_target = help_target

        # Scope border state (set via set_scope_color_scheme)
        self._scope_color_scheme = None

        # Create custom title widget with help
        title_widget = QWidget()
        title_layout = QHBoxLayout(title_widget)
        title_layout.setContentsMargins(0, 0, 0, 0)
        title_layout.setSpacing(5)

        # Title label
        title_label = QLabel(title)
        title_font = QFont()
        title_font.setBold(True)
        title_label.setFont(title_font)
        title_layout.addWidget(title_label)

        # Help button for dataclass (left-aligned, next to title)
        if help_target:
            help_btn = HelpButton(help_target=help_target, text="?", color_scheme=self.color_scheme)
            help_btn.setMaximumWidth(25)
            help_btn.setMaximumHeight(20)
            title_layout.addWidget(help_btn)

        title_layout.addStretch()

        # Store title_layout so we can add more widgets later (e.g., reset button)
        self.title_layout = title_layout

        # Create main layout and add title widget at top
        # NOTE: Let Qt use default spacing - matches main branch behavior
        main_layout = QVBoxLayout(self)
        main_layout.addWidget(title_widget)

        # Content area for child widgets
        self.content_layout = QVBoxLayout()
        main_layout.addLayout(self.content_layout)

    def set_scope_color_scheme(self, scheme) -> None:
        """Set scope color scheme for border rendering."""
        import logging
        logger = logging.getLogger(__name__)
        logger.info(f"🎨 GroupBoxWithHelp.set_scope_color_scheme: title='{self.title()}', scheme={scheme is not None}")
        self._scope_color_scheme = scheme
        # Add margin for border layers if needed
        if scheme and hasattr(scheme, 'step_border_layers') and scheme.step_border_layers:
            total_width = sum(layer[0] for layer in scheme.step_border_layers)
            logger.info(f"🎨 GroupBoxWithHelp: Setting margins to {total_width} for border layers")
            self.setContentsMargins(total_width, total_width, total_width, total_width)
        self.update()

    def paintEvent(self, event) -> None:
        """Paint with scope background and border layers if set."""
        super().paintEvent(event)
        if not self._scope_color_scheme:
            return

        layers = getattr(self._scope_color_scheme, 'step_border_layers', None)

        # Paint scope background tint (same approach as list item delegate)
        self._paint_scope_background(layers)

        # Paint border layers on top
        if layers:
            self._paint_border_layers(layers)

    def _paint_scope_background(self, layers) -> None:
        """Paint subtle scope-colored background (matching list item style)."""
        from openhcs.pyqt_gui.widgets.shared.scope_color_utils import tint_color_perceptual
        from openhcs.pyqt_gui.widgets.shared.scope_visual_config import ScopeVisualConfig
        from openhcs.pyqt_gui.widgets.shared.flash_mixin import get_widget_corner_radius, DEFAULT_CORNER_RADIUS

        base_rgb = getattr(self._scope_color_scheme, 'base_color_rgb', None)
        if not base_rgb:
            return

        # Get tint index from first layer (or default)
        if layers:
            _, tint_idx, _ = (layers[0] + ("solid",))[:3]
        else:
            tint_idx = 1

        color = tint_color_perceptual(base_rgb, tint_idx)
        color.setAlphaF(ScopeVisualConfig.GROUPBOX_BG_OPACITY)

        # Get border rect (accounts for margin-top offset)
        rect = self._get_border_rect()

        # Get corner radius for rounded background
        radius = get_widget_corner_radius(self)
        if radius == 0:
            radius = DEFAULT_CORNER_RADIUS

        # Calculate content rect (inside borders)
        border_inset = sum(layer[0] for layer in layers) if layers else 0
        content_rect = rect.adjusted(border_inset, border_inset, -border_inset, -border_inset)

        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(color)
        painter.drawRoundedRect(QRectF(content_rect), radius - border_inset, radius - border_inset)
        painter.end()

    def _get_border_rect(self) -> QRect:
        """Get the painted area rect, accounting for margin-top offset.

        Uses the same geometry calculation as the flash overlay system
        for consistent visual alignment.
        """
        import re
        rect = self.rect()

        # Extract margin-top from stylesheet (same logic as flash overlay)
        margin_top = 0
        stylesheet = self.styleSheet()
        if not stylesheet:
            parent = self.parentWidget()
            while parent:
                stylesheet = parent.styleSheet()
                if stylesheet and 'QGroupBox' in stylesheet:
                    break
                parent = parent.parentWidget()

        if stylesheet:
            match = re.search(r'margin-top\s*:\s*(\d+)', stylesheet)
            if match:
                margin_top = int(match.group(1))

        # Adjust rect to match painted area (offset by margin-top, reduce height)
        return QRect(rect.x(), rect.y() + margin_top, rect.width(), rect.height() - margin_top)

    def _paint_border_layers(self, layers) -> None:
        """Paint layered scope borders (same algorithm as ScopedBorderMixin).

        Uses _get_border_rect() for geometry matching flash overlay.
        """
        from openhcs.pyqt_gui.widgets.shared.scope_color_utils import tint_color_perceptual

        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)

        # Use flash-compatible geometry
        rect = self._get_border_rect()
        inset = 0
        base_rgb = self._scope_color_scheme.base_color_rgb

        # Get corner radius from stylesheet for rounded borders
        from openhcs.pyqt_gui.widgets.shared.flash_mixin import get_widget_corner_radius, DEFAULT_CORNER_RADIUS
        radius = get_widget_corner_radius(self)
        if radius == 0:
            radius = DEFAULT_CORNER_RADIUS

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
            draw_rect = rect.adjusted(offset, offset, -offset - 1, -offset - 1)
            # Draw rounded rect to match flash overlay geometry
            painter.drawRoundedRect(QRectF(draw_rect), radius, radius)
            inset += width

        painter.end()

    def addWidget(self, widget):
        """Add widget to the content area."""
        self.content_layout.addWidget(widget)

    def addLayout(self, layout):
        """Add layout to the content area."""
        self.content_layout.addLayout(layout)

    def addTitleWidget(self, widget):
        """Add widget to the title area, right-aligned (after the stretch)."""
        # Add at the end (right-aligned, after the stretch)
        self.title_layout.addWidget(widget)
