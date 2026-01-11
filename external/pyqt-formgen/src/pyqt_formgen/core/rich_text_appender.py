"""Utility for appending HTML content to QTextEdit with proper cursor/scroll handling."""

import html
from typing import Optional
from PyQt6.QtWidgets import QTextEdit
from PyQt6.QtGui import QTextCursor

from pyqt_formgen.theming import ColorScheme


class RichTextAppender:
    """
    Utility for appending HTML content to QTextEdit with proper cursor/scroll handling.

    Usage:
        appender = RichTextAppender(self.chat_history, color_scheme=self.color_scheme)
        appender.append_html("<b>User:</b> Hello")
        appender.append_code("def foo(): pass")
        appender.append_error("Something went wrong")
    """

    def __init__(self, text_edit: QTextEdit, color_scheme: ColorScheme = None):
        self._text_edit = text_edit
        self._color_scheme = color_scheme or ColorScheme()
        self._border_color = self._color_scheme.to_hex(self._color_scheme.border_color)
        self._success_color = self._color_scheme.to_hex(self._color_scheme.status_success)
        self._error_color = self._color_scheme.to_hex(self._color_scheme.status_error)

    def append_html(self, html_content: str, add_spacing: bool = True):
        """
        Append HTML content at end, scroll to bottom.

        Args:
            html_content: HTML string to append
            add_spacing: Whether to add blank line after
        """
        cursor = self._text_edit.textCursor()
        cursor.movePosition(QTextCursor.MoveOperation.End)
        self._text_edit.setTextCursor(cursor)

        self._text_edit.insertHtml(html_content)

        if add_spacing:
            self._text_edit.insertHtml("<br><br>")

        self._scroll_to_bottom()

    def append_text(self, text: str, bold: bool = False, color: Optional[str] = None):
        """
        Append plain text (escaped) with optional styling.

        Args:
            text: Plain text to append
            bold: Whether to make text bold
            color: Optional text color (hex)
        """
        escaped = html.escape(text)

        if bold:
            escaped = f"<b>{escaped}</b>"
        if color:
            escaped = f"<span style='color: {color};'>{escaped}</span>"

        self.append_html(escaped)

    def append_code(self, code: str, language: str = None):
        """
        Append code block with border styling.

        Args:
            code: Code string to display
            language: Optional language hint (for future syntax highlighting)
        """
        escaped = html.escape(code)
        html_block = f"""
        <pre style="
            border: 1px solid {self._border_color};
            padding: 8px;
            margin: 4px 0;
            font-family: 'Courier New', monospace;
            white-space: pre-wrap;
            word-wrap: break-word;
        ">{escaped}</pre>
        """
        self.append_html(html_block, add_spacing=False)

    def append_error(self, message: str):
        """Append error message in red."""
        self.append_text(message, bold=True, color=self._error_color)

    def append_success(self, message: str):
        """Append success message in green."""
        self.append_text(message, bold=True, color=self._success_color)

    def clear(self):
        """Clear all content."""
        self._text_edit.clear()

    def _scroll_to_bottom(self):
        """Scroll text edit to bottom."""
        scrollbar = self._text_edit.verticalScrollBar()
        scrollbar.setValue(scrollbar.maximum())

