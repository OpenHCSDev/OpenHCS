"""
PyQt6 Log Viewer Window

Provides comprehensive log viewing capabilities with real-time tailing, search functionality,
and integration with OpenHCS subprocess execution. Reimplements log viewing using Qt widgets
for native desktop integration.
"""

import logging
from typing import Optional, List, Set, Tuple
from pathlib import Path

from PyQt6.QtWidgets import (
    QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QComboBox,
    QListView, QToolBar, QLineEdit, QCheckBox, QPushButton, QDialog,
    QStyledItemDelegate, QAbstractItemView, QApplication, QStyleOptionViewItem,
    QStyle, QPlainTextEdit,
)
from PyQt6.QtGui import QSyntaxHighlighter, QTextDocument
from PyQt6.QtCore import (
    QObject, QTimer, QFileSystemWatcher, pyqtSignal, pyqtSlot,
    Qt, QRegularExpression, QThread, QAbstractListModel, QModelIndex, QSize,
    QThreadPool, QRunnable, QPoint, QPointF,
)
from PyQt6.QtGui import QTextCharFormat, QColor, QAction, QFont, QTextCursor, QPalette, QAbstractTextDocumentLayout

from openhcs.io.filemanager import FileManager
from openhcs.core.log_utils import LogFileInfo
from openhcs.pyqt_gui.utils.log_detection_utils import (
    get_current_tui_log_path, discover_logs, discover_all_logs
)
from openhcs.core.log_utils import (
    classify_log_file, is_openhcs_log_file, infer_base_log_path
)
from openhcs.pyqt_gui.utils.process_tracker import (
    ProcessTracker, extract_pid_from_log_filename, get_log_display_name, get_log_tooltip
)

# Import Pygments for advanced syntax highlighting
from pygments import highlight
from pygments.lexers import PythonLexer, get_lexer_by_name
from pygments.formatters import get_formatter_by_name
from pygments.token import Token
from pygments.style import Style
from pygments.styles import get_style_by_name
from dataclasses import dataclass
from typing import Dict, Tuple

logger = logging.getLogger(__name__)


@dataclass
class LogColorScheme:
    """
    Centralized color scheme for log highlighting with semantic color names.

    Supports light/dark theme variants and ensures WCAG accessibility compliance.
    All colors meet minimum 4.5:1 contrast ratio for normal text readability.
    """

    # Log level colors with semantic meaning (WCAG 4.5:1 compliant)
    log_critical_fg: Tuple[int, int, int] = (255, 255, 255)  # White text
    log_critical_bg: Tuple[int, int, int] = (139, 0, 0)      # Dark red background
    log_error_color: Tuple[int, int, int] = (255, 85, 85)    # Brighter red - WCAG compliant
    log_warning_color: Tuple[int, int, int] = (255, 140, 0)  # Dark orange - attention grabbing
    log_info_color: Tuple[int, int, int] = (100, 160, 210)   # Brighter steel blue - WCAG compliant
    log_debug_color: Tuple[int, int, int] = (160, 160, 160)  # Lighter gray - better contrast

    # Metadata and structural colors
    timestamp_color: Tuple[int, int, int] = (105, 105, 105)      # Dim gray - unobtrusive
    logger_name_color: Tuple[int, int, int] = (147, 112, 219)   # Medium slate blue - distinctive
    memory_address_color: Tuple[int, int, int] = (255, 182, 193) # Light pink - technical data
    file_path_color: Tuple[int, int, int] = (34, 139, 34)       # Forest green - file system

    # Python syntax colors (following VS Code dark theme conventions)
    python_keyword_color: Tuple[int, int, int] = (86, 156, 214)    # Blue - language keywords
    python_string_color: Tuple[int, int, int] = (206, 145, 120)    # Orange - string literals
    python_number_color: Tuple[int, int, int] = (181, 206, 168)    # Light green - numeric values
    python_operator_color: Tuple[int, int, int] = (212, 212, 212)  # Light gray - operators/punctuation
    python_name_color: Tuple[int, int, int] = (156, 220, 254)      # Light blue - identifiers
    python_function_color: Tuple[int, int, int] = (220, 220, 170)  # Yellow - function names
    python_class_color: Tuple[int, int, int] = (78, 201, 176)      # Teal - class names
    python_builtin_color: Tuple[int, int, int] = (86, 156, 214)    # Blue - built-in functions
    python_comment_color: Tuple[int, int, int] = (106, 153, 85)    # Green - comments

    # Special highlighting colors
    exception_color: Tuple[int, int, int] = (255, 69, 0)       # Red orange - error types
    function_call_color: Tuple[int, int, int] = (255, 215, 0)  # Gold - function invocations
    boolean_color: Tuple[int, int, int] = (86, 156, 214)       # Blue - True/False/None

    # Enhanced syntax colors (Phase 1 additions)
    tuple_parentheses_color: Tuple[int, int, int] = (255, 215, 0)     # Gold - tuple delimiters
    set_braces_color: Tuple[int, int, int] = (255, 140, 0)            # Dark orange - set delimiters
    class_representation_color: Tuple[int, int, int] = (78, 201, 176) # Teal - <class 'name'>
    function_representation_color: Tuple[int, int, int] = (220, 220, 170) # Yellow - <function name>
    module_path_color: Tuple[int, int, int] = (147, 112, 219)         # Medium slate blue - module.path
    hex_number_color: Tuple[int, int, int] = (181, 206, 168)          # Light green - 0xFF
    scientific_notation_color: Tuple[int, int, int] = (181, 206, 168) # Light green - 1.23e-4
    binary_number_color: Tuple[int, int, int] = (181, 206, 168)       # Light green - 0b1010
    octal_number_color: Tuple[int, int, int] = (181, 206, 168)        # Light green - 0o755
    python_special_color: Tuple[int, int, int] = (255, 20, 147)       # Deep pink - __name__
    single_quoted_string_color: Tuple[int, int, int] = (206, 145, 120) # Orange - 'string'
    list_comprehension_color: Tuple[int, int, int] = (156, 220, 254)  # Light blue - [x for x in y]
    generator_expression_color: Tuple[int, int, int] = (156, 220, 254) # Light blue - (x for x in y)

    @classmethod
    def create_dark_theme(cls) -> 'LogColorScheme':
        """
        Create a dark theme variant with adjusted colors for dark backgrounds.

        Returns:
            LogColorScheme: Dark theme color scheme with higher contrast
        """
        return cls(
            # Enhanced colors for dark backgrounds with better contrast
            log_error_color=(255, 100, 100),    # Brighter red
            log_info_color=(120, 180, 230),     # Brighter steel blue
            timestamp_color=(160, 160, 160),    # Lighter gray
            python_string_color=(236, 175, 150), # Brighter orange
            python_number_color=(200, 230, 190), # Brighter green
            # Other colors remain the same as they work well on dark backgrounds
        )

    @classmethod
    def create_light_theme(cls) -> 'LogColorScheme':
        """
        Create a light theme variant with adjusted colors for light backgrounds.

        Returns:
            LogColorScheme: Light theme color scheme with appropriate contrast
        """
        return cls(
            # Darker colors for light backgrounds with WCAG compliance
            log_error_color=(180, 20, 40),       # Darker red
            log_info_color=(30, 80, 130),        # Darker steel blue
            log_warning_color=(200, 100, 0),     # Darker orange
            timestamp_color=(60, 60, 60),        # Darker gray
            logger_name_color=(100, 60, 160),    # Darker slate blue
            python_string_color=(150, 80, 60),   # Darker orange
            python_number_color=(120, 140, 100), # Darker green
            memory_address_color=(200, 120, 140), # Darker pink
            file_path_color=(20, 100, 20),       # Darker forest green
            exception_color=(200, 40, 0),        # Darker red orange
            # Adjust other colors for light background contrast
        )

    def to_qcolor(self, color_tuple: Tuple[int, int, int]) -> QColor:
        """Convert RGB tuple to QColor object.

        Args:
            color_tuple: RGB color tuple (r, g, b)

        Returns:
            QColor: Corresponding QColor instance.
        """
        r, g, b = color_tuple
        return QColor(r, g, b)

class LogListModel(QAbstractListModel):
    """Lightweight list model storing log lines in a bounded ring buffer.

    The model is pure data; rendering and highlighting are handled by a
    delegate on top of this model.
    """

    MAX_LINES = 100_000

    def __init__(self, parent: Optional[QObject] = None):
        super().__init__(parent)
        self._lines: List[str] = []

    def rowCount(self, parent: QModelIndex = QModelIndex()) -> int:  # type: ignore[override]
        if parent.isValid():
            return 0
        return len(self._lines)

    def data(self, index: QModelIndex, role: int = Qt.ItemDataRole.DisplayRole):  # type: ignore[override]
        if not index.isValid():
            return None
        row = index.row()
        if row < 0 or row >= len(self._lines):
            return None
        if role == Qt.ItemDataRole.DisplayRole:
            return self._lines[row]
        return None

    def clear(self) -> None:
        """Clear all stored lines."""
        if not self._lines:
            return
        self.beginResetModel()
        self._lines.clear()
        self.endResetModel()

    def append_lines(self, lines: List[str]) -> None:
        """Append new lines, enforcing the MAX_LINES ring buffer constraint."""
        if not lines:
            return

        new_total = len(self._lines) + len(lines)
        if new_total > self.MAX_LINES:
            remove_count = new_total - self.MAX_LINES
            if remove_count >= len(self._lines):
                # Replace entire buffer with newest lines only.
                self.beginResetModel()
                self._lines = lines[-self.MAX_LINES :]
                self.endResetModel()
                return

            # Drop oldest lines.
            self.beginRemoveRows(QModelIndex(), 0, remove_count - 1)
            del self._lines[:remove_count]
            self.endRemoveRows()

        start_row = len(self._lines)
        end_row = start_row + len(lines) - 1
        self.beginInsertRows(QModelIndex(), start_row, end_row)
        self._lines.extend(lines)
        self.endInsertRows()

    def iter_lines(self) -> List[str]:
        """Expose lines for read-only access (e.g., search)."""
        return self._lines


@dataclass
class HighlightedSegment:
    """A segment of text with formatting information."""
    start: int
    length: int
    color: Tuple[int, int, int]
    bold: bool = False
    italic: bool = False


class SelectableDocument(QTextDocument):
    """
    QTextDocument wrapper that manages text cursor and selection state.

    Enables text selection within QListView delegate items by tracking cursor position
    and applying visual selection highlighting using QTextCharFormat.

    Based on Qt Forum solution for interactive elements in delegates.
    """

    def __init__(self, parent: Optional[QObject] = None) -> None:
        super().__init__(parent)
        self.setDocumentMargin(0)
        self._text_cursor = QTextCursor(self)
        self._selected_word_on_double_click = QTextCursor(self)

    def selectionStart(self) -> int:
        """Get the start position of the current selection."""
        return self._text_cursor.selectionStart()

    def selectionEnd(self) -> int:
        """Get the end position of the current selection."""
        return self._text_cursor.selectionEnd()

    def setCursorPosition(self, pos: int, mode: QTextCursor.MoveMode = QTextCursor.MoveMode.MoveAnchor) -> None:
        """
        Set cursor position and update selection highlighting.

        Args:
            pos: Character position in document
            mode: MoveAnchor (clear selection) or KeepAnchor (extend selection)
        """
        # Clear previous selection highlighting
        if self._text_cursor.hasSelection():
            self._clearSelection()

        # Update cursor position
        self._text_cursor.setPosition(pos, mode)

        # Apply selection highlighting if we have a selection
        if self._text_cursor.hasSelection():
            self._highlightSelection()

    def moveCursorPosition(
        self,
        op: QTextCursor.MoveOperation,
        mode: QTextCursor.MoveMode = QTextCursor.MoveMode.MoveAnchor,
        n: int = 1
    ) -> bool:
        """
        Move cursor by operation and update highlighting.

        Args:
            op: Move operation (e.g., StartOfWord, EndOfWord)
            mode: MoveAnchor or KeepAnchor
            n: Number of times to repeat operation

        Returns:
            True if move was successful
        """
        # Clear previous selection highlighting
        if self._text_cursor.hasSelection():
            self._clearSelection()

        # Move cursor
        result = self._text_cursor.movePosition(op, mode, n)

        # Apply selection highlighting if we have a selection
        if self._text_cursor.hasSelection():
            self._highlightSelection()

        return result

    def select(self, selection: QTextCursor.SelectionType) -> None:
        """
        Select text by type (word, line, etc.) and update highlighting.

        Args:
            selection: Type of selection (WordUnderCursor, LineUnderCursor, Document)
        """
        # Clear previous selection highlighting
        if self._text_cursor.hasSelection():
            self._clearSelection()

        # Select text
        self._text_cursor.select(selection)

        # Store the word selection for word-wise extension during drag
        self._selected_word_on_double_click = QTextCursor(self._text_cursor)

        # Apply selection highlighting
        if self._text_cursor.hasSelection():
            self._highlightSelection()

    def extendWordwiseSelection(self, newPos: int) -> None:
        """
        Extend selection to word boundaries when dragging after double-click.

        This implements the behavior where double-clicking selects a word, then
        dragging extends the selection by whole words rather than characters.

        Args:
            newPos: New cursor position from mouse drag
        """
        # Clear previous selection highlighting
        if self._text_cursor.hasSelection():
            self._clearSelection()

        tempCursor = QTextCursor(self._text_cursor)
        tempCursor.setPosition(newPos, QTextCursor.MoveMode.KeepAnchor)

        # Move to start of word at new position
        if not tempCursor.movePosition(QTextCursor.MoveOperation.StartOfWord):
            return
        wordStartPos = tempCursor.position()

        # Move to end of word at new position
        if not tempCursor.movePosition(QTextCursor.MoveOperation.EndOfWord):
            return
        wordEndPos = tempCursor.position()

        # Extend selection to word boundary based on drag direction
        if newPos < self._selected_word_on_double_click.position():
            # Dragging left - extend to start of word
            self._text_cursor.setPosition(self._text_cursor.selectionEnd())
            self._text_cursor.setPosition(wordStartPos, QTextCursor.MoveMode.KeepAnchor)
        else:
            # Dragging right - extend to end of word
            self._text_cursor.setPosition(self._text_cursor.selectionStart())
            self._text_cursor.setPosition(wordEndPos, QTextCursor.MoveMode.KeepAnchor)

        # Apply selection highlighting
        if self._text_cursor.hasSelection():
            self._highlightSelection()

    def selectedText(self) -> str:
        """Get the currently selected text."""
        return self._text_cursor.selectedText()

    def _clearSelection(self) -> None:
        """
        Remove selection highlighting from the previously selected region.

        This preserves the underlying syntax highlighting by only clearing
        the background color that was added for selection.
        """
        if not self._text_cursor.hasSelection():
            return

        # Create a cursor for the selected region
        clearCursor = QTextCursor(self._text_cursor)

        # Create format that only clears background (preserves foreground/syntax colors)
        clearFormat = QTextCharFormat()
        clearFormat.setBackground(QColor(0, 0, 0, 0))  # Transparent background

        # Apply to selected region
        clearCursor.setCharFormat(clearFormat)

    def _highlightSelection(self) -> None:
        """
        Apply visual selection highlighting using system palette colors.

        This only modifies the background color, preserving the syntax highlighting
        foreground colors.
        """
        if not self._text_cursor.hasSelection():
            return

        # Create a cursor for the selected region
        highlightCursor = QTextCursor(self._text_cursor)

        # Create format that only sets background (preserves foreground/syntax colors)
        selectFormat = QTextCharFormat()
        selectFormat.setBackground(QApplication.palette().highlight().color())
        # Don't set foreground - preserve syntax highlighting colors

        # Apply to selected region
        highlightCursor.setCharFormat(selectFormat)


class HighlightSignals(QObject):
    """Signals for background highlighting worker."""
    finished = pyqtSignal(object, object)  # (cache_key, List[HighlightedSegment])


class HighlightWorker(QRunnable):
    """Background worker that does expensive regex parsing to extract formatting info.

    This runs all the expensive regex matching in a background thread and returns
    just the formatting information (which segments should be what color).
    The main thread then applies this to a QTextDocument.
    """

    def __init__(self, text: str, cache_key: Tuple[str, str, int],
                 color_scheme: LogColorScheme, signals: HighlightSignals):
        super().__init__()
        self.text = text
        self.cache_key = cache_key
        self.color_scheme = color_scheme
        self.signals = signals

    def run(self):
        """Parse text and extract formatting information in background thread."""
        segments = self._parse_log_line(self.text)
        self.signals.finished.emit(self.cache_key, segments)

    def _parse_log_line(self, text: str) -> List[HighlightedSegment]:
        """
        Parse a log line and return formatting segments.

        This duplicates the regex logic from LogHighlighter but returns
        structured data instead of applying to QTextDocument.
        """
        segments = []
        cs = self.color_scheme

        # Timestamp pattern (start of line)
        import re
        timestamp_pattern = r'^\d{4}-\d{2}-\d{2}\s+\d{2}:\d{2}:\d{2},\d{3}'
        match = re.match(timestamp_pattern, text)
        if match:
            segments.append(HighlightedSegment(
                start=match.start(),
                length=match.end() - match.start(),
                color=cs.timestamp_color
            ))

        # Log level (ERROR, WARNING, INFO, DEBUG)
        level_pattern = r'\b(ERROR|WARNING|INFO|DEBUG|CRITICAL)\b'
        for match in re.finditer(level_pattern, text):
            level = match.group(1)
            if level == 'ERROR' or level == 'CRITICAL':
                color = cs.log_error_color
            elif level == 'WARNING':
                color = cs.log_warning_color
            else:
                color = cs.log_info_color

            segments.append(HighlightedSegment(
                start=match.start(),
                length=match.end() - match.start(),
                color=color,
                bold=True
            ))

        # Logger name pattern (between timestamp and level)
        logger_pattern = r' - ([\w\.]+) - '
        for match in re.finditer(logger_pattern, text):
            segments.append(HighlightedSegment(
                start=match.start(1),
                length=match.end(1) - match.start(1),
                color=cs.logger_name_color
            ))

        # File paths
        path_pattern = r'(?:/[\w\-\.]+)+\.py'
        for match in re.finditer(path_pattern, text):
            segments.append(HighlightedSegment(
                start=match.start(),
                length=match.end() - match.start(),
                color=cs.file_path_color
            ))

        # Python strings
        string_pattern = r'["\'](?:[^"\'\\]|\\.)*["\']'
        for match in re.finditer(string_pattern, text):
            segments.append(HighlightedSegment(
                start=match.start(),
                length=match.end() - match.start(),
                color=cs.python_string_color
            ))

        # Numbers
        number_pattern = r'\b\d+(?:\.\d+)?\b'
        for match in re.finditer(number_pattern, text):
            segments.append(HighlightedSegment(
                start=match.start(),
                length=match.end() - match.start(),
                color=cs.python_number_color
            ))

        return segments


class LogItemDelegate(QStyledItemDelegate):
    """Delegate responsible for per-line coloring, regex-based syntax, and search highlighting.

    We avoid document-wide highlighting and instead reuse the existing
    LogHighlighter rules on a per-line QTextDocument that is only used
    for visible rows. This keeps work bounded by visible rows and line
    length, independent of total log size.

    Performance optimization:
    1. Cache highlighted QTextDocuments to avoid re-running expensive regex highlighting
    2. Perform highlighting in background thread pool to never block UI
    3. Paint with plain text if highlighting not ready yet (progressive enhancement)
    """

    # Cache configuration
    MAX_CACHE_SIZE = 10000  # Maximum number of unique lines to cache

    def __init__(
        self,
        color_scheme: Optional[LogColorScheme] = None,
        parent: Optional[QWidget] = None,
    ) -> None:
        super().__init__(parent)
        self._color_scheme = color_scheme or LogColorScheme.create_dark_theme()
        self._search_text: str = ""
        self._case_sensitive: bool = False

        # Thread pool for background highlighting
        self._thread_pool = QThreadPool.globalInstance()

        # Signals for background workers
        self._highlight_signals = HighlightSignals()
        self._highlight_signals.finished.connect(self._on_highlighting_finished)

        # Cache: maps (text, font_family, font_size) -> List[HighlightedSegment]
        # Stores the parsed formatting information from background thread
        self._segment_cache: Dict[Tuple[str, str, int], List[HighlightedSegment]] = {}
        self._cache_access_order: List[Tuple[str, str, int]] = []  # LRU tracking

        # Track which lines are being highlighted in background
        self._pending_highlights: Set[Tuple[str, str, int]] = set()

        # Text selection state - support multi-line selection
        self._interactive_documents: Dict[int, SelectableDocument] = {}  # Map row -> document with selection

    def set_search_state(self, text: str, case_sensitive: bool) -> None:
        """Update search text used for line-level search highlighting."""
        self._search_text = text or ""
        self._case_sensitive = case_sensitive

    def hasInteractiveDocument(self, row: int) -> bool:
        """Check if a row has an interactive document with selection."""
        return row in self._interactive_documents

    def getInteractiveDocument(self, row: int) -> Optional[SelectableDocument]:
        """Get the interactive document for a specific row."""
        return self._interactive_documents.get(row)

    def setInteractiveDocument(self, row: int, doc: SelectableDocument) -> None:
        """Set the interactive document for a specific row."""
        self._interactive_documents[row] = doc

    def clearInteractiveDocuments(self) -> None:
        """Clear all interactive documents."""
        self._interactive_documents.clear()

    def createInteractiveDocument(self, text: str, font: QFont) -> SelectableDocument:
        """
        Create a SelectableDocument with syntax highlighting applied.

        This is used by LogListView when creating a new interactive document
        for text selection. It applies the same syntax highlighting as normal
        rendering.

        Args:
            text: The log line text
            font: The font to use for rendering

        Returns:
            SelectableDocument with syntax highlighting applied
        """
        # Create the selectable document
        doc = SelectableDocument()
        doc.setDefaultFont(font)
        doc.setPlainText(text)

        # Try to get cached formatting segments
        segments = self._get_or_request_segments(text, font)

        if segments is not None:
            # Apply syntax highlighting
            self._apply_segments_to_document(doc, segments)

        return doc

    def _on_highlighting_finished(self, cache_key: Tuple[str, str, int],
                                   segments: List[HighlightedSegment]) -> None:
        """
        Cache formatting segments when background parsing completes.

        Args:
            cache_key: Cache key for this line
            segments: List of formatting segments from background thread
        """
        # Remove from pending set
        self._pending_highlights.discard(cache_key)

        # Add to cache
        self._segment_cache[cache_key] = segments
        self._cache_access_order.append(cache_key)

        # Enforce cache size limit (LRU eviction)
        if len(self._segment_cache) > self.MAX_CACHE_SIZE:
            oldest_key = self._cache_access_order.pop(0)
            del self._segment_cache[oldest_key]

        # Trigger repaint for this line
        if self.parent() and isinstance(self.parent(), QListView):
            self.parent().viewport().update()

    def _get_or_request_segments(self, text: str, font: QFont) -> Optional[List[HighlightedSegment]]:
        """
        Get cached formatting segments or start async parsing.

        This dramatically improves paint performance by:
        1. Running expensive regex parsing in background thread (never blocks UI)
        2. Caching the results for instant reuse
        3. Returning None if not ready (caller paints plain text as fallback)

        Args:
            text: The log line text
            font: The font to use for rendering

        Returns:
            List[HighlightedSegment] if cached/ready, None if still parsing in background
        """
        # Create cache key from text and font properties
        cache_key = (text, font.family(), font.pointSize())

        # Check cache first
        if cache_key in self._segment_cache:
            # Move to end of access order (LRU)
            self._cache_access_order.remove(cache_key)
            self._cache_access_order.append(cache_key)
            return self._segment_cache[cache_key]

        # Not in cache - start async parsing if not already pending
        if cache_key not in self._pending_highlights:
            self._pending_highlights.add(cache_key)
            worker = HighlightWorker(text, cache_key, self._color_scheme, self._highlight_signals)
            self._thread_pool.start(worker)

        # Return None - caller will paint plain text until parsing completes
        return None

    def _apply_segments_to_document(self, doc: QTextDocument, segments: List[HighlightedSegment]) -> None:
        """
        Apply formatting segments to a QTextDocument (on main thread).

        Args:
            doc: Document to format
            segments: Formatting segments from background parsing
        """
        cursor = QTextCursor(doc)

        for segment in segments:
            # Select the segment
            cursor.setPosition(segment.start)
            cursor.setPosition(segment.start + segment.length, QTextCursor.MoveMode.KeepAnchor)

            # Create format
            fmt = QTextCharFormat()
            fmt.setForeground(QColor(*segment.color))
            if segment.bold:
                fmt.setFontWeight(QFont.Weight.Bold)
            if segment.italic:
                fmt.setFontItalic(True)

            # Apply format
            cursor.setCharFormat(fmt)

    def paint(self, painter, option, index):  # type: ignore[override]
        opt = QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)

        text = opt.text

        # Apply search highlight as a background brush if the current line matches.
        if self._search_text:
            haystack = text if self._case_sensitive else text.lower()
            needle = self._search_text if self._case_sensitive else self._search_text.lower()
            if needle and needle in haystack:
                highlight_color = QColor(255, 255, 0, 60)
                opt.backgroundBrush = highlight_color

        # Draw the item background/selection/borders without any text.
        style = opt.widget.style() if opt.widget is not None else QApplication.style()
        original_text = opt.text
        opt.text = ""
        style.drawControl(QStyle.ControlElement.CE_ItemViewItem, opt, painter, opt.widget)
        opt.text = original_text

        # Check if this row has an interactive document with text selection
        row = index.row()
        if self.hasInteractiveDocument(row):
            # Use the interactive document which has selection state
            doc = self.getInteractiveDocument(row)
            if doc is not None:
                doc.setTextWidth(opt.rect.width())
            else:
                # Fallback to normal rendering
                segments = self._get_or_request_segments(text, opt.font)
                doc = QTextDocument()
                doc.setDefaultFont(opt.font)
                doc.setPlainText(text)
                doc.setTextWidth(opt.rect.width())
                if segments is not None:
                    self._apply_segments_to_document(doc, segments)
        else:
            # Normal rendering: create temporary document with syntax highlighting
            # Try to get cached formatting segments (async, may return None)
            segments = self._get_or_request_segments(text, opt.font)

            # Create document on main thread (fast, just allocation)
            doc = QTextDocument()
            doc.setDefaultFont(opt.font)
            doc.setPlainText(text)
            doc.setTextWidth(opt.rect.width())

            if segments is not None:
                # Formatting ready - apply it (fast, just setting char formats)
                self._apply_segments_to_document(doc, segments)
            # else: No formatting yet, paint plain text (still readable while parsing)

        # Paint the document
        context = QAbstractTextDocumentLayout.PaintContext()
        context.palette = opt.palette

        painter.save()
        painter.translate(opt.rect.topLeft())
        painter.setClipRect(0, 0, opt.rect.width(), opt.rect.height())
        doc.documentLayout().draw(painter, context)
        painter.restore()

    def sizeHint(self, option, index):  # type: ignore[override]
        """Return height large enough to show wrapped text for this row.

        We compute the document layout for the current line using the
        available viewport width so that long log lines wrap instead of
        being clipped or forcing a horizontal scrollbar.
        """
        text = index.data(Qt.DisplayRole)
        if text is None:
            return super().sizeHint(option, index)

        opt = QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)

        # Determine available width for wrapping. Prefer the parent
        # QListView viewport width when possible so row heights respond
        # to window resizing.
        width = opt.rect.width()
        parent = self.parent()
        if width <= 0 and isinstance(parent, QListView) and parent.viewport() is not None:
            width = parent.viewport().width()
        if width <= 0:
            width = 800  # conservative fallback, not critical for layout

        # Create simple document for size calculation (formatting doesn't affect size)
        doc = QTextDocument()
        doc.setDefaultFont(opt.font)
        doc.setPlainText(str(text))
        doc.setTextWidth(width)
        doc_size = doc.size()
        height = int(doc_size.height())

        # Add a small vertical padding so text is not flush with borders.
        return QSize(width, height + 4)

    def clear_cache(self) -> None:
        """Clear the segment cache. Call this when resetting the log viewer."""
        self._segment_cache.clear()
        self._cache_access_order.clear()
        self._pending_highlights.clear()
        logger.debug("LogItemDelegate cache cleared")


class LogListView(QListView):
    """
    Custom QListView that enables text selection within and across items.

    Handles mouse events to track cursor position in QTextDocument and manage
    text selection state. Supports single-line and multi-line selection.
    Works in conjunction with LogItemDelegate to paint selection highlighting.

    Based on Qt Forum solution for interactive elements in delegates.
    """

    def __init__(self, parent: Optional[QWidget] = None) -> None:
        super().__init__(parent)

        # State for tracking text selection
        self._selection_start_index = QModelIndex()  # Row where selection started
        self._selection_end_index = QModelIndex()  # Row where selection ends
        self._selection_start_pos = 0  # Character position where selection started
        self._selection_end_pos = 0  # Character position where selection ends
        self._is_selecting = False  # Whether we're currently selecting
        self._word_selection = False  # Whether in word-wise selection mode (double-click)

        # Auto-scroll when dragging selection past edges
        self._auto_scroll_timer = QTimer()
        self._auto_scroll_timer.timeout.connect(self._auto_scroll_during_selection)
        self._auto_scroll_distance = 0  # Distance from edge in pixels (negative = up, positive = down)
        self._last_mouse_pos = QPoint()  # Track mouse position for auto-scroll

        # Enable mouse tracking for cursor changes
        self.setMouseTracking(True)

    def mousePressEvent(self, event) -> None:  # type: ignore[override]
        """Handle mouse press to start text selection."""
        mousePos = event.pos()
        clickedIndex = self.indexAt(mousePos)

        if not clickedIndex.isValid():
            event.accept()
            return

        # Clear any previous selection
        self._clearSelection()

        # Get text for this row
        text = clickedIndex.data(Qt.ItemDataRole.DisplayRole)
        if text is None:
            event.accept()
            return

        # Calculate character position at mouse click
        itemRect = self.visualRect(clickedIndex)
        relativePos = mousePos - itemRect.topLeft()
        relativePosF = QPointF(relativePos)

        # Create temporary document to calculate cursor position
        tempDoc = QTextDocument()
        tempDoc.setDefaultFont(self.font())
        tempDoc.setPlainText(str(text))
        tempDoc.setTextWidth(itemRect.width())
        charPos = tempDoc.documentLayout().hitTest(relativePosF, Qt.HitTestAccuracy.FuzzyHit)

        # Start selection
        self._selection_start_index = clickedIndex
        self._selection_end_index = clickedIndex
        self._selection_start_pos = charPos
        self._selection_end_pos = charPos
        self._is_selecting = True
        self._word_selection = False

        # Update display
        self._updateSelection()

        # Don't call super() - we don't want QListView's row selection behavior
        event.accept()

    def mouseMoveEvent(self, event) -> None:  # type: ignore[override]
        """Handle mouse move to update cursor icon and extend selection."""
        mousePos = event.pos()
        self._last_mouse_pos = mousePos

        # Update cursor icon based on whether we're over a valid item
        if self.indexAt(mousePos).isValid():
            if not QApplication.overrideCursor() or QApplication.overrideCursor().shape() != Qt.CursorShape.IBeamCursor:
                QApplication.setOverrideCursor(Qt.CursorShape.IBeamCursor)
        else:
            QApplication.restoreOverrideCursor()

        # If left button is pressed and we're selecting, update selection
        if self._is_selecting and (event.buttons() & Qt.MouseButton.LeftButton):
            # Check if mouse is past viewport edges for auto-scrolling
            viewport_rect = self.viewport().rect()
            scroll_margin = 50  # Pixels from edge to start scrolling

            if mousePos.y() < 0:
                # Mouse is above viewport - calculate distance from top
                # Distance is negative (how far above), speed increases with distance
                self._auto_scroll_distance = mousePos.y()  # Negative value
                if not self._auto_scroll_timer.isActive():
                    self._auto_scroll_timer.start(50)  # Scroll every 50ms
            elif mousePos.y() > viewport_rect.height():
                # Mouse is below viewport - calculate distance from bottom
                # Distance is positive (how far below), speed increases with distance
                self._auto_scroll_distance = mousePos.y() - viewport_rect.height()  # Positive value
                if not self._auto_scroll_timer.isActive():
                    self._auto_scroll_timer.start(50)
            elif mousePos.y() < scroll_margin:
                # Mouse is near top edge but still inside - slow scroll up
                # Map 0-50px to 0-1.0 factor
                factor = 1.0 - (mousePos.y() / scroll_margin)
                self._auto_scroll_distance = -scroll_margin * factor
                if not self._auto_scroll_timer.isActive():
                    self._auto_scroll_timer.start(50)
            elif mousePos.y() > viewport_rect.height() - scroll_margin:
                # Mouse is near bottom edge but still inside - slow scroll down
                # Map (height-50)-height to 0-1.0 factor
                distance_from_bottom = viewport_rect.height() - mousePos.y()
                factor = 1.0 - (distance_from_bottom / scroll_margin)
                self._auto_scroll_distance = scroll_margin * factor
                if not self._auto_scroll_timer.isActive():
                    self._auto_scroll_timer.start(50)
            else:
                # Mouse is within safe zone - stop auto-scrolling
                self._auto_scroll_timer.stop()
                self._auto_scroll_distance = 0

            currentIndex = self.indexAt(mousePos)

            if not currentIndex.isValid():
                # Mouse is outside items but we're still selecting - keep last valid index
                event.accept()
                return

            # Get text for current row
            text = currentIndex.data(Qt.ItemDataRole.DisplayRole)
            if text is None:
                event.accept()
                return

            # Calculate character position at current mouse position
            itemRect = self.visualRect(currentIndex)
            relativePos = mousePos - itemRect.topLeft()
            relativePosF = QPointF(relativePos)

            # Create temporary document to calculate cursor position
            tempDoc = QTextDocument()
            tempDoc.setDefaultFont(self.font())
            tempDoc.setPlainText(str(text))
            tempDoc.setTextWidth(itemRect.width())
            charPos = tempDoc.documentLayout().hitTest(relativePosF, Qt.HitTestAccuracy.FuzzyHit)

            # Update selection end
            self._selection_end_index = currentIndex
            self._selection_end_pos = charPos

            # Update display
            self._updateSelection()

            event.accept()
        else:
            # Not selecting - stop auto-scroll
            self._auto_scroll_timer.stop()
            self._auto_scroll_distance = 0
            super().mouseMoveEvent(event)

    def mouseDoubleClickEvent(self, event) -> None:  # type: ignore[override]
        """Handle double-click to select word."""
        # TODO: Implement word selection for multi-line selection
        # For now, just accept the event
        event.accept()

    def mouseReleaseEvent(self, event) -> None:  # type: ignore[override]
        """Handle mouse release to copy selected text to clipboard."""
        if self._is_selecting:
            # Stop auto-scrolling
            self._auto_scroll_timer.stop()
            self._auto_scroll_distance = 0

            # Get selected text and copy to clipboard
            selectedText = self._getSelectedText()
            if selectedText:
                QApplication.clipboard().setText(selectedText)

            self._is_selecting = False

        # Don't call super() - we don't want QListView's row selection behavior
        event.accept()

    def _auto_scroll_during_selection(self) -> None:
        """Auto-scroll the view when dragging selection past edges.

        Scroll speed is proportional to distance from viewport edge:
        - Inside viewport near edge (0-50px): Slow scroll (0-100% of base speed)
        - Outside viewport: Fast scroll (proportional to distance, max 10x base speed)
        """
        if not self._is_selecting or self._auto_scroll_distance == 0:
            return

        scrollbar = self.verticalScrollBar()
        current_value = scrollbar.value()

        # Base scroll speed in pixels per tick
        base_speed = 3
        max_speed_multiplier = 50

        # Calculate scroll speed based on distance from edge
        if abs(self._auto_scroll_distance) <= 50:
            # Near edge but inside viewport - proportional slow scroll
            scroll_pixels = base_speed * (abs(self._auto_scroll_distance) / 50)
        else:
            # Outside viewport - faster scroll proportional to distance
            # Map distance to speed multiplier (50-200px → 1x-10x)
            distance_outside = abs(self._auto_scroll_distance) - 50
            multiplier = min(max_speed_multiplier, 1 + (distance_outside / 150) * (max_speed_multiplier - 1))
            scroll_pixels = base_speed * multiplier

        # Apply direction
        if self._auto_scroll_distance < 0:
            # Scroll up
            new_value = max(0, current_value - int(scroll_pixels))
            scrollbar.setValue(new_value)
        else:
            # Scroll down
            new_value = min(scrollbar.maximum(), current_value + int(scroll_pixels))
            scrollbar.setValue(new_value)

        # Update selection with current mouse position
        if self._last_mouse_pos:
            currentIndex = self.indexAt(self._last_mouse_pos)
            if currentIndex.isValid():
                text = currentIndex.data(Qt.ItemDataRole.DisplayRole)
                if text is not None:
                    itemRect = self.visualRect(currentIndex)
                    relativePos = self._last_mouse_pos - itemRect.topLeft()
                    relativePosF = QPointF(relativePos)

                    tempDoc = QTextDocument()
                    tempDoc.setDefaultFont(self.font())
                    tempDoc.setPlainText(str(text))
                    tempDoc.setTextWidth(itemRect.width())
                    charPos = tempDoc.documentLayout().hitTest(relativePosF, Qt.HitTestAccuracy.FuzzyHit)

                    self._selection_end_index = currentIndex
                    self._selection_end_pos = charPos
                    self._updateSelection()

    def _clearSelection(self) -> None:
        """Clear the current selection."""
        delegate = self.itemDelegate()
        if isinstance(delegate, LogItemDelegate):
            # Clear all interactive documents
            delegate.clearInteractiveDocuments()

        # Repaint previously selected rows
        if self._selection_start_index.isValid() and self._selection_end_index.isValid():
            startRow = self._selection_start_index.row()
            endRow = self._selection_end_index.row()
            minRow = min(startRow, endRow)
            maxRow = max(startRow, endRow)

            for row in range(minRow, maxRow + 1):
                index = self.model().index(row, 0)
                self.update(index)

        # Reset selection state
        self._selection_start_index = QModelIndex()
        self._selection_end_index = QModelIndex()
        self._selection_start_pos = 0
        self._selection_end_pos = 0
        self._is_selecting = False

    def _updateSelection(self) -> None:
        """Update the visual selection based on current selection state."""
        if not self._selection_start_index.isValid():
            return

        delegate = self.itemDelegate()
        if not isinstance(delegate, LogItemDelegate):
            return

        # Clear previous interactive documents
        delegate.clearInteractiveDocuments()

        # Determine selection range (start and end might be in different order)
        startRow = self._selection_start_index.row()
        endRow = self._selection_end_index.row()

        # Determine forward or backward selection
        if startRow < endRow or (startRow == endRow and self._selection_start_pos <= self._selection_end_pos):
            # Forward selection
            firstRow = startRow
            firstPos = self._selection_start_pos
            lastRow = endRow
            lastPos = self._selection_end_pos
        else:
            # Backward selection
            firstRow = endRow
            firstPos = self._selection_end_pos
            lastRow = startRow
            lastPos = self._selection_start_pos

        # Create documents for each selected line
        for row in range(firstRow, lastRow + 1):
            index = self.model().index(row, 0)
            text = index.data(Qt.ItemDataRole.DisplayRole)
            if text is None:
                continue

            # Create SelectableDocument with syntax highlighting
            doc = delegate.createInteractiveDocument(str(text), self.font())

            if row == firstRow and row == lastRow:
                # Single-line selection
                doc.setCursorPosition(firstPos)
                doc.setCursorPosition(lastPos, QTextCursor.MoveMode.KeepAnchor)
            elif row == firstRow:
                # First line - select from start position to end
                doc.setCursorPosition(firstPos)
                doc.setCursorPosition(len(str(text)), QTextCursor.MoveMode.KeepAnchor)
            elif row == lastRow:
                # Last line - select from beginning to end position
                doc.setCursorPosition(0)
                doc.setCursorPosition(lastPos, QTextCursor.MoveMode.KeepAnchor)
            else:
                # Middle lines - select entire line
                doc.setCursorPosition(0)
                doc.setCursorPosition(len(str(text)), QTextCursor.MoveMode.KeepAnchor)

            # Store document for this row
            delegate.setInteractiveDocument(row, doc)

            # Repaint this row
            self.update(index)

    def _getSelectedText(self) -> str:
        """Get the currently selected text."""
        if not self._selection_start_index.isValid():
            return ""

        startRow = self._selection_start_index.row()
        endRow = self._selection_end_index.row()

        if startRow == endRow:
            # Single-line selection
            text = self._selection_start_index.data(Qt.ItemDataRole.DisplayRole)
            if text is None:
                return ""

            minPos = min(self._selection_start_pos, self._selection_end_pos)
            maxPos = max(self._selection_start_pos, self._selection_end_pos)
            return str(text)[minPos:maxPos]
        else:
            # Multi-line selection
            minRow = min(startRow, endRow)
            maxRow = max(startRow, endRow)

            # Determine if we're selecting forward or backward
            if startRow < endRow or (startRow == endRow and self._selection_start_pos < self._selection_end_pos):
                # Forward selection
                firstRow = startRow
                firstPos = self._selection_start_pos
                lastRow = endRow
                lastPos = self._selection_end_pos
            else:
                # Backward selection
                firstRow = endRow
                firstPos = self._selection_end_pos
                lastRow = startRow
                lastPos = self._selection_start_pos

            lines = []
            for row in range(firstRow, lastRow + 1):
                index = self.model().index(row, 0)
                text = index.data(Qt.ItemDataRole.DisplayRole)
                if text is None:
                    continue

                textStr = str(text)
                if row == firstRow:
                    # First line - take from start position to end
                    lines.append(textStr[firstPos:])
                elif row == lastRow:
                    # Last line - take from beginning to end position
                    lines.append(textStr[:lastPos])
                else:
                    # Middle lines - take entire line
                    lines.append(textStr)

            return "\n".join(lines)


class LogFileDetector(QObject):
    """
    Detects new log files in directory using efficient file monitoring.

    Uses QFileSystemWatcher to monitor directory changes and set operations
    for efficient new file detection. Handles base_log_path as file prefix
    and watches the parent directory.
    """

    # Signals
    new_log_detected = pyqtSignal(object)  # LogFileInfo object
    _server_scan_complete = pyqtSignal(list)  # List of LogFileInfo from server scan

    def __init__(self, base_log_path: Optional[str] = None):
        """
        Initialize LogFileDetector.

        Args:
            base_log_path: Base path for subprocess log files (file prefix, not directory)
        """
        super().__init__()
        self._base_log_path = base_log_path
        self._previous_files: Set[Path] = set()
        self._watcher = QFileSystemWatcher()
        self._watcher.directoryChanged.connect(self._on_directory_changed)
        self._watching_directory: Optional[Path] = None

        logger.debug(f"LogFileDetector initialized with base_log_path: {base_log_path}")

    def start_watching(self, directory: Path) -> None:
        """
        Start watching directory for new log files.

        Args:
            directory: Directory to watch for new log files
        """
        if not directory.exists():
            logger.warning(f"Cannot watch non-existent directory: {directory}")
            return

        # Stop any existing watching
        self.stop_watching()

        # Add directory to watcher
        success = self._watcher.addPath(str(directory))
        if success:
            self._watching_directory = directory
            # Initialize previous files set
            self._previous_files = self.scan_directory(directory)
            logger.debug(f"Started watching directory: {directory}")
            logger.debug(f"Initial file count: {len(self._previous_files)}")
        else:
            logger.error(f"Failed to add directory to watcher: {directory}")

    def stop_watching(self) -> None:
        """Stop file watching and cleanup."""
        if self._watching_directory:
            self._watcher.removePath(str(self._watching_directory))
            self._watching_directory = None
            self._previous_files.clear()
            logger.debug("Stopped file watching")

    def scan_directory(self, directory: Path) -> Set[Path]:
        """
        Scan directory for .log files.

        Args:
            directory: Directory to scan

        Returns:
            Set[Path]: Set of Path objects for .log files found
        """
        try:
            log_files = set(directory.glob("*.log"))
            logger.debug(f"Scanned directory {directory}: found {len(log_files)} .log files")
            return log_files
        except (FileNotFoundError, PermissionError) as e:
            logger.warning(f"Error scanning directory {directory}: {e}")
            return set()

    def detect_new_files(self, current_files: Set[Path]) -> Set[Path]:
        """
        Use set.difference() to find new files efficiently.

        Args:
            current_files: Current set of files in directory

        Returns:
            Set[Path]: Set of newly discovered files
        """
        new_files = current_files.difference(self._previous_files)
        if new_files:
            logger.debug(f"Detected {len(new_files)} new files: {[f.name for f in new_files]}")

        # Update previous files set
        self._previous_files = current_files
        return new_files



    def _on_directory_changed(self, directory_path: str) -> None:
        """
        Handle QFileSystemWatcher directory change signal.

        Args:
            directory_path: Path of directory that changed
        """
        directory = Path(directory_path)
        logger.debug(f"Directory changed: {directory}")

        # Scan directory for current files
        current_files = self.scan_directory(directory)

        # Detect new files
        new_files = self.detect_new_files(current_files)

        # Process new files
        for file_path in new_files:
            if file_path.exists() and is_openhcs_log_file(file_path):
                try:
                    # For general watching, try to infer base_log_path from the file name
                    effective_base_log_path = self._base_log_path
                    if not effective_base_log_path and 'subprocess_' in file_path.name:
                        effective_base_log_path = infer_base_log_path(file_path)

                    log_info = classify_log_file(file_path, effective_base_log_path,
                                                include_tui_log=False)

                    logger.info(f"New relevant log file detected: {file_path} (type: {log_info.log_type})")
                    self.new_log_detected.emit(log_info)
                except Exception as e:
                    logger.error(f"Error classifying new log file {file_path}: {e}")


class LogHighlighter(QSyntaxHighlighter):
    """
    Advanced syntax highlighter for log files using Pygments.

    Provides sophisticated highlighting for OpenHCS log format with support for:
    - Log levels and timestamps
    - Python code snippets and data structures
    - Memory addresses and function signatures
    - Complex nested dictionaries and lists
    - Exception tracebacks and file paths
    """

    def __init__(self, parent: QTextDocument, color_scheme: LogColorScheme = None):
        """
        Initialize the log highlighter with optional color scheme.

        Args:
            parent: QTextDocument to apply highlighting to
            color_scheme: Color scheme to use (defaults to dark theme)
        """
        super().__init__(parent)
        self.color_scheme = color_scheme or LogColorScheme()
        self.setup_pygments_styles()
        self.setup_highlighting_rules()

    def setup_pygments_styles(self) -> None:
        """Setup Pygments token to QTextCharFormat mapping using color scheme."""
        cs = self.color_scheme  # Shorthand for readability

        # Create a mapping from Pygments tokens to Qt text formats
        self.token_formats = {
            # Log levels with distinct colors and backgrounds
            'log_critical': self._create_format(
                cs.to_qcolor(cs.log_critical_fg),
                cs.to_qcolor(cs.log_critical_bg),
                bold=True
            ),
            'log_error': self._create_format(cs.to_qcolor(cs.log_error_color), bold=True),
            'log_warning': self._create_format(cs.to_qcolor(cs.log_warning_color), bold=True),
            'log_info': self._create_format(cs.to_qcolor(cs.log_info_color), bold=True),
            'log_debug': self._create_format(cs.to_qcolor(cs.log_debug_color)),

            # Timestamps and metadata
            'timestamp': self._create_format(cs.to_qcolor(cs.timestamp_color)),
            'logger_name': self._create_format(cs.to_qcolor(cs.logger_name_color), bold=True),

            # Python syntax highlighting (for complex data structures)
            Token.Keyword: self._create_format(cs.to_qcolor(cs.python_keyword_color), bold=True),
            Token.String: self._create_format(cs.to_qcolor(cs.python_string_color)),
            Token.String.Single: self._create_format(cs.to_qcolor(cs.python_string_color)),
            Token.String.Double: self._create_format(cs.to_qcolor(cs.python_string_color)),
            Token.Number: self._create_format(cs.to_qcolor(cs.python_number_color)),
            Token.Number.Integer: self._create_format(cs.to_qcolor(cs.python_number_color)),
            Token.Number.Float: self._create_format(cs.to_qcolor(cs.python_number_color)),
            Token.Number.Hex: self._create_format(cs.to_qcolor(cs.python_number_color)),
            Token.Number.Oct: self._create_format(cs.to_qcolor(cs.python_number_color)),
            Token.Number.Bin: self._create_format(cs.to_qcolor(cs.python_number_color)),
            Token.Operator: self._create_format(cs.to_qcolor(cs.python_operator_color)),
            Token.Punctuation: self._create_format(cs.to_qcolor(cs.python_operator_color)),
            Token.Name: self._create_format(cs.to_qcolor(cs.python_name_color)),
            Token.Name.Function: self._create_format(cs.to_qcolor(cs.python_function_color), bold=True),
            Token.Name.Class: self._create_format(cs.to_qcolor(cs.python_class_color), bold=True),
            Token.Name.Builtin: self._create_format(cs.to_qcolor(cs.python_builtin_color)),
            Token.Comment: self._create_format(cs.to_qcolor(cs.python_comment_color)),
            Token.Literal: self._create_format(cs.to_qcolor(cs.python_number_color)),

            # Special patterns for log content
            'memory_address': self._create_format(cs.to_qcolor(cs.memory_address_color)),
            'file_path': self._create_format(cs.to_qcolor(cs.file_path_color)),
            'exception': self._create_format(cs.to_qcolor(cs.exception_color), bold=True),
            'function_call': self._create_format(cs.to_qcolor(cs.function_call_color)),
            'dict_key': self._create_format(cs.to_qcolor(cs.python_name_color)),
            'boolean': self._create_format(cs.to_qcolor(cs.boolean_color), bold=True),

            # Enhanced Python syntax elements (Phase 1)
            'tuple_parentheses': self._create_format(cs.to_qcolor(cs.tuple_parentheses_color)),
            'set_braces': self._create_format(cs.to_qcolor(cs.set_braces_color)),
            'class_representation': self._create_format(cs.to_qcolor(cs.class_representation_color), bold=True),
            'function_representation': self._create_format(cs.to_qcolor(cs.function_representation_color), bold=True),
            'module_path': self._create_format(cs.to_qcolor(cs.module_path_color)),
            'hex_number': self._create_format(cs.to_qcolor(cs.hex_number_color)),
            'scientific_notation': self._create_format(cs.to_qcolor(cs.scientific_notation_color)),
            'binary_number': self._create_format(cs.to_qcolor(cs.binary_number_color)),
            'octal_number': self._create_format(cs.to_qcolor(cs.octal_number_color)),
            'python_special': self._create_format(cs.to_qcolor(cs.python_special_color), bold=True),
            'single_quoted_string': self._create_format(cs.to_qcolor(cs.single_quoted_string_color)),
            'list_comprehension': self._create_format(cs.to_qcolor(cs.list_comprehension_color)),
            'generator_expression': self._create_format(cs.to_qcolor(cs.generator_expression_color)),
        }

    def _create_format(self, fg_color: QColor, bg_color: QColor = None, bold: bool = False) -> QTextCharFormat:
        """Create a QTextCharFormat with specified properties."""
        format = QTextCharFormat()
        format.setForeground(fg_color)
        if bg_color:
            format.setBackground(bg_color)
        if bold:
            format.setFontWeight(QFont.Weight.Bold)
        return format

    def setup_highlighting_rules(self) -> None:
        """Setup regex patterns for log-specific highlighting."""
        self.highlighting_rules = []

        # Log level patterns (highest priority)
        log_levels = [
            ("CRITICAL", self.token_formats['log_critical']),
            ("ERROR", self.token_formats['log_error']),
            ("WARNING", self.token_formats['log_warning']),
            ("INFO", self.token_formats['log_info']),
            ("DEBUG", self.token_formats['log_debug']),
        ]

        for level, format in log_levels:
            pattern = QRegularExpression(rf"\b{level}\b")
            self.highlighting_rules.append((pattern, format))

        # Timestamp pattern: YYYY-MM-DD HH:MM:SS,mmm
        timestamp_pattern = QRegularExpression(r"\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2},\d{3}")
        self.highlighting_rules.append((timestamp_pattern, self.token_formats['timestamp']))

        # Logger names (e.g., openhcs.core.orchestrator)
        logger_pattern = QRegularExpression(r"openhcs\.[a-zA-Z0-9_.]+")
        self.highlighting_rules.append((logger_pattern, self.token_formats['logger_name']))

        # Memory addresses (e.g., 0x7f1640dd8e00)
        memory_pattern = QRegularExpression(r"0x[0-9a-fA-F]+")
        self.highlighting_rules.append((memory_pattern, self.token_formats['memory_address']))

        # File paths in tracebacks
        filepath_pattern = QRegularExpression(r'["\']?/[^"\'\s]+\.py["\']?')
        self.highlighting_rules.append((filepath_pattern, self.token_formats['file_path']))

        # Exception names
        exception_pattern = QRegularExpression(r'\b[A-Z][a-zA-Z]*Error\b|\b[A-Z][a-zA-Z]*Exception\b')
        self.highlighting_rules.append((exception_pattern, self.token_formats['exception']))

        # Function calls with parentheses
        function_pattern = QRegularExpression(r'\b[a-zA-Z_][a-zA-Z0-9_]*\(\)')
        self.highlighting_rules.append((function_pattern, self.token_formats['function_call']))

        # Boolean values
        boolean_pattern = QRegularExpression(r'\b(True|False|None)\b')
        self.highlighting_rules.append((boolean_pattern, self.token_formats['boolean']))

        # Enhanced Python syntax elements

        # Single-quoted strings (complement to double-quoted)
        single_quote_pattern = QRegularExpression(r"'[^']*'")
        self.highlighting_rules.append((single_quote_pattern, self.token_formats['single_quoted_string']))

        # Class representations: <class 'module.ClassName'>
        class_repr_pattern = QRegularExpression(r"<class '[^']*'>")
        self.highlighting_rules.append((class_repr_pattern, self.token_formats['class_representation']))

        # Function representations: <function name at 0xaddress>
        function_repr_pattern = QRegularExpression(r"<function [^>]+ at 0x[0-9a-fA-F]+>")
        self.highlighting_rules.append((function_repr_pattern, self.token_formats['function_representation']))

        # Extended module paths (beyond just openhcs)
        module_path_pattern = QRegularExpression(r"\b[a-zA-Z_][a-zA-Z0-9_]*(?:\.[a-zA-Z_][a-zA-Z0-9_]*){2,}")
        self.highlighting_rules.append((module_path_pattern, self.token_formats['module_path']))

        # Hexadecimal numbers (beyond memory addresses): 0xFF, 0x1A2B
        hex_number_pattern = QRegularExpression(r"\b0[xX][0-9a-fA-F]+\b")
        self.highlighting_rules.append((hex_number_pattern, self.token_formats['hex_number']))

        # Scientific notation: 1.23e-4, 5.67E+10
        scientific_pattern = QRegularExpression(r"\b\d+\.?\d*[eE][+-]?\d+\b")
        self.highlighting_rules.append((scientific_pattern, self.token_formats['scientific_notation']))

        # Binary literals: 0b1010
        binary_pattern = QRegularExpression(r"\b0[bB][01]+\b")
        self.highlighting_rules.append((binary_pattern, self.token_formats['binary_number']))

        # Octal literals: 0o755
        octal_pattern = QRegularExpression(r"\b0[oO][0-7]+\b")
        self.highlighting_rules.append((octal_pattern, self.token_formats['octal_number']))

        # Python special constants: __name__, __main__, __file__, etc.
        python_special_pattern = QRegularExpression(r"\b__[a-zA-Z_][a-zA-Z0-9_]*__\b")
        self.highlighting_rules.append((python_special_pattern, self.token_formats['python_special']))

        logger.debug(f"Setup {len(self.highlighting_rules)} highlighting rules")

    def set_color_scheme(self, color_scheme: LogColorScheme) -> None:
        """
        Update the color scheme and refresh highlighting.

        Args:
            color_scheme: New color scheme to apply
        """
        self.color_scheme = color_scheme
        self.setup_pygments_styles()
        self.setup_highlighting_rules()
        # Trigger re-highlighting of the entire document
        self.rehighlight()
        logger.debug(f"Applied new color scheme with {len(self.token_formats)} token formats")

    def switch_to_dark_theme(self) -> None:
        """Switch to dark theme color scheme."""
        self.set_color_scheme(LogColorScheme.create_dark_theme())

    def switch_to_light_theme(self) -> None:
        """Switch to light theme color scheme."""
        self.set_color_scheme(LogColorScheme.create_light_theme())

    @classmethod
    def load_color_scheme_from_config(cls, config_path: str = None) -> LogColorScheme:
        """
        Load color scheme from external configuration file.

        Args:
            config_path: Path to JSON/YAML config file (optional)

        Returns:
            LogColorScheme: Loaded color scheme or default if file not found
        """
        if config_path and Path(config_path).exists():
            try:
                import json
                with open(config_path, 'r') as f:
                    config = json.load(f)

                # Create color scheme from config
                scheme_kwargs = {}
                for key, value in config.items():
                    if key.endswith('_color') or key.endswith('_fg') or key.endswith('_bg'):
                        if isinstance(value, list) and len(value) == 3:
                            scheme_kwargs[key] = tuple(value)

                return LogColorScheme(**scheme_kwargs)

            except Exception as e:
                logger.warning(f"Failed to load color scheme from {config_path}: {e}")

        return LogColorScheme()  # Return default scheme

    def highlightBlock(self, text: str) -> None:
        """
        Apply highlighting to text block using regex patterns.

        Uses regex patterns for log-specific content (timestamps, log levels, etc.).
        Fast and doesn't block the UI.
        """
        # Apply log-specific patterns
        for pattern, format in self.highlighting_rules:
            iterator = pattern.globalMatch(text)
            while iterator.hasNext():
                match = iterator.next()
                start = match.capturedStart()
                length = match.capturedLength()
                self.setFormat(start, length, format)


class LogFileLoader(QThread):
    """Background thread for loading large log files without blocking UI."""

    # Signals
    content_loaded = pyqtSignal(str)  # Emits file content when loaded
    load_failed = pyqtSignal(str)     # Emits error message on failure

    def __init__(self, log_path: Path):
        super().__init__()
        self.log_path = log_path

    def run(self):
        """Load file content in background thread."""
        try:
            with open(self.log_path, 'r', encoding='utf-8', errors='replace') as f:
                content = f.read()
            self.content_loaded.emit(content)
        except Exception as e:
            self.load_failed.emit(str(e))


class LogTailer(QThread):
    """Background thread for tailing log files without blocking UI."""

    # Signals
    new_content = pyqtSignal(str, int)  # Emits (new_content, new_file_position)
    log_rotated = pyqtSignal()  # Emits when log rotation detected
    error_occurred = pyqtSignal(str)  # Emits error message

    def __init__(self, log_path: Path, initial_position: int = 0):
        super().__init__()
        self.log_path = log_path
        self.file_position = initial_position
        self._running = False

    def run(self):
        """Continuously tail log file in background thread."""
        self._running = True

        while self._running:
            try:
                if not self.log_path.exists():
                    self.msleep(100)
                    continue

                # Get current file size
                current_size = self.log_path.stat().st_size

                # Handle log rotation (file size decreased)
                if current_size < self.file_position:
                    self.log_rotated.emit()
                    self.file_position = 0

                # Read new content if file grew
                if current_size > self.file_position:
                    with open(self.log_path, 'rb') as f:
                        f.seek(self.file_position)
                        new_data = f.read(current_size - self.file_position)

                    # Decode new content
                    try:
                        new_content = new_data.decode('utf-8', errors='replace')
                    except UnicodeDecodeError:
                        new_content = new_data.decode('latin-1', errors='replace')

                    if new_content:
                        self.new_content.emit(new_content, current_size)
                        self.file_position = current_size

            except (OSError, PermissionError) as e:
                self.error_occurred.emit(str(e))
            except Exception as e:
                self.error_occurred.emit(f"Unexpected error: {e}")

            # Sleep for 100ms before next check
            self.msleep(100)

    def stop(self):
        """Stop the tailing thread."""
        self._running = False


class LogViewerWindow(QMainWindow):
    """Main log viewer window with dropdown, search, and real-time tailing."""

    window_closed = pyqtSignal()
    _subprocess_scan_complete = pyqtSignal(list)  # Internal signal for async subprocess scan
    _server_scan_complete = pyqtSignal(list)  # Internal signal for async server scan

    def __init__(self, file_manager: FileManager, service_adapter, parent=None):
        super().__init__(parent)
        self.file_manager = file_manager
        self.service_adapter = service_adapter

        # State
        self.current_log_path: Optional[Path] = None
        self.current_file_position: int = 0
        self.auto_scroll_enabled: bool = True
        self.tailing_paused: bool = False
        self._pending_partial_line: str = ""

        # Search state
        self.current_search_text: str = ""
        self._search_case_sensitive: bool = False
        self._search_matches: List[int] = []
        self._search_match_cursor: int = -1

        # Update throttling to reduce UI load
        self._pending_lines: List[str] = []  # Buffer for pending log lines
        self._update_timer = QTimer()
        self._update_timer.setSingleShot(True)
        self._update_timer.timeout.connect(self._flush_pending_lines)
        self._update_throttle_ms = 50  # Minimum time between UI updates
        self._last_scroll_state = True  # Track if we were at bottom

        # Components
        self.log_selector: QComboBox = None
        self.search_toolbar: QToolBar = None
        self.log_view: QListView = None
        self.log_model: Optional[LogListModel] = None
        self.log_delegate: Optional[LogItemDelegate] = None
        self.file_detector: LogFileDetector = None
        self.tail_timer: QTimer = None  # Deprecated - kept for compatibility
        self.log_tailer: Optional[LogTailer] = None  # Async log tailer thread
        self.highlighter: Optional[LogHighlighter] = None
        self.file_loader: Optional[LogFileLoader] = None  # Async file loader
        self.server_scan_timer: QTimer = None  # Periodic ZMQ server scanning
        self._pending_log_to_load: Optional[Path] = None  # Log to load when window is shown

        # Process tracking for alive/dead process indication
        self.process_tracker = ProcessTracker()
        self.process_update_timer: QTimer = None
        self.show_alive_only: bool = False  # Filter to show only logs from running processes

        # Master list of all discovered logs (single source of truth)
        # Dropdown is a filtered VIEW of this list
        self._all_discovered_logs: List[LogFileInfo] = []

        # Track session start time to filter out old logs from previous sessions
        # Use current process start time, not log viewer init time
        self._session_start_time = self._get_process_start_time()

        self.setup_ui()
        self.setup_connections()
        self.initialize_logs()
        self.start_process_tracking()

    def setup_ui(self) -> None:
        """Setup complete UI layout with exact widget hierarchy."""
        self.setWindowTitle("Log Viewer")
        self.setMinimumSize(800, 600)

        # Central widget with main layout
        central_widget = QWidget()
        self.setCentralWidget(central_widget)
        main_layout = QVBoxLayout(central_widget)

        # Log selector dropdown
        self.log_selector = QComboBox()
        self.log_selector.setMinimumHeight(30)
        main_layout.addWidget(self.log_selector)

        # Search toolbar (initially hidden)
        self.search_toolbar = QToolBar("Search")
        self.search_toolbar.setVisible(False)

        # Search input
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("Search logs...")
        self.search_toolbar.addWidget(self.search_input)

        # Search options
        self.case_sensitive_cb = QCheckBox("Case sensitive")
        self.search_toolbar.addWidget(self.case_sensitive_cb)

        self.regex_cb = QCheckBox("Regex")
        self.search_toolbar.addWidget(self.regex_cb)

        # Search navigation buttons
        self.prev_button = QPushButton("Previous")
        self.next_button = QPushButton("Next")
        self.close_search_button = QPushButton("Close")

        self.search_toolbar.addWidget(self.prev_button)
        self.search_toolbar.addWidget(self.next_button)
        self.search_toolbar.addWidget(self.close_search_button)

        main_layout.addWidget(self.search_toolbar)

        # Log display area (virtualized with text selection support)
        self.log_model = LogListModel(self)
        self.log_view = LogListView()
        self.log_view.setModel(self.log_model)
        # Enable per-row word wrapping and variable item heights so long
        # log lines are fully visible instead of clipped or forcing
        # horizontal scrolling.
        self.log_view.setUniformItemSizes(False)
        self.log_view.setWordWrap(True)
        self.log_view.setResizeMode(QListView.ResizeMode.Adjust)
        self.log_view.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.log_view.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.log_view.setVerticalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
        self.log_view.setFont(QFont("Consolas", 10))  # Monospace font for logs
        self.log_delegate = LogItemDelegate(LogColorScheme.create_dark_theme(), self.log_view)
        self.log_view.setItemDelegate(self.log_delegate)
        main_layout.addWidget(self.log_view)

        # Control buttons layout
        control_layout = QHBoxLayout()

        self.auto_scroll_btn = QPushButton("Auto-scroll")
        self.auto_scroll_btn.setCheckable(True)
        self.auto_scroll_btn.setChecked(True)

        self.pause_btn = QPushButton("Pause")
        self.pause_btn.setCheckable(True)

        self.clear_btn = QPushButton("Clear")
        self.reset_memory_btn = QPushButton("Reset Memory")
        self.reset_memory_btn.setToolTip("Clear display and reset memory usage (reloads current log from disk)")
        self.bottom_btn = QPushButton("Bottom")

        # Process filter checkbox
        self.show_alive_only_cb = QCheckBox("Show only running processes")
        self.show_alive_only_cb.setToolTip("Filter logs to show only those from currently running processes")

        control_layout.addWidget(self.auto_scroll_btn)
        control_layout.addWidget(self.pause_btn)
        control_layout.addWidget(self.clear_btn)
        control_layout.addWidget(self.reset_memory_btn)
        control_layout.addWidget(self.bottom_btn)
        control_layout.addWidget(self.show_alive_only_cb)
        control_layout.addStretch()  # Push buttons to left

        main_layout.addLayout(control_layout)

        # Setup window-local Ctrl+F shortcut
        search_action = QAction("Search", self)
        search_action.setShortcut("Ctrl+F")
        search_action.triggered.connect(self.toggle_search_toolbar)
        self.addAction(search_action)

        logger.debug("LogViewerWindow UI setup complete")

    def setup_connections(self) -> None:
        """Setup signal/slot connections."""
        # Log selector
        self.log_selector.currentIndexChanged.connect(self.on_log_selection_changed)

        # Search functionality
        self.search_input.returnPressed.connect(self.perform_search)
        self.prev_button.clicked.connect(self.find_previous)
        self.next_button.clicked.connect(self.find_next)
        self.close_search_button.clicked.connect(self.toggle_search_toolbar)

        # Control buttons
        self.auto_scroll_btn.toggled.connect(self.toggle_auto_scroll)
        self.pause_btn.toggled.connect(self.toggle_pause_tailing)
        self.clear_btn.clicked.connect(self.clear_log_display)
        self.reset_memory_btn.clicked.connect(self.reset_memory)
        self.bottom_btn.clicked.connect(self.scroll_to_bottom)
        self.show_alive_only_cb.stateChanged.connect(self.on_filter_changed)

        # Internal signals
        self._subprocess_scan_complete.connect(self._on_subprocess_scan_complete)
        self._server_scan_complete.connect(self._on_server_scan_complete)

        logger.debug("LogViewerWindow connections setup complete")

    def showEvent(self, event):
        """Override showEvent to load log when window is first shown."""
        super().showEvent(event)

        # Load pending log on first show
        if self._pending_log_to_load:
            self.switch_to_log(self._pending_log_to_load)
            self._pending_log_to_load = None

    def initialize_logs(self) -> None:
        """Initialize with main log only, then scan for subprocess logs in background."""
        # Only discover the main log initially (fast startup)
        initial_logs = []
        try:
            from openhcs.core.log_utils import get_current_log_file_path, classify_log_file
            from pathlib import Path

            main_log_path = get_current_log_file_path()
            main_log = Path(main_log_path)
            if main_log.exists():
                log_info = classify_log_file(main_log, None, True)
                initial_logs.append(log_info)
                logger.debug("Discovered main log")
        except Exception as e:
            logger.warning(f"Error discovering main log: {e}")
            # Continue without main log
            pass

        # Store main log in master list
        self._all_discovered_logs = initial_logs.copy()

        # Populate dropdown with main log immediately (fast)
        if initial_logs:
            self.populate_log_dropdown(initial_logs)
            # Store first log to load when window is shown (defer loading)
            self._pending_log_to_load = initial_logs[0].path

        # Start monitoring for new logs
        self.start_monitoring()

        # Scan for existing subprocess logs in background (async - doesn't block)
        self._scan_subprocess_logs_async()

        # Scan for servers in background (async - doesn't block)
        self._scan_servers_async()

    def _scan_subprocess_logs_async(self) -> None:
        """Scan for existing subprocess logs in background thread (non-blocking)."""
        import threading

        def scan_and_update():
            """Background thread function."""
            subprocess_logs = self._scan_for_subprocess_logs()
            # Emit signal to update UI on main thread
            self._subprocess_scan_complete.emit(subprocess_logs)

        thread = threading.Thread(target=scan_and_update, daemon=True)
        thread.start()
        logger.debug("Started async subprocess log scan in background")

    def _scan_servers_async(self) -> None:
        """Scan for ZMQ servers in background thread (non-blocking)."""
        import threading

        def scan_and_update():
            """Background thread function."""
            server_logs = self._scan_for_server_logs()
            # Emit signal to update UI on main thread
            self._server_scan_complete.emit(server_logs)

        thread = threading.Thread(target=scan_and_update, daemon=True)
        thread.start()
        logger.debug("Started async server scan in background")

    @pyqtSlot(list)
    def _on_subprocess_scan_complete(self, subprocess_logs: List[LogFileInfo]) -> None:
        """Handle subprocess scan completion on UI thread."""
        if not subprocess_logs:
            logger.debug("No subprocess logs found during scan")
            return

        # Add subprocess logs to master list (avoid duplicates by path)
        existing_paths = {log.path for log in self._all_discovered_logs}
        new_logs_added = 0
        for subprocess_log in subprocess_logs:
            if subprocess_log.path not in existing_paths:
                self._all_discovered_logs.append(subprocess_log)
                new_logs_added += 1

        # Repopulate dropdown from master list
        self.populate_log_dropdown(self._all_discovered_logs)

        logger.info(f"Added {new_logs_added} subprocess logs from current session "
                   f"(scanned {len(subprocess_logs)} total)")

    @pyqtSlot(list)
    def _on_server_scan_complete(self, server_logs: List[LogFileInfo]) -> None:
        """Handle server scan completion on UI thread."""
        if not server_logs:
            logger.debug("No server logs found during scan")
            return

        # Add server logs to master list (avoid duplicates by path)
        existing_paths = {log.path for log in self._all_discovered_logs}
        new_logs_added = 0
        for server_log in server_logs:
            if server_log.path not in existing_paths:
                self._all_discovered_logs.append(server_log)
                new_logs_added += 1

        # Repopulate dropdown from master list
        self.populate_log_dropdown(self._all_discovered_logs)

        logger.info(f"Added {new_logs_added} new server logs to dropdown (scanned {len(server_logs)} total)")

    def _scan_for_subprocess_logs(self) -> List[LogFileInfo]:
        """
        Efficiently scan log directory for subprocess logs from current session.
        Uses os.scandir() and filters by mtime FIRST before parsing.
        Returns list of LogFileInfo for discovered subprocess log files.
        """
        from openhcs.core.log_utils import classify_log_file, is_openhcs_log_file
        from pathlib import Path
        import os

        logger.debug("Scanning for subprocess logs from current session...")

        try:
            # Get log directory
            log_dir = Path.home() / ".local" / "share" / "openhcs" / "logs"

            if not log_dir.exists():
                return []

            # Use os.scandir() for efficiency - it's faster than glob and gives us stat info
            session_logs = []
            total_scanned = 0
            filtered_by_time = 0

            # Calculate cutoff time (session start - 5 second buffer)
            cutoff_time = self._session_start_time - 5.0

            # Scan directory efficiently
            with os.scandir(log_dir) as entries:
                for entry in entries:
                    total_scanned += 1

                    # Skip non-.log files immediately
                    if not entry.name.endswith('.log'):
                        continue

                    # Filter by mtime FIRST (cheap filesystem check)
                    # This avoids parsing thousands of old log files
                    try:
                        stat_info = entry.stat()
                        if stat_info.st_mtime < cutoff_time:
                            filtered_by_time += 1
                            continue
                    except OSError:
                        continue

                    # Now check if it's an OpenHCS log (still just filename check, no file I/O)
                    log_path = Path(entry.path)
                    if not is_openhcs_log_file(log_path):
                        continue

                    # Finally, classify it (this is the expensive part, but we only do it for recent files)
                    try:
                        log_info = classify_log_file(log_path, None, include_tui_log=False)
                        session_logs.append(log_info)
                    except Exception as e:
                        logger.debug(f"Failed to classify {log_path}: {e}")

            logger.info(f"Found {len(session_logs)} subprocess logs from current session "
                       f"(scanned {total_scanned} files, filtered {filtered_by_time} by time)")

            return session_logs
        except Exception as e:
            logger.warning(f"Error scanning for subprocess logs: {e}")
            return []

    def _scan_for_server_logs(self) -> List[LogFileInfo]:
        """
        Scan for running ZMQ servers and Napari viewers by pinging common ports.
        Returns list of LogFileInfo for discovered server log files.
        """
        from openhcs.core.log_utils import classify_log_file
        from pathlib import Path
        import zmq
        import pickle

        logger.debug("Scanning for running ZMQ/streaming servers...")
        discovered_logs = []

        # Scan all streaming ports using current global config
        # This ensures we find viewers launched with custom ports
        from openhcs.core.config import get_all_streaming_ports
        ports_to_scan = get_all_streaming_ports(num_ports_per_type=10)  # Uses global config by default

        def ping_server(port: int) -> dict:
            """Ping a server and return pong response, or None if no response."""
            from openhcs.constants.constants import CONTROL_PORT_OFFSET
            from openhcs.runtime.zmq_base import get_zmq_transport_url, get_default_transport_mode

            control_port = port + CONTROL_PORT_OFFSET
            try:
                context = zmq.Context()
                socket = context.socket(zmq.REQ)
                socket.setsockopt(zmq.LINGER, 0)
                socket.setsockopt(zmq.RCVTIMEO, 1000)  # 1 second timeout (servers may be busy)

                # Use transport mode-aware URL (IPC or TCP)
                transport_mode = get_default_transport_mode()
                control_url = get_zmq_transport_url(control_port, transport_mode, 'localhost')
                socket.connect(control_url)

                # Send ping
                socket.send(pickle.dumps({'type': 'ping'}))

                # Wait for pong
                response = socket.recv()
                pong = pickle.loads(response)

                socket.close()
                context.term()
                logger.debug(f"Port {port} responded: {pong}")
                return pong
            except Exception as e:
                logger.debug(f"Port {port} no response: {e}")
                return None

        # Scan all ports (execution server + all streaming types)
        for port in ports_to_scan:
            pong = ping_server(port)
            if pong and pong.get('log_file_path'):
                log_path = Path(pong['log_file_path'])
                if log_path.exists():
                    log_info = classify_log_file(log_path, None, False)
                    discovered_logs.append(log_info)
                    viewer_type = pong.get('viewer', 'ZMQ server')
                    logger.debug(f"Discovered {viewer_type} log: {log_path}")

        return discovered_logs

    # Dropdown Management Methods
    def populate_log_dropdown(self, log_files: List[LogFileInfo]) -> None:
        """
        Populate QComboBox with log files with process status indicators.

        Args:
            log_files: List of LogFileInfo objects to add to dropdown
        """
        self.log_selector.clear()

        # Sort logs: TUI first, main subprocess, then workers by timestamp
        sorted_logs = sorted(log_files, key=self._log_sort_key)

        # Filter if "show alive only" is enabled
        if self.show_alive_only:
            sorted_logs = [
                log_info for log_info in sorted_logs
                if self._is_log_from_alive_process(log_info)
            ]

        for log_info in sorted_logs:
            # Add process status indicator to display name
            display_name = get_log_display_name(log_info.path, self.process_tracker)
            tooltip = get_log_tooltip(log_info.path, self.process_tracker)

            self.log_selector.addItem(display_name, log_info)
            # Set tooltip for the item
            self.log_selector.setItemData(self.log_selector.count() - 1, tooltip, Qt.ItemDataRole.ToolTipRole)

        logger.debug(f"Populated dropdown with {len(sorted_logs)} log files (filtered: {self.show_alive_only})")

    def _log_sort_key(self, log_info: LogFileInfo) -> tuple:
        """
        Generate sort key for log files.

        Args:
            log_info: LogFileInfo to generate sort key for

        Returns:
            tuple: Sort key (priority, timestamp)
        """
        # Priority: TUI=0, main=1, worker=2, unknown=3
        priority_map = {"tui": 0, "main": 1, "worker": 2, "unknown": 3}
        priority = priority_map.get(log_info.log_type, 3)

        # Use file modification time as secondary sort
        try:
            timestamp = log_info.path.stat().st_mtime
        except (OSError, AttributeError):
            timestamp = 0

        return (priority, -timestamp)  # Negative timestamp for newest first

    def clear_subprocess_logs(self) -> None:
        """Remove all non-TUI logs from dropdown and switch to TUI log."""
        import traceback
        logger.error(f"🔥 DEBUG: clear_subprocess_logs called! Stack trace:")
        for line in traceback.format_stack():
            logger.error(f"🔥 DEBUG: {line.strip()}")

        current_logs = []

        # Collect TUI logs only
        for i in range(self.log_selector.count()):
            log_info = self.log_selector.itemData(i)
            if log_info and log_info.log_type == "tui":
                current_logs.append(log_info)

        # Repopulate with TUI logs only
        self.populate_log_dropdown(current_logs)

        # Auto-select TUI log if available
        if current_logs:
            self.switch_to_log(current_logs[0].path)

        logger.info("Cleared subprocess logs, kept TUI logs")

    def add_new_log(self, log_file_info: LogFileInfo) -> None:
        """
        Add new log to dropdown maintaining sort order.

        Args:
            log_file_info: New LogFileInfo to add
        """
        # Add to master list (avoid duplicates by path)
        existing_paths = {log.path for log in self._all_discovered_logs}
        if log_file_info.path not in existing_paths:
            self._all_discovered_logs.append(log_file_info)

            # Repopulate dropdown from master list
            self.populate_log_dropdown(self._all_discovered_logs)

            logger.info(f"Added new log to dropdown: {log_file_info.display_name}")
        else:
            logger.debug(f"Log already exists, skipping: {log_file_info.display_name}")

    def on_log_selection_changed(self, index: int) -> None:
        """
        Handle dropdown selection change - switch log display.

        Args:
            index: Selected index in dropdown
        """
        if index >= 0:
            log_info = self.log_selector.itemData(index)
            if log_info:
                self.switch_to_log(log_info.path)

    def switch_to_log(self, log_path: Path) -> None:
        """Switch log display to show specified log file.

        Args:
            log_path: Path to log file to display
        """
        try:
            # Stop current tailing
            self.stop_log_tailing()

            # Stop any existing file loader
            if self.file_loader and self.file_loader.isRunning():
                self.file_loader.wait()

            # Reset streaming state
            self._pending_partial_line = ""
            self.current_file_position = 0

            # Validate file exists
            if not log_path.exists():
                self.clear_log_display()
                self.log_model.append_lines([f"Log file not found: {log_path}"])
                return

            # Store path for later use
            self.current_log_path = log_path

            # ALWAYS use async loading to prevent UI blocking
            file_size = log_path.stat().st_size
            logger.debug(f"Loading log file ({file_size} bytes) asynchronously")

            self.clear_log_display()
            self.log_model.append_lines([f"Loading log file ({file_size // 1024} KB)..."])

            # Create and start async loader
            self.file_loader = LogFileLoader(log_path)
            self.file_loader.content_loaded.connect(self._on_file_loaded)
            self.file_loader.load_failed.connect(self._on_file_load_failed)
            self.file_loader.start()

        except Exception as e:
            logger.error(f"Error switching to log {log_path}: {e}")
            raise

    def _on_file_loaded(self, content: str) -> None:
        """Handle file content loaded (either sync or async)."""
        try:
            self._pending_partial_line = ""
            self.clear_log_display()

            lines = content.splitlines()

            # Update file position immediately
            self.current_file_position = len(content.encode("utf-8"))

            # Batch insert lines to prevent UI freeze
            # Insert in chunks of 1000 lines with event loop yields
            self._batch_insert_lines(lines)

        except Exception as e:
            logger.error(f"Error displaying loaded content: {e}")

    def _batch_insert_lines(self, lines: List[str], chunk_size: int = 1000) -> None:
        """
        Insert lines in batches to prevent UI freeze.

        Yields control back to the event loop between batches so the UI
        stays responsive even when loading large log files.

        Args:
            lines: All lines to insert
            chunk_size: Number of lines to insert per batch
        """
        if not lines:
            # No lines to insert - finish up
            self._finish_batch_insert()
            return

        # Take next chunk
        chunk = lines[:chunk_size]
        remaining = lines[chunk_size:]

        # Insert this chunk
        self.log_model.append_lines(chunk)

        if remaining:
            # Schedule next batch on event loop (yields to UI)
            QTimer.singleShot(0, lambda: self._batch_insert_lines(remaining, chunk_size))
        else:
            # All done - finish up
            self._finish_batch_insert()

    def _finish_batch_insert(self) -> None:
        """Called after all batches are inserted."""
        # Start tailing if not paused
        if not self.tailing_paused and self.current_log_path:
            self.start_log_tailing(self.current_log_path)

        # Scroll to bottom if auto-scroll enabled
        if self.auto_scroll_enabled:
            self.scroll_to_bottom()

        logger.info(f"Loaded log file: {self.current_log_path}")

    def _on_file_load_failed(self, error_msg: str) -> None:
        """Handle file load failure."""
        self.clear_log_display()
        self.log_model.append_lines([f"Failed to load log file: {error_msg}"])
        logger.error(f"Failed to load log file: {error_msg}")

    # Search Functionality Methods
    def toggle_search_toolbar(self) -> None:
        """Show/hide search toolbar (Ctrl+F handler)."""
        if self.search_toolbar.isVisible():
            # Hide toolbar and clear highlights
            self.search_toolbar.setVisible(False)
            self.clear_search_highlights()
        else:
            # Show toolbar and focus search input
            self.search_toolbar.setVisible(True)
            self.search_input.setFocus()
            self.search_input.selectAll()

    def perform_search(self) -> None:
        """Search forwards in the current log using the model/view backend."""
        self._advance_search(step=1)

    def _advance_search(self, step: int) -> None:
        """Advance search cursor in the given direction.

        Args:
            step: +1 for next, -1 for previous
        """
        search_text = self.search_input.text()
        if not search_text:
            self.clear_search_highlights()
            return

        case_sensitive = self.case_sensitive_cb.isChecked()

        # Rebuild match list if query or case sensitivity changed.
        if (
            search_text != self.current_search_text
            or case_sensitive != self._search_case_sensitive
        ):
            self.current_search_text = search_text
            self._search_case_sensitive = case_sensitive
            self._search_matches = []

            lines = self.log_model.iter_lines()
            if case_sensitive:
                for row, line in enumerate(lines):
                    if search_text in line:
                        self._search_matches.append(row)
            else:
                needle = search_text.lower()
                for row, line in enumerate(lines):
                    if needle in line.lower():
                        self._search_matches.append(row)

            # Reset cursor for new search set.
            self._search_match_cursor = -1

            # Update delegate highlighting state.
            if self.log_delegate is not None:
                self.log_delegate.set_search_state(self.current_search_text, self._search_case_sensitive)
            if self.log_view is not None:
                self.log_view.viewport().update()

        if not self._search_matches:
            return

        # Step through matches with wrap-around.
        if self._search_match_cursor == -1:
            self._search_match_cursor = 0 if step >= 0 else len(self._search_matches) - 1
        else:
            self._search_match_cursor = (self._search_match_cursor + step) % len(self._search_matches)

        target_row = self._search_matches[self._search_match_cursor]
        index = self.log_model.index(target_row, 0)
        self.log_view.setCurrentIndex(index)
        self.log_view.scrollTo(index, QAbstractItemView.ScrollHint.PositionAtCenter)

    def clear_search_highlights(self) -> None:
        """Clear search state and delegate highlights."""
        self.current_search_text = ""
        self._search_case_sensitive = False
        self._search_matches = []
        self._search_match_cursor = -1

        if self.log_delegate is not None:
            self.log_delegate.set_search_state("", False)
        if self.log_view is not None:
            self.log_view.viewport().update()

    def find_next(self) -> None:
        """Find next search result."""
        self._advance_search(step=1)

    def find_previous(self) -> None:
        """Find previous search result."""
        self._advance_search(step=-1)

    # Control Button Methods
    def toggle_auto_scroll(self, enabled: bool) -> None:
        """Toggle auto-scroll to bottom."""
        self.auto_scroll_enabled = enabled
        logger.debug(f"Auto-scroll {'enabled' if enabled else 'disabled'}")

    def toggle_pause_tailing(self, paused: bool) -> None:
        """Toggle pause/resume log tailing."""
        self.tailing_paused = paused
        if paused:
            self.stop_log_tailing()
        elif not paused and self.current_log_path:
            self.start_log_tailing(self.current_log_path)
        logger.debug(f"Log tailing {'paused' if paused else 'resumed'}")

    def clear_log_display(self) -> None:
        """Clear current log display content."""
        self._pending_partial_line = ""
        self.log_model.clear()
        logger.debug("Log display cleared")

    def reset_memory(self) -> None:
        """
        Reset memory usage by clearing the in-memory log model and reloading current log.

        This completely clears the text buffer and reloads the log file from disk,
        freeing memory accumulated from long-running log tailing.
        """
        if not self.current_log_path:
            logger.warning("No log file currently loaded - cannot reset memory")
            return

        logger.info(f"Resetting memory for log: {self.current_log_path}")

        # Stop tailing
        was_paused = self.tailing_paused
        self.stop_log_tailing()

        # Clear the model completely (frees memory)
        self.clear_log_display()

        # Clear the delegate's document cache (frees cached QTextDocuments)
        if self.log_delegate is not None:
            self.log_delegate.clear_cache()

        # Reset file position to reload from beginning
        self.current_file_position = 0

        # Reload the log file
        self.switch_to_log(self.current_log_path)

        # Restore pause state
        if was_paused:
            self.tailing_paused = True
            self.pause_btn.setChecked(True)

        logger.info("Memory reset complete - log reloaded from disk")

    def scroll_to_bottom(self) -> None:
        """Scroll log view to bottom."""
        self.log_view.scrollToBottom()



    # Real-time Tailing Methods
    def start_log_tailing(self, log_path: Path) -> None:
        """
        Start tailing log file with async background thread (never blocks UI).

        Args:
            log_path: Path to log file to tail
        """
        # Stop any existing tailer
        self.stop_log_tailing()

        # Create and start async tailer thread
        self.log_tailer = LogTailer(log_path, self.current_file_position)
        self.log_tailer.new_content.connect(self._on_new_content)
        self.log_tailer.log_rotated.connect(self._on_log_rotated)
        self.log_tailer.error_occurred.connect(self._on_tail_error)
        self.log_tailer.start()

        logger.debug(f"Started async tailing for log file: {log_path}")

    def stop_log_tailing(self) -> None:
        """Stop current log tailing."""
        if self.log_tailer:
            self.log_tailer.stop()
            self.log_tailer.wait(1000)  # Wait up to 1 second for thread to finish
            self.log_tailer = None
        logger.debug("Stopped log tailing")

    def _on_new_content(self, new_content: str, new_file_position: int) -> None:
        """Handle new content from async tailer (runs on UI thread via signal)."""
        # Defer updates if window is minimized or hidden to reduce UI load
        if self.isMinimized() or not self.isVisible():
            # Just update file position, skip rendering
            self.current_file_position = new_file_position
            return

        # Check if user has scrolled up (disable auto-scroll)
        scrollbar = self.log_view.verticalScrollBar()
        was_at_bottom = scrollbar.value() >= scrollbar.maximum() - 10
        self._last_scroll_state = was_at_bottom

        # Merge with any pending partial line and split into full lines.
        chunk = f"{self._pending_partial_line}{new_content}"
        if not chunk:
            return

        lines = chunk.splitlines()
        if not chunk.endswith(("\n", "\r")):
            # Last line is incomplete; keep it for the next chunk.
            self._pending_partial_line = lines.pop() if lines else chunk
        else:
            self._pending_partial_line = ""

        if lines:
            # Add to pending buffer
            self._pending_lines.extend(lines)

            # Start throttle timer if not already running
            if not self._update_timer.isActive():
                self._update_timer.start(self._update_throttle_ms)

        # Update file position
        self.current_file_position = new_file_position

    def _flush_pending_lines(self) -> None:
        """Flush pending lines to the UI (called by throttle timer)."""
        if not self._pending_lines:
            return

        lines = self._pending_lines
        self._pending_lines = []

        # For tailing, batch if we have a large burst (>500 lines)
        if len(lines) > 500:
            self._batch_insert_lines_for_tailing(lines, self._last_scroll_state)
        else:
            # Small batch - insert directly
            self.log_model.append_lines(lines)

            # Auto-scroll if enabled and user was at bottom
            if self.auto_scroll_enabled and self._last_scroll_state:
                self.scroll_to_bottom()

    def _batch_insert_lines_for_tailing(self, lines: List[str], was_at_bottom: bool, chunk_size: int = 500) -> None:
        """
        Batch insert lines during tailing to prevent UI freeze on large bursts.

        Similar to _batch_insert_lines but preserves scroll position for tailing.

        Args:
            lines: Lines to insert
            was_at_bottom: Whether user was scrolled to bottom before insert
            chunk_size: Number of lines per batch
        """
        if not lines:
            return

        # Take next chunk
        chunk = lines[:chunk_size]
        remaining = lines[chunk_size:]

        # Insert this chunk
        self.log_model.append_lines(chunk)

        # Auto-scroll if enabled and user was at bottom
        if self.auto_scroll_enabled and was_at_bottom:
            self.scroll_to_bottom()

        if remaining:
            # Schedule next batch on event loop (yields to UI)
            QTimer.singleShot(0, lambda: self._batch_insert_lines_for_tailing(remaining, was_at_bottom, chunk_size))


    def _on_log_rotated(self) -> None:
        """Handle log rotation detected by async tailer."""
        logger.info(f"Log rotation detected for {self.current_log_path}")
        self.current_file_position = 0
        self._pending_partial_line = ""
        self.log_model.append_lines(["", "--- Log rotated ---", ""])

    def _on_tail_error(self, error_msg: str) -> None:
        """Handle errors from async tailer."""
        logger.warning(f"Tailing error: {error_msg}")

        # Check if file was deleted
        if self.current_log_path and not self.current_log_path.exists():
            logger.info(f"Log file deleted: {self.current_log_path}")
            self.log_model.append_lines([
                "",
                f"--- Log file deleted: {self.current_log_path} ---",
                "",
            ])
            # Try to reconnect after a delay
            QTimer.singleShot(1000, self._attempt_reconnection)

    def read_log_incremental(self) -> None:
        """Deprecated - kept for compatibility. Tailing now handled by LogTailer thread."""
        pass

    def _attempt_reconnection(self) -> None:
        """Attempt to reconnect to log file after deletion."""
        if self.current_log_path and self.current_log_path.exists():
            logger.info(f"Log file recreated, reconnecting: {self.current_log_path}")
            self.current_file_position = 0
            self._pending_partial_line = ""
            self.log_model.append_lines([
                "",
                f"--- Reconnected to: {self.current_log_path} ---",
                "",
            ])
            # File will be read on next timer tick

    # External Integration Methods
    def start_monitoring(self, base_log_path: Optional[str] = None) -> None:
        """Start monitoring for new logs."""
        if self.file_detector:
            self.file_detector.stop_watching()

        # Get log directory
        log_directory = Path(base_log_path).parent if base_log_path else Path.home() / ".local" / "share" / "openhcs" / "logs"

        # Start file watching
        self.file_detector = LogFileDetector(base_log_path)
        self.file_detector.new_log_detected.connect(self.add_new_log)
        self.file_detector.start_watching(log_directory)

    def stop_monitoring(self) -> None:
        """Stop monitoring for new logs."""
        if self.file_detector:
            self.file_detector.stop_watching()
            self.file_detector = None
        logger.info("Stopped monitoring for new logs")

    def start_process_tracking(self) -> None:
        """Start periodic process status updates."""
        # Initial update
        self.process_tracker.update()

        # Setup timer for periodic updates (every 2 seconds)
        self.process_update_timer = QTimer()
        self.process_update_timer.timeout.connect(self.update_process_status)
        self.process_update_timer.start(2000)  # 2 second interval

        logger.debug("Started process tracking")

    def update_process_status(self) -> None:
        """Update process status and refresh dropdown if needed."""
        # Update process tracker
        self.process_tracker.update()

        # Refresh dropdown to update status indicators
        # Only if we have logs loaded
        if self.log_selector.count() > 0:
            # Remember current selection
            current_index = self.log_selector.currentIndex()
            current_log_info = self.log_selector.itemData(current_index) if current_index >= 0 else None

            # Temporarily disconnect signal to avoid triggering reload
            self.log_selector.currentIndexChanged.disconnect(self.on_log_selection_changed)

            try:
                # Repopulate from master list with updated status indicators
                self.populate_log_dropdown(self._all_discovered_logs)

                # Restore selection if possible
                if current_log_info:
                    # Find the same log in the new dropdown
                    for i in range(self.log_selector.count()):
                        log_info = self.log_selector.itemData(i)
                        if log_info and log_info.path == current_log_info.path:
                            self.log_selector.setCurrentIndex(i)
                            break
            finally:
                # Reconnect signal
                self.log_selector.currentIndexChanged.connect(self.on_log_selection_changed)

    def _get_process_start_time(self) -> float:
        """
        Get the start time of the current process.

        Returns:
            float: Process start time as Unix timestamp
        """
        try:
            import psutil
            import os
            process = psutil.Process(os.getpid())
            return process.create_time()
        except Exception as e:
            logger.warning(f"Failed to get process start time: {e}")
            # Fallback to current time
            import time
            return time.time()

    def _is_log_from_current_session(self, log_info: LogFileInfo) -> bool:
        """
        Check if a log file was created during the current session.

        Args:
            log_info: LogFileInfo to check

        Returns:
            bool: True if log was created after session start time
        """
        try:
            # Get file modification time (when log was created/last written)
            mtime = log_info.path.stat().st_mtime
            # Allow a small buffer (5 seconds) to account for timing differences
            return mtime >= (self._session_start_time - 5.0)
        except (OSError, FileNotFoundError):
            # If we can't stat the file, exclude it
            return False

    def _is_log_from_alive_process(self, log_info: LogFileInfo) -> bool:
        """
        Check if a log file is from a currently running process.

        Args:
            log_info: LogFileInfo to check

        Returns:
            bool: True if process is alive or unknown, False if terminated
        """
        pid = extract_pid_from_log_filename(log_info.path)
        if pid is None:
            # No PID found - assume it's a main log (always show)
            return True
        return self.process_tracker.is_alive(pid)

    def on_filter_changed(self, state: int) -> None:
        """
        Handle filter checkbox state change.

        Args:
            state: Qt.CheckState value
        """
        self.show_alive_only = (state == Qt.CheckState.Checked.value)

        # Refresh dropdown with filter applied
        # Always use master list as source, not the current dropdown
        # This ensures all logs are available when filter is toggled off
        if self._all_discovered_logs:
            self.populate_log_dropdown(self._all_discovered_logs)

        logger.debug(f"Filter changed: show_alive_only={self.show_alive_only}")

    def cleanup(self) -> None:
        """Cleanup all resources and background processes."""
        try:
            # Stop async log tailer thread
            if hasattr(self, 'log_tailer') and self.log_tailer:
                self.stop_log_tailing()

            # Stop tailing timer (deprecated, kept for compatibility)
            if hasattr(self, 'tail_timer') and self.tail_timer and self.tail_timer.isActive():
                self.tail_timer.stop()
                self.tail_timer.deleteLater()
                self.tail_timer = None

            # Stop process tracking timer
            if hasattr(self, 'process_update_timer') and self.process_update_timer and self.process_update_timer.isActive():
                self.process_update_timer.stop()
                self.process_update_timer.deleteLater()
                self.process_update_timer = None

            # Stop file monitoring
            self.stop_monitoring()

            # Clean up file detector
            if hasattr(self, 'file_detector') and self.file_detector:
                self.file_detector.stop_watching()
                self.file_detector = None

        except Exception as e:
            logger.warning(f"Error during log viewer cleanup: {e}")

    def closeEvent(self, event) -> None:
        """Handle window close event."""
        # Stop async tailer
        if hasattr(self, 'log_tailer') and self.log_tailer:
            self.stop_log_tailing()

        if self.file_detector:
            self.file_detector.stop_watching()
        if self.tail_timer:
            self.tail_timer.stop()
        if hasattr(self, 'process_update_timer') and self.process_update_timer:
            self.process_update_timer.stop()
        self.window_closed.emit()
        super().closeEvent(event)
