"""
Simple Code Editor Service for PyQt GUI.

Provides modular text editing with QScintilla (default) or external program launch.
No threading complications - keeps it simple and direct.
"""

import logging
import tempfile
import os
import subprocess
from pathlib import Path
from typing import Optional, Callable

from PyQt6.QtWidgets import (QDialog, QVBoxLayout, QTextEdit, QPushButton, QHBoxLayout,
                             QMessageBox, QMenuBar, QMenu, QFileDialog)
from PyQt6.QtCore import Qt
from PyQt6.QtGui import QFont, QAction, QKeySequence

logger = logging.getLogger(__name__)

# Try to import QScintilla, fall back to QTextEdit if not available
try:
    from PyQt6.Qsci import QsciScintilla, QsciLexerPython
    QSCINTILLA_AVAILABLE = True
    logger.info("QScintilla successfully imported")
except ImportError as e:
    logger.warning(f"QScintilla not available: {e}")
    logger.info("Install with: pip install PyQt6-QScintilla")
    QSCINTILLA_AVAILABLE = False


class SimpleCodeEditorService:
    """
    Simple, modular code editor service.

    Uses QScintilla for professional Python editing (default) or external programs.
    Falls back to QTextEdit if QScintilla is not available.
    No threading - keeps it simple and reliable.
    """
    
    def __init__(self, parent_widget):
        """
        Initialize the code editor service.

        Args:
            parent_widget: Parent widget for dialogs
        """
        self.parent = parent_widget

    def edit_code(self, initial_content: str, title: str = "Edit Code",
                  callback: Optional[Callable[[str], None]] = None,
                  use_external: bool = False,
                  code_type: str = None,
                  code_data: dict = None) -> None:
        """
        Edit code using either Qt native editor or external program.

        Args:
            initial_content: Initial code content
            title: Editor window title
            callback: Callback function called with edited content
            use_external: If True, use external editor; if False, use Qt native
            code_type: Type of code being edited ('orchestrator', 'pipeline', 'function', None)
            code_data: Data needed to regenerate code (for clean mode toggle)
        """
        if use_external:
            self._edit_with_external_program(initial_content, callback)
        else:
            self._edit_with_qt_native(initial_content, title, callback, code_type, code_data)
    
    def _edit_with_qt_native(self, initial_content: str, title: str,
                           callback: Optional[Callable[[str], None]],
                           code_type: str = None,
                           code_data: dict = None) -> None:
        """Edit code using Qt native text editor dialog (QScintilla preferred)."""
        try:
            if QSCINTILLA_AVAILABLE:
                logger.debug("Using QScintilla editor for code editing")
                dialog = QScintillaCodeEditorDialog(self.parent, initial_content, title,
                                                   code_type=code_type, code_data=code_data)
            else:
                logger.debug("QScintilla not available, using QTextEdit fallback")
                dialog = CodeEditorDialog(self.parent, initial_content, title)

            if dialog.exec() == QDialog.DialogCode.Accepted:
                edited_content = dialog.get_content()
                if callback:
                    callback(edited_content)

        except Exception as e:
            logger.error(f"Qt native editor failed: {e}")
            self._show_error(f"Editor failed: {str(e)}")
    
    def _edit_with_external_program(self, initial_content: str,
                                  callback: Optional[Callable[[str], None]]) -> None:
        """Edit code using external program (vim, nano, vscode, etc.)."""
        try:
            # Create temporary file
            with tempfile.NamedTemporaryFile(mode='w', suffix='.py', delete=False) as f:
                f.write(initial_content)
                temp_path = Path(f.name)
            
            # Get editor from environment or use default
            editor = os.environ.get('EDITOR', 'nano')
            
            # Launch editor and wait for completion
            result = subprocess.run([editor, str(temp_path)], 
                                  capture_output=False, 
                                  text=True)
            
            if result.returncode == 0:
                # Read edited content
                with open(temp_path, 'r') as f:
                    edited_content = f.read()
                
                if callback:
                    callback(edited_content)
            else:
                self._show_error(f"Editor exited with code {result.returncode}")
                
        except FileNotFoundError:
            self._show_error(f"Editor '{editor}' not found. Set EDITOR environment variable or install nano/vim.")
        except Exception as e:
            logger.error(f"External editor failed: {e}")
            self._show_error(f"External editor failed: {str(e)}")
        finally:
            # Clean up temporary file
            try:
                if temp_path.exists():
                    temp_path.unlink()
            except:
                pass
    
    def _show_error(self, message: str) -> None:
        """Show error message to user."""
        QMessageBox.critical(self.parent, "Editor Error", message)


class QScintillaCodeEditorDialog(QDialog):
    """
    Professional code editor dialog using QScintilla.

    Provides Python syntax highlighting, code folding, line numbers, and more.
    Integrates with PyQt6ColorScheme for consistent theming.
    Supports clean mode toggle for orchestrator/pipeline/function code.
    """

    def __init__(self, parent, initial_content: str, title: str,
                 code_type: str = None, code_data: dict = None):
        """
        Initialize code editor dialog.

        Args:
            parent: Parent widget
            initial_content: Initial code content
            title: Window title
            code_type: Type of code being edited ('orchestrator', 'pipeline', 'function', None)
            code_data: Data needed to regenerate code (for clean mode toggle)
        """
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setModal(True)
        self.resize(900, 700)

        # Store code generation context for clean mode toggle
        self.code_type = code_type
        self.code_data = code_data or {}
        self.clean_mode = self.code_data.get('clean_mode', True)  # Default to clean mode

        # Get color scheme from parent
        from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
        self.color_scheme = PyQt6ColorScheme()

        # Setup UI
        self._setup_ui(initial_content)

        # Apply theming
        self._apply_theme()

        # Focus on editor
        self.editor.setFocus()



    def _setup_ui(self, initial_content: str):
        """Setup the UI components."""
        # Main layout
        main_layout = QVBoxLayout(self)

        # Menu bar
        self._setup_menu_bar()
        main_layout.addWidget(self.menu_bar)

        # QScintilla editor
        self.editor = QsciScintilla()
        self.editor.setText(initial_content)

        # Set Python lexer for syntax highlighting
        self.lexer = QsciLexerPython()
        self.editor.setLexer(self.lexer)

        # Configure editor features
        self._configure_editor()

        main_layout.addWidget(self.editor)

        # Buttons
        button_layout = QHBoxLayout()

        self.save_btn = QPushButton("Save")
        self.save_btn.clicked.connect(self.accept)
        button_layout.addWidget(self.save_btn)

        self.cancel_btn = QPushButton("Cancel")
        self.cancel_btn.clicked.connect(self.reject)
        button_layout.addWidget(self.cancel_btn)

        button_layout.addStretch()
        main_layout.addLayout(button_layout)

    def _setup_menu_bar(self):
        """Setup menu bar with File, Edit, View menus."""
        from PyQt6.QtWidgets import QMenuBar

        self.menu_bar = QMenuBar(self)

        # File menu
        file_menu = self.menu_bar.addMenu("&File")

        # New action
        new_action = QAction("&New", self)
        new_action.setShortcut(QKeySequence.StandardKey.New)
        new_action.triggered.connect(self._new_file)
        file_menu.addAction(new_action)

        # Open action
        open_action = QAction("&Open...", self)
        open_action.setShortcut(QKeySequence.StandardKey.Open)
        open_action.triggered.connect(self._open_file)
        file_menu.addAction(open_action)

        file_menu.addSeparator()

        # Save action
        save_action = QAction("&Save", self)
        save_action.setShortcut(QKeySequence.StandardKey.Save)
        save_action.triggered.connect(self.accept)
        file_menu.addAction(save_action)

        # Save As action
        save_as_action = QAction("Save &As...", self)
        save_as_action.setShortcut(QKeySequence.StandardKey.SaveAs)
        save_as_action.triggered.connect(self._save_as)
        file_menu.addAction(save_as_action)

        file_menu.addSeparator()

        # Close action
        close_action = QAction("&Close", self)
        close_action.setShortcut(QKeySequence.StandardKey.Close)
        close_action.triggered.connect(self.reject)
        file_menu.addAction(close_action)

        # Edit menu
        edit_menu = self.menu_bar.addMenu("&Edit")

        # Undo action
        undo_action = QAction("&Undo", self)
        undo_action.setShortcut(QKeySequence.StandardKey.Undo)
        undo_action.triggered.connect(lambda: self.editor.undo())
        edit_menu.addAction(undo_action)

        # Redo action
        redo_action = QAction("&Redo", self)
        redo_action.setShortcut(QKeySequence.StandardKey.Redo)
        redo_action.triggered.connect(lambda: self.editor.redo())
        edit_menu.addAction(redo_action)

        edit_menu.addSeparator()

        # Cut, Copy, Paste
        cut_action = QAction("Cu&t", self)
        cut_action.setShortcut(QKeySequence.StandardKey.Cut)
        cut_action.triggered.connect(lambda: self.editor.cut())
        edit_menu.addAction(cut_action)

        copy_action = QAction("&Copy", self)
        copy_action.setShortcut(QKeySequence.StandardKey.Copy)
        copy_action.triggered.connect(lambda: self.editor.copy())
        edit_menu.addAction(copy_action)

        paste_action = QAction("&Paste", self)
        paste_action.setShortcut(QKeySequence.StandardKey.Paste)
        paste_action.triggered.connect(lambda: self.editor.paste())
        edit_menu.addAction(paste_action)

        edit_menu.addSeparator()

        # Select All
        select_all_action = QAction("Select &All", self)
        select_all_action.setShortcut(QKeySequence.StandardKey.SelectAll)
        select_all_action.triggered.connect(lambda: self.editor.selectAll())
        edit_menu.addAction(select_all_action)

        # View menu
        view_menu = self.menu_bar.addMenu("&View")

        # Toggle line numbers
        toggle_line_numbers = QAction("Toggle &Line Numbers", self)
        toggle_line_numbers.setCheckable(True)
        toggle_line_numbers.setChecked(True)
        toggle_line_numbers.triggered.connect(self._toggle_line_numbers)
        view_menu.addAction(toggle_line_numbers)

        # Toggle code folding
        toggle_folding = QAction("Toggle Code &Folding", self)
        toggle_folding.setCheckable(True)
        toggle_folding.setChecked(True)
        toggle_folding.triggered.connect(self._toggle_code_folding)
        view_menu.addAction(toggle_folding)

        # Add separator before clean mode toggle
        view_menu.addSeparator()

        # Toggle clean mode - always available
        toggle_clean_mode = QAction("Toggle &Clean Mode", self)
        toggle_clean_mode.setCheckable(True)
        toggle_clean_mode.setChecked(self.clean_mode)
        toggle_clean_mode.triggered.connect(self._toggle_clean_mode)
        view_menu.addAction(toggle_clean_mode)

    def _configure_editor(self):
        """Configure QScintilla editor with professional features."""
        # Line numbers
        self.editor.setMarginType(0, QsciScintilla.MarginType.NumberMargin)
        self.editor.setMarginWidth(0, "0000")
        self.editor.setMarginLineNumbers(0, True)
        self.editor.setMarginsBackgroundColor(Qt.GlobalColor.lightGray)

        # Current line highlighting
        self.editor.setCaretLineVisible(True)
        self.editor.setCaretLineBackgroundColor(Qt.GlobalColor.lightGray)

        # Set font
        font = QFont("Consolas", 10)
        if not font.exactMatch():
            font = QFont("Courier New", 10)
        self.editor.setFont(font)

        # Indentation
        self.editor.setIndentationsUseTabs(False)
        self.editor.setIndentationWidth(4)
        self.editor.setTabWidth(4)
        self.editor.setAutoIndent(True)

        # Code folding
        self.editor.setFolding(QsciScintilla.FoldStyle.BoxedTreeFoldStyle)

        # Brace matching
        self.editor.setBraceMatching(QsciScintilla.BraceMatch.SloppyBraceMatch)

        # Selection
        self.editor.setSelectionBackgroundColor(Qt.GlobalColor.blue)

        # Enable UTF-8
        self.editor.setUtf8(True)

        # Configure autocomplete
        self._configure_autocomplete()

    def _configure_autocomplete(self):
        """Configure autocomplete for Python code."""
        logger.info("🔧 Configuring Jedi-powered autocomplete...")

        # Use custom autocomplete source (we'll populate it with Jedi)
        self.editor.setAutoCompletionSource(QsciScintilla.AutoCompletionSource.AcsAPIs)
        logger.info("  ✓ Autocomplete source set to AcsAPIs")

        # Show autocomplete after typing 2 characters
        self.editor.setAutoCompletionThreshold(2)
        logger.info("  ✓ Autocomplete threshold: 2 characters")

        # Case-insensitive matching
        self.editor.setAutoCompletionCaseSensitivity(False)

        # Replace word when selecting from autocomplete
        self.editor.setAutoCompletionReplaceWord(True)

        # Show single item automatically
        self.editor.setAutoCompletionUseSingle(QsciScintilla.AutoCompletionUseSingle.AcusNever)

        # Note: setAutoCompletionMaxVisibleItems() doesn't exist in QScintilla
        # The list size is automatically managed

        # Setup Jedi-based API
        self._setup_jedi_api()

        # Install event filter to catch key presses for autocomplete triggering
        self.editor.installEventFilter(self)
        logger.info("  ✓ Event filter installed for '.' trigger")

    def eventFilter(self, obj, event):
        """Filter events to trigger Jedi autocomplete on '.' """
        from PyQt6.QtCore import QEvent
        from PyQt6.QtGui import QKeyEvent

        if obj == self.editor and event.type() == QEvent.Type.KeyPress:
            key_event = event
            # Trigger autocomplete when '.' is typed
            if key_event.text() == '.':
                logger.info("🔍 Detected '.' keypress - triggering Jedi autocomplete")
                # Let the '.' be inserted first
                from PyQt6.QtCore import QTimer
                QTimer.singleShot(10, self._show_jedi_completions)

        return super().eventFilter(obj, event)

    def _setup_jedi_api(self):
        """Setup initial API with basic Python keywords for fallback."""
        try:
            from PyQt6.Qsci import QsciAPIs

            # Create API object for Python lexer
            self.api = QsciAPIs(self.lexer)
            logger.info("  ✓ Created QsciAPIs object")

            # Add basic Python keywords as fallback
            python_keywords = [
                'False', 'None', 'True', 'and', 'as', 'assert', 'async', 'await',
                'break', 'class', 'continue', 'def', 'del', 'elif', 'else', 'except',
                'finally', 'for', 'from', 'global', 'if', 'import', 'in', 'is',
                'lambda', 'nonlocal', 'not', 'or', 'pass', 'raise', 'return',
                'try', 'while', 'with', 'yield', 'print', 'len', 'range', 'str',
                'int', 'float', 'list', 'dict', 'tuple', 'set'
            ]

            for keyword in python_keywords:
                self.api.add(keyword)

            # Prepare the API
            self.api.prepare()

            logger.info(f"  ✓ Added {len(python_keywords)} Python keywords to API")

        except Exception as e:
            logger.error(f"❌ Failed to setup Jedi API autocomplete: {e}")

    def _show_jedi_completions(self):
        """Show Jedi-powered autocomplete suggestions."""
        logger.info("🧠 _show_jedi_completions called")
        try:
            import jedi

            # Get current code and cursor position
            code = self.editor.text()
            line, col = self.editor.getCursorPosition()

            # Get the current line text to see what we're completing
            current_line = self.editor.text(line)
            logger.info(f"  📍 Cursor position: line={line}, col={col}")
            logger.info(f"  📝 Current line: '{current_line}'")
            logger.info(f"  📝 Code length: {len(code)} chars")

            # Check if we're typing an import statement or module access
            # If the line starts with 'import' or 'from', add it if not already there
            current_line_stripped = current_line.strip()
            if current_line_stripped and not current_line_stripped.startswith(('import ', 'from ')):
                # User is typing module.attribute without import - add implicit import for Jedi
                # Extract the module path before the cursor
                before_cursor = current_line[:col].strip()
                if '.' in before_cursor:
                    # Get the base module (everything before last dot)
                    parts = before_cursor.rsplit('.', 1)
                    if parts:
                        module_path = parts[0]
                        # Add import statement for Jedi
                        code = f"import {module_path}\n" + code
                        # Adjust line number since we added a line
                        jedi_line = line + 2  # +1 for 1-based, +1 for added import
                        logger.info(f"  💡 Added implicit import for Jedi: 'import {module_path}'")
                    else:
                        jedi_line = line + 1
                else:
                    jedi_line = line + 1
            else:
                jedi_line = line + 1

            # jedi_line already set above based on whether we added import
            jedi_col = col

            # Create Jedi script with current code
            # Use project parameter to tell Jedi where to find openhcs modules
            import os

            # Get project root (where openhcs package is)
            project_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(__file__))))

            # Create Jedi project
            project = jedi.Project(path=project_root)

            script = jedi.Script(code, path='<editor>', project=project)
            logger.info(f"  ✓ Created Jedi script with project root: {project_root}")

            # Get completions at cursor position
            completions = script.complete(jedi_line, jedi_col)
            logger.info(f"  🔍 Jedi returned {len(completions)} completions")

            # If no completions, try to get more info about what Jedi sees
            if len(completions) == 0:
                logger.info(f"  ⚠️  No completions - Jedi may not be able to resolve the module")
                logger.info(f"  💡 Project root: {project_root}")

            if completions:
                # Log first few completions for debugging
                sample = [c.name for c in completions[:5]]
                logger.info(f"  📋 Sample completions: {sample}")

                # Check if autocomplete is already active
                if self.editor.isListActive():
                    logger.info(f"  ⚠️  Autocomplete list already active, canceling first")
                    self.editor.cancelList()

                # Build completion list
                # Format for each item: "name?type" where ?type is optional
                completion_items = []
                for c in completions:
                    if c.type:
                        completion_items.append(f"{c.name}?{c.type}")
                    else:
                        completion_items.append(c.name)

                logger.info(f"  📝 Built {len(completion_items)} completion items")

                # Use showUserList instead of autoCompleteFromAll to avoid QScintilla's filtering
                # showUserList(id, list) - id=1 for user completions, list is an iterable of strings
                self.editor.showUserList(1, completion_items)
                logger.info(f"  ✅ Called showUserList() with {len(completions)} completions")

                # Check if it's showing
                if self.editor.isListActive():
                    logger.info(f"  ✅ Autocomplete list is now active!")
                else:
                    logger.info(f"  ❌ Autocomplete list is NOT active")

            else:
                logger.info("  ⚠️  No Jedi completions - trying standard autocomplete")
                # No Jedi completions, try standard autocomplete
                self.editor.autoCompleteFromAll()

        except Exception as e:
            logger.error(f"❌ Jedi autocomplete failed: {e}", exc_info=True)
            # Fall back to standard autocomplete
            try:
                self.editor.autoCompleteFromAll()
            except:
                pass

    def _apply_theme(self):
        """Apply PyQt6ColorScheme theming to QScintilla editor."""
        cs = self.color_scheme

        # Apply dialog styling
        self.setStyleSheet(f"""
            QDialog {{
                background-color: {cs.to_hex(cs.window_bg)};
                color: {cs.to_hex(cs.text_primary)};
            }}
            QPushButton {{
                background-color: {cs.to_hex(cs.button_normal_bg)};
                color: {cs.to_hex(cs.button_text)};
                border: 1px solid {cs.to_hex(cs.border_light)};
                border-radius: 3px;
                padding: 5px;
                min-width: 80px;
            }}
            QPushButton:hover {{
                background-color: {cs.to_hex(cs.button_hover_bg)};
            }}
            QPushButton:pressed {{
                background-color: {cs.to_hex(cs.button_pressed_bg)};
            }}
            QMenuBar {{
                background-color: {cs.to_hex(cs.panel_bg)};
                color: {cs.to_hex(cs.text_primary)};
                border-bottom: 1px solid {cs.to_hex(cs.border_color)};
            }}
            QMenuBar::item {{
                background-color: transparent;
                padding: 4px 8px;
            }}
            QMenuBar::item:selected {{
                background-color: {cs.to_hex(cs.button_hover_bg)};
            }}
            QMenu {{
                background-color: {cs.to_hex(cs.panel_bg)};
                color: {cs.to_hex(cs.text_primary)};
                border: 1px solid {cs.to_hex(cs.border_color)};
            }}
            QMenu::item {{
                padding: 4px 20px;
            }}
            QMenu::item:selected {{
                background-color: {cs.to_hex(cs.button_hover_bg)};
            }}
        """)

        # Apply QScintilla-specific theming
        self._apply_qscintilla_theme()

    def _apply_qscintilla_theme(self):
        """Apply color scheme to QScintilla editor and lexer."""
        cs = self.color_scheme

        # Set editor background and text colors
        self.editor.setColor(cs.to_qcolor(cs.text_primary))
        self.editor.setPaper(cs.to_qcolor(cs.panel_bg))

        # Set margin colors
        self.editor.setMarginsBackgroundColor(cs.to_qcolor(cs.frame_bg))
        self.editor.setMarginsForegroundColor(cs.to_qcolor(cs.text_secondary))

        # Set caret line color
        self.editor.setCaretLineBackgroundColor(cs.to_qcolor(cs.selection_bg))

        # Set selection colors
        self.editor.setSelectionBackgroundColor(cs.to_qcolor(cs.selection_bg))
        self.editor.setSelectionForegroundColor(cs.to_qcolor(cs.selection_text))

        # Configure Python lexer colors
        if self.lexer:
            # Keywords (def, class, if, etc.)
            self.lexer.setColor(cs.to_qcolor(cs.python_keyword_color), QsciLexerPython.Keyword)

            # Strings
            self.lexer.setColor(cs.to_qcolor(cs.python_string_color), QsciLexerPython.SingleQuotedString)
            self.lexer.setColor(cs.to_qcolor(cs.python_string_color), QsciLexerPython.DoubleQuotedString)
            self.lexer.setColor(cs.to_qcolor(cs.python_string_color), QsciLexerPython.TripleSingleQuotedString)
            self.lexer.setColor(cs.to_qcolor(cs.python_string_color), QsciLexerPython.TripleDoubleQuotedString)

            # F-strings
            self.lexer.setColor(cs.to_qcolor(cs.python_string_color), QsciLexerPython.SingleQuotedFString)
            self.lexer.setColor(cs.to_qcolor(cs.python_string_color), QsciLexerPython.DoubleQuotedFString)
            self.lexer.setColor(cs.to_qcolor(cs.python_string_color), QsciLexerPython.TripleSingleQuotedFString)
            self.lexer.setColor(cs.to_qcolor(cs.python_string_color), QsciLexerPython.TripleDoubleQuotedFString)

            # Comments
            self.lexer.setColor(cs.to_qcolor(cs.python_comment_color), QsciLexerPython.Comment)
            self.lexer.setColor(cs.to_qcolor(cs.python_comment_color), QsciLexerPython.CommentBlock)

            # Numbers
            self.lexer.setColor(cs.to_qcolor(cs.python_number_color), QsciLexerPython.Number)

            # Functions and classes
            self.lexer.setColor(cs.to_qcolor(cs.python_function_color), QsciLexerPython.FunctionMethodName)
            self.lexer.setColor(cs.to_qcolor(cs.python_class_color), QsciLexerPython.ClassName)

            # Operators
            self.lexer.setColor(cs.to_qcolor(cs.python_operator_color), QsciLexerPython.Operator)

            # Identifiers
            self.lexer.setColor(cs.to_qcolor(cs.python_name_color), QsciLexerPython.Identifier)
            self.lexer.setColor(cs.to_qcolor(cs.python_name_color), QsciLexerPython.HighlightedIdentifier)

            # Decorators
            self.lexer.setColor(cs.to_qcolor(cs.python_function_color), QsciLexerPython.Decorator)

            # Set default background for lexer
            self.lexer.setPaper(cs.to_qcolor(cs.panel_bg))

    # Menu action handlers
    def _new_file(self):
        """Clear editor content."""
        self.editor.clear()

    def _open_file(self):
        """Open file dialog and load content."""
        from openhcs.core.path_cache import PathCacheKey, get_cached_dialog_path, cache_dialog_path

        # Get cached initial directory
        initial_dir = str(get_cached_dialog_path(PathCacheKey.CODE_EDITOR, fallback=Path.home()))

        file_path, _ = QFileDialog.getOpenFileName(
            self, "Open Python File", initial_dir, "Python Files (*.py);;All Files (*)"
        )
        if file_path:
            try:
                selected_path = Path(file_path)
                # Cache the parent directory for future dialogs
                cache_dialog_path(PathCacheKey.CODE_EDITOR, selected_path.parent)

                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                self.editor.setText(content)
            except Exception as e:
                QMessageBox.critical(self, "Error", f"Failed to open file: {str(e)}")

    def _save_as(self):
        """Save content to file."""
        from openhcs.core.path_cache import PathCacheKey, get_cached_dialog_path, cache_dialog_path

        # Get cached initial directory
        initial_dir = str(get_cached_dialog_path(PathCacheKey.CODE_EDITOR, fallback=Path.home()))

        file_path, _ = QFileDialog.getSaveFileName(
            self, "Save Python File", initial_dir, "Python Files (*.py);;All Files (*)"
        )
        if file_path:
            try:
                selected_path = Path(file_path)

                # Ensure file always ends with .py extension
                if not selected_path.suffix.lower() == '.py':
                    selected_path = selected_path.with_suffix('.py')
                    file_path = str(selected_path)

                # Cache the parent directory for future dialogs
                cache_dialog_path(PathCacheKey.CODE_EDITOR, selected_path.parent)

                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(self.editor.text())
                QMessageBox.information(self, "Success", f"File saved to {file_path}")
            except Exception as e:
                QMessageBox.critical(self, "Error", f"Failed to save file: {str(e)}")

    def _toggle_line_numbers(self, checked):
        """Toggle line number display."""
        if checked:
            self.editor.setMarginType(0, QsciScintilla.MarginType.NumberMargin)
            self.editor.setMarginWidth(0, "0000")
            self.editor.setMarginLineNumbers(0, True)
        else:
            self.editor.setMarginWidth(0, 0)

    def _toggle_code_folding(self, checked):
        """Toggle code folding."""
        if checked:
            self.editor.setFolding(QsciScintilla.FoldStyle.BoxedTreeFoldStyle)
        else:
            self.editor.setFolding(QsciScintilla.FoldStyle.NoFoldStyle)

    def _toggle_clean_mode(self, checked):
        """Toggle between clean mode (minimal) and explicit mode (full)."""
        try:
            # Parse current code to extract data
            current_code = self.editor.text()
            namespace = {}
            exec(current_code, namespace)

            # Toggle clean mode
            self.clean_mode = checked
            self.code_data['clean_mode'] = self.clean_mode

            # Auto-detect code type from namespace variables
            from openhcs.debug.pickle_to_python import (
                generate_complete_orchestrator_code,
                generate_complete_pipeline_steps_code,
                generate_complete_function_pattern_code,
                generate_config_code
            )

            # Check what variables exist in the namespace to determine code type
            if 'plate_paths' in namespace or 'pipeline_data' in namespace:
                # Orchestrator code
                plate_paths = namespace.get('plate_paths', [])
                pipeline_data = namespace.get('pipeline_data', {})
                global_config = namespace.get('global_config')
                per_plate_configs = namespace.get('per_plate_configs')
                pipeline_config = namespace.get('pipeline_config')

                new_code = generate_complete_orchestrator_code(
                    plate_paths=plate_paths,
                    pipeline_data=pipeline_data,
                    global_config=global_config,
                    per_plate_configs=per_plate_configs,
                    pipeline_config=pipeline_config,
                    clean_mode=self.clean_mode
                )
            elif 'pipeline_steps' in namespace:
                # Pipeline steps code
                pipeline_steps = namespace.get('pipeline_steps', [])

                new_code = generate_complete_pipeline_steps_code(
                    pipeline_steps=pipeline_steps,
                    clean_mode=self.clean_mode
                )
            elif 'pattern' in namespace:
                # Function pattern code (uses 'pattern' variable name)
                pattern = namespace.get('pattern')

                new_code = generate_complete_function_pattern_code(
                    func_obj=pattern,
                    clean_mode=self.clean_mode
                )
            elif 'config' in namespace:
                # Config code - auto-detect config class from the object
                config = namespace.get('config')
                config_class = type(config)

                new_code = generate_config_code(
                    config=config,
                    config_class=config_class,
                    clean_mode=self.clean_mode
                )
            else:
                # Unsupported code type
                from PyQt6.QtWidgets import QMessageBox
                QMessageBox.warning(self, "Clean Mode Toggle",
                                  "Could not detect code type. Expected one of: plate_paths, pipeline_steps, pattern, or config variable.")
                return

            # Update editor with new code
            self.editor.setText(new_code)

        except Exception as e:
            from PyQt6.QtWidgets import QMessageBox
            QMessageBox.critical(self, "Clean Mode Toggle Error",
                               f"Failed to toggle clean mode: {str(e)}")

    def get_content(self) -> str:
        """Get the edited content."""
        return self.editor.text()


class CodeEditorDialog(QDialog):
    """
    Fallback Qt native code editor dialog using QTextEdit.

    Used when QScintilla is not available.
    """

    def __init__(self, parent, initial_content: str, title: str):
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setModal(True)
        self.resize(800, 600)

        # Setup UI
        layout = QVBoxLayout(self)

        # Text editor
        self.text_edit = QTextEdit()
        self.text_edit.setPlainText(initial_content)

        # Use monospace font for code
        font = QFont("Consolas", 10)
        if not font.exactMatch():
            font = QFont("Courier New", 10)
        self.text_edit.setFont(font)

        layout.addWidget(self.text_edit)

        # Buttons
        button_layout = QHBoxLayout()

        save_btn = QPushButton("Save")
        save_btn.clicked.connect(self.accept)
        button_layout.addWidget(save_btn)

        cancel_btn = QPushButton("Cancel")
        cancel_btn.clicked.connect(self.reject)
        button_layout.addWidget(cancel_btn)

        button_layout.addStretch()
        layout.addLayout(button_layout)

        # Focus on text editor
        self.text_edit.setFocus()

    def get_content(self) -> str:
        """Get the edited content."""
        return self.text_edit.toPlainText()
