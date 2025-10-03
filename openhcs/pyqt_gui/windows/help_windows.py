"""PyQt6 help system - reuses Textual TUI help logic and components."""

import logging
from typing import Union, Callable, Optional
from PyQt6.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QPushButton, QLabel, 
    QTextEdit, QScrollArea, QWidget, QMessageBox
)
from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QFont

# REUSE the actual working Textual TUI help components
from openhcs.ui.shared.signature_analyzer import DocstringExtractor, SignatureAnalyzer
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator

logger = logging.getLogger(__name__)


class BaseHelpWindow(QDialog):
    """Base class for all PyQt6 help windows - reuses Textual TUI help logic."""
    
    def __init__(self, title: str = "Help", color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        super().__init__(parent)

        # Initialize color scheme and style generator
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.style_generator = StyleSheetGenerator(self.color_scheme)

        self.setWindowTitle(title)
        self.setModal(False)  # Allow interaction with main window
        self.resize(600, 400)

        # Setup UI
        self.setup_ui()

        # Apply centralized styling
        self.setStyleSheet(self.style_generator.generate_dialog_style())
        
    def setup_ui(self):
        """Setup the base help window UI."""
        layout = QVBoxLayout(self)
        
        # Content area (to be filled by subclasses)
        self.content_area = QScrollArea()
        self.content_area.setWidgetResizable(True)
        self.content_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.content_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        layout.addWidget(self.content_area)
        
        # Close button
        button_layout = QHBoxLayout()
        button_layout.addStretch()
        
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(self.close)
        button_layout.addWidget(close_btn)
        
        layout.addLayout(button_layout)


class DocstringHelpWindow(BaseHelpWindow):
    """Help window for functions and classes - reuses Textual TUI DocstringExtractor."""
    
    def __init__(self, target: Union[Callable, type], title: Optional[str] = None,
                 color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        self.target = target

        # REUSE Textual TUI docstring extraction logic
        self.docstring_info = DocstringExtractor.extract(target)

        # Generate title from target if not provided
        if title is None:
            if hasattr(target, '__name__'):
                title = f"Help: {target.__name__}"
            else:
                title = "Help"

        super().__init__(title, color_scheme, parent)
        self.populate_content()
        
    def populate_content(self):
        """Populate the help content with minimal styling."""
        content_widget = QWidget()
        layout = QVBoxLayout(content_widget)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(5)

        # Function/class summary
        if self.docstring_info.summary:
            summary_label = QLabel(self.docstring_info.summary)
            summary_label.setWordWrap(True)
            summary_label.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
            summary_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 12px;")
            layout.addWidget(summary_label)

        # Full description
        if self.docstring_info.description:
            desc_label = QLabel(self.docstring_info.description)
            desc_label.setWordWrap(True)
            desc_label.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
            desc_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 12px;")
            layout.addWidget(desc_label)
            
        # Parameters section
        if self.docstring_info.parameters:
            params_label = QLabel("Parameters:")
            params_label.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
            params_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)}; font-size: 14px; font-weight: bold; margin-top: 8px;")
            layout.addWidget(params_label)

            for param_name, param_desc in self.docstring_info.parameters.items():
                # Parameter name
                name_label = QLabel(f"• {param_name}")
                name_label.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
                name_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 12px; margin-left: 5px; margin-top: 3px;")
                layout.addWidget(name_label)

                # Parameter description
                if param_desc:
                    desc_label = QLabel(param_desc)
                    desc_label.setWordWrap(True)
                    desc_label.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
                    desc_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 12px; margin-left: 20px;")
                    layout.addWidget(desc_label)
                
        # Returns section
        if self.docstring_info.returns:
            returns_label = QLabel("Returns:")
            returns_label.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
            returns_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)}; font-size: 14px; font-weight: bold; margin-top: 8px;")
            layout.addWidget(returns_label)

            returns_desc = QLabel(self.docstring_info.returns)
            returns_desc.setWordWrap(True)
            returns_desc.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
            returns_desc.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 12px; margin-left: 5px;")
            layout.addWidget(returns_desc)
            
        # Examples section
        if self.docstring_info.examples:
            examples_label = QLabel("Examples:")
            examples_label.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
            examples_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)}; font-size: 14px; font-weight: bold; margin-top: 8px;")
            layout.addWidget(examples_label)

            examples_text = QTextEdit()
            examples_text.setPlainText(self.docstring_info.examples)
            examples_text.setReadOnly(True)
            examples_text.setMaximumHeight(150)
            examples_text.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
            examples_text.setStyleSheet(f"""
                QTextEdit {{
                    background-color: transparent;
                    color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
                    border: none;
                    font-family: monospace;
                    font-size: 11px;
                }}
                QTextEdit:hover {{
                    background-color: transparent;
                }}
            """)
            layout.addWidget(examples_text)
            
        layout.addStretch()
        self.content_area.setWidget(content_widget)


class ParameterHelpWindow(BaseHelpWindow):
    """Help window for individual parameters - reuses Textual TUI parameter logic."""
    
    def __init__(self, param_name: str, param_description: str, param_type: type = None,
                 color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        self.param_name = param_name
        self.param_description = param_description
        self.param_type = param_type

        title = f"Parameter Help: {param_name}"
        super().__init__(title, color_scheme, parent)
        self.populate_content()
        
    def populate_content(self):
        """Populate parameter help content with minimal styling."""
        content_widget = QWidget()
        layout = QVBoxLayout(content_widget)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(5)

        # Parameter name and type
        header_text = f"• {self.param_name}"
        if self.param_type:
            type_name = getattr(self.param_type, '__name__', str(self.param_type))
            header_text += f" ({type_name})"

        header_label = QLabel(header_text)
        header_label.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
        header_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 12px;")
        layout.addWidget(header_label)

        # Parameter description
        if self.param_description:
            desc_label = QLabel(self.param_description)
            desc_label.setWordWrap(True)
            desc_label.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
            desc_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 12px; margin-left: 15px;")
            layout.addWidget(desc_label)
        else:
            no_desc_label = QLabel("No description available")
            no_desc_label.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
            no_desc_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_disabled)}; font-size: 12px; font-style: italic; margin-left: 15px;")
            layout.addWidget(no_desc_label)

        layout.addStretch()
        self.content_area.setWidget(content_widget)


class HelpWindowManager:
    """PyQt6 help window manager - reuses Textual TUI help logic."""
    
    # Class-level storage for singleton windows
    _docstring_window = None
    _parameter_window = None
    
    @classmethod
    def show_docstring_help(cls, target: Union[Callable, type], title: Optional[str] = None, parent=None):
        """Show help for a function or class - reuses Textual TUI extraction logic."""
        try:
            # Check if existing window is still valid
            if cls._docstring_window and hasattr(cls._docstring_window, 'isVisible'):
                try:
                    if not cls._docstring_window.isHidden():
                        cls._docstring_window.target = target
                        cls._docstring_window.docstring_info = DocstringExtractor.extract(target)
                        cls._docstring_window.populate_content()
                        cls._docstring_window.raise_()
                        cls._docstring_window.activateWindow()
                        return
                except RuntimeError:
                    # Window was deleted, clear reference
                    cls._docstring_window = None

            # Create new window
            cls._docstring_window = DocstringHelpWindow(target, title=title, parent=parent)
            cls._docstring_window.show()

        except Exception as e:
            logger.error(f"Failed to show docstring help: {e}")
            QMessageBox.warning(parent, "Help Error", f"Failed to show help: {e}")
    
    @classmethod
    def show_parameter_help(cls, param_name: str, param_description: str, param_type: type = None, parent=None):
        """Show help for a parameter - reuses Textual TUI parameter logic."""
        try:
            # Check if existing window is still valid
            if cls._parameter_window and hasattr(cls._parameter_window, 'isVisible'):
                try:
                    if not cls._parameter_window.isHidden():
                        cls._parameter_window.param_name = param_name
                        cls._parameter_window.param_description = param_description
                        cls._parameter_window.param_type = param_type
                        cls._parameter_window.populate_content()
                        cls._parameter_window.raise_()
                        cls._parameter_window.activateWindow()
                        return
                except RuntimeError:
                    # Window was deleted, clear reference
                    cls._parameter_window = None

            # Create new window
            cls._parameter_window = ParameterHelpWindow(param_name, param_description, param_type, parent=parent)
            cls._parameter_window.show()

        except Exception as e:
            logger.error(f"Failed to show parameter help: {e}")
            QMessageBox.warning(parent, "Help Error", f"Failed to show help: {e}")


class HelpableWidget:
    """Mixin class to add help functionality to PyQt6 widgets - mirrors Textual TUI."""
    
    def show_function_help(self, target: Union[Callable, type]) -> None:
        """Show help window for a function or class."""
        HelpWindowManager.show_docstring_help(target, parent=self)
        
    def show_parameter_help(self, param_name: str, param_description: str, param_type: type = None) -> None:
        """Show help window for a parameter."""
        HelpWindowManager.show_parameter_help(param_name, param_description, param_type, parent=self)
