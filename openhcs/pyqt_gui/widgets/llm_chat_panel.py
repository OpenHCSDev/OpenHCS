"""
LLM Chat Panel Widget

Embeddable chat panel for LLM-powered code generation.
Can be integrated into any code editor or dialog.
"""

import logging
from typing import Optional, Callable

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QTextEdit, QPushButton,
    QLabel, QMessageBox
)
from PyQt6.QtCore import Qt, QThread, pyqtSignal
from PyQt6.QtGui import QFont

from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.services.llm_pipeline_service import LLMPipelineService

logger = logging.getLogger(__name__)


class LLMGenerationThread(QThread):
    """Background thread for LLM generation to keep UI responsive."""

    finished = pyqtSignal(str)  # Emits generated code
    error = pyqtSignal(str)     # Emits error message

    def __init__(self, service: LLMPipelineService, user_request: str, code_type: str):
        super().__init__()
        self.service = service
        self.user_request = user_request
        self.code_type = code_type

    def run(self):
        """Execute LLM generation in background."""
        try:
            generated_code = self.service.generate_code(self.user_request, self.code_type)
            self.finished.emit(generated_code)
        except Exception as e:
            self.error.emit(str(e))


class LLMChatPanel(QWidget):
    """
    Chat panel for LLM-powered code generation.

    Designed to be embedded in code editor as a side panel.
    Emits signal when code is generated for parent to handle insertion.
    """

    # Signal emitted when code is generated
    code_generated = pyqtSignal(str)

    def __init__(self, parent=None, color_scheme: Optional[PyQt6ColorScheme] = None,
                 code_type: str = None):
        """
        Initialize chat panel.

        Args:
            parent: Parent widget
            color_scheme: Color scheme for consistent styling
            code_type: Type of code being edited ('pipeline', 'step', 'config', etc.)
        """
        super().__init__(parent)

        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.style_generator = StyleSheetGenerator(self.color_scheme)
        self.code_type = code_type
        self.llm_service = LLMPipelineService()
        self.generation_thread: Optional[LLMGenerationThread] = None

        self.setup_ui()
        self.setup_connections()

    def setup_ui(self):
        """Setup UI components."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(5, 5, 5, 5)
        layout.setSpacing(5)

        # Title label
        context_name = {
            'pipeline': 'Pipeline',
            'step': 'Step',
            'config': 'Config',
            'function': 'Function',
            'orchestrator': 'Orchestrator'
        }.get(self.code_type, 'Code')

        title = QLabel(f"LLM Assist - {context_name}")
        title.setFont(QFont("Arial", 9, QFont.Weight.Bold))
        title.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};")
        layout.addWidget(title)

        # Chat history display (read-only, compact)
        self.chat_history = QTextEdit()
        self.chat_history.setReadOnly(True)
        self.chat_history.setStyleSheet(f"""
            QTextEdit {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.input_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_color)};
                border-radius: 3px;
                padding: 4px;
                font-family: 'Courier New', monospace;
                font-size: 9pt;
            }}
        """)
        layout.addWidget(self.chat_history, stretch=2)

        # User input area (compact)
        input_label = QLabel("Describe what you want:")
        input_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)}; font-size: 9pt;")
        layout.addWidget(input_label)

        self.user_input = QTextEdit()
        self.user_input.setPlaceholderText("Example: Add a step that normalizes images using percentile normalization")
        self.user_input.setStyleSheet(f"""
            QTextEdit {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.input_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_color)};
                border-radius: 3px;
                padding: 4px;
                font-size: 9pt;
            }}
        """)
        self.user_input.setMaximumHeight(80)
        layout.addWidget(self.user_input, stretch=1)

        # Button row (compact)
        button_layout = QHBoxLayout()
        button_layout.setSpacing(4)

        self.generate_button = QPushButton("Generate")
        self.generate_button.setStyleSheet(self.style_generator.generate_button_style())
        self.generate_button.setMinimumHeight(28)
        button_layout.addWidget(self.generate_button)

        self.clear_button = QPushButton("Clear")
        self.clear_button.setStyleSheet(self.style_generator.generate_button_style())
        self.clear_button.setMinimumHeight(28)
        button_layout.addWidget(self.clear_button)

        layout.addLayout(button_layout)

        # Apply panel background
        self.setStyleSheet(f"""
            QWidget {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.window_bg)};
            }}
        """)

    def setup_connections(self):
        """Setup signal/slot connections."""
        self.generate_button.clicked.connect(self.on_generate_clicked)
        self.clear_button.clicked.connect(self.on_clear_clicked)

    def on_generate_clicked(self):
        """Handle generate button click."""
        user_request = self.user_input.toPlainText().strip()

        if not user_request:
            QMessageBox.warning(self, "Empty Request", "Please describe what you want first.")
            return

        # Disable generate button during generation
        self.generate_button.setEnabled(False)
        self.generate_button.setText("Generating...")

        # Add user request to chat history
        self.append_to_history(f"<b>You:</b> {user_request}")

        # Clear input
        self.user_input.clear()

        # Start background generation
        self.generation_thread = LLMGenerationThread(
            self.llm_service, user_request, self.code_type
        )
        self.generation_thread.finished.connect(self.on_generation_finished)
        self.generation_thread.error.connect(self.on_generation_error)
        self.generation_thread.start()

    def on_generation_finished(self, generated_code: str):
        """Handle successful generation."""
        # Re-enable button
        self.generate_button.setEnabled(True)
        self.generate_button.setText("Generate")

        # Add success message to history
        self.append_to_history(f"<b>LLM:</b> Code generated (inserted into editor)")

        # Emit signal for parent to handle insertion
        self.code_generated.emit(generated_code)

    def on_generation_error(self, error_message: str):
        """Handle generation error."""
        # Re-enable button
        self.generate_button.setEnabled(True)
        self.generate_button.setText("Generate")

        # Show error in chat history
        self.append_to_history(f"<b style='color: red;'>Error:</b> {error_message}")

        # Show error dialog
        QMessageBox.critical(self, "Generation Failed",
                           f"Failed to generate code:\n\n{error_message}")

    def on_clear_clicked(self):
        """Clear chat history."""
        self.chat_history.clear()

    def append_to_history(self, message: str):
        """Append message to chat history."""
        self.chat_history.append(message)
        self.chat_history.append("")  # Add blank line for spacing

        # Scroll to bottom
        scrollbar = self.chat_history.verticalScrollBar()
        scrollbar.setValue(scrollbar.maximum())
