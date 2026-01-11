"""
LLM Chat Panel Widget

Embeddable chat panel for LLM-powered code generation.
Can be integrated into any code editor or dialog.
"""

import html
import logging
from typing import Optional

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QTextEdit, QPushButton,
    QLabel, QMessageBox, QDialog, QFormLayout, QLineEdit, QDialogButtonBox,
    QComboBox
)
from PyQt6.QtCore import pyqtSignal
from PyQt6.QtGui import QFont

from pyqt_formgen.theming import ColorScheme
from pyqt_formgen.theming import StyleSheetGenerator
from pyqt_formgen.core import BackgroundTaskManager
from pyqt_formgen.widgets import StatusIndicator, StatusState
from pyqt_formgen.core import RichTextAppender
from pyqt_formgen.protocols import get_llm_service, register_llm_service, LLMServiceProtocol

logger = logging.getLogger(__name__)


class LLMStatusIndicator(StatusIndicator):
    """StatusIndicator that also controls generate button enable/disable."""

    def __init__(self, generate_button: QPushButton, **kwargs):
        self._generate_button = generate_button
        super().__init__(**kwargs)

    def set_state(self, state: StatusState, message: str = None):
        super().set_state(state, message)
        # Only enable generate when connected
        self._generate_button.setEnabled(state == StatusState.CONNECTED)


class LLMChatPanel(QWidget):
    """
    Chat panel for LLM-powered code generation.

    Designed to be embedded in code editor as a side panel.
    Emits signal when code is generated for parent to handle insertion.
    """

    code_generated = pyqtSignal(str)

    def __init__(self, parent=None, color_scheme: Optional[ColorScheme] = None,
                 code_type: str = None, llm_service: Optional[LLMServiceProtocol] = None):
        super().__init__(parent)

        self.color_scheme = color_scheme or ColorScheme()
        self.style_generator = StyleSheetGenerator(self.color_scheme)
        self.code_type = code_type
        self.llm_service = llm_service or get_llm_service()
        if self.llm_service is None:
            raise RuntimeError("No LLM service registered. Call register_llm_service(...) before creating LLMChatPanel.")

        # State
        self._pending_code: Optional[str] = None
        self._last_request: Optional[str] = None

        # Abstractions from plan_00
        self._generation_tasks = BackgroundTaskManager()

        self._setup_ui()
        self._setup_connections()

    def _setup_ui(self):
        layout = QVBoxLayout(self)
        layout.setContentsMargins(5, 5, 5, 5)
        layout.setSpacing(5)

        # --- Header: Title + Status Indicator ---
        context_name = {
            'pipeline': 'Pipeline', 'step': 'Step', 'config': 'Config',
            'function': 'Function', 'orchestrator': 'Orchestrator'
        }.get(self.code_type, 'Code')

        header_layout = QHBoxLayout()
        header_layout.setSpacing(8)

        title = QLabel(f"LLM Assist - {context_name}")
        title.setFont(QFont("Arial", 9, QFont.Weight.Bold))
        title.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};")
        header_layout.addWidget(title)
        header_layout.addStretch()

        # Generate button (created early so StatusIndicator can reference it)
        self.generate_button = QPushButton("Generate")
        self.generate_button.setStyleSheet(self.style_generator.generate_button_style())
        self.generate_button.setMinimumHeight(28)
        self.generate_button.setEnabled(False)  # Disabled until connection confirmed

        # Status indicator controls generate button
        self._status_indicator = LLMStatusIndicator(
            generate_button=self.generate_button,
            check_fn=self.llm_service.test_connection,
            color_scheme=self.color_scheme,
            parent=self
        )
        header_layout.addWidget(self._status_indicator)

        # Settings button (gear icon)
        self.settings_button = QPushButton("⚙")
        self.settings_button.setFixedSize(24, 24)
        self.settings_button.setToolTip("Configure LLM endpoint")
        self.settings_button.setStyleSheet(self.style_generator.generate_button_style())
        header_layout.addWidget(self.settings_button)

        layout.addLayout(header_layout)

        # --- Chat History ---
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

        # RichTextAppender for chat history
        self._chat_appender = RichTextAppender(self.chat_history, color_scheme=self.color_scheme)

        # --- Action Buttons (Insert / Regenerate) - initially hidden ---
        action_layout = QHBoxLayout()
        action_layout.setSpacing(8)

        self.insert_button = QPushButton("Insert into Editor")
        self.insert_button.setStyleSheet(self.style_generator.generate_button_style())
        action_layout.addWidget(self.insert_button)

        self.regenerate_button = QPushButton("Regenerate")
        self.regenerate_button.setStyleSheet(self.style_generator.generate_button_style())
        action_layout.addWidget(self.regenerate_button)

        action_layout.addStretch()

        self.action_buttons_widget = QWidget()
        self.action_buttons_widget.setLayout(action_layout)
        self.action_buttons_widget.setVisible(False)
        layout.addWidget(self.action_buttons_widget)

        # --- User Input ---
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

        # --- Bottom Buttons (Generate / Clear) ---
        button_layout = QHBoxLayout()
        button_layout.setSpacing(4)

        button_layout.addWidget(self.generate_button)

        self.clear_button = QPushButton("Clear")
        self.clear_button.setStyleSheet(self.style_generator.generate_button_style())
        self.clear_button.setMinimumHeight(28)
        button_layout.addWidget(self.clear_button)

        layout.addLayout(button_layout)

        # Panel background
        self.setStyleSheet(f"""
            QWidget {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.window_bg)};
            }}
        """)

    def _setup_connections(self):
        self.generate_button.clicked.connect(self._on_generate_clicked)
        self.clear_button.clicked.connect(self._on_clear_clicked)
        self.insert_button.clicked.connect(self._on_insert_clicked)
        self.regenerate_button.clicked.connect(self._on_regenerate_clicked)
        self.settings_button.clicked.connect(self._on_settings_clicked)

    def _on_generate_clicked(self):
        user_request = self.user_input.toPlainText().strip()
        if not user_request:
            QMessageBox.warning(self, "Empty Request", "Please describe what you want.")
            return

        self._last_request = user_request
        self.action_buttons_widget.setVisible(False)
        self._start_generation(user_request)

    def _start_generation(self, request: str):
        self._chat_appender.append_html(f"<b>You:</b> {html.escape(request)}")
        self.user_input.clear()

        self._generation_tasks.run(
            target=lambda: self.llm_service.generate_code(request, self.code_type),
            button=self.generate_button,
            button_loading_text="Generating...",
            on_success=self._on_generation_success,
            on_error=self._on_generation_error,
        )

    def _on_generation_success(self, code: str):
        self._pending_code = code
        self._chat_appender.append_text("Generated:", bold=True)
        self._chat_appender.append_code(code)
        self.action_buttons_widget.setVisible(True)

    def _on_generation_error(self, error: Exception):
        self._chat_appender.append_error(str(error))

    def _on_insert_clicked(self):
        if self._pending_code:
            self.code_generated.emit(self._pending_code)
            self._chat_appender.append_success("Code inserted into editor.")
        self.action_buttons_widget.setVisible(False)
        self._pending_code = None

    def _on_regenerate_clicked(self):
        if self._last_request:
            self.action_buttons_widget.setVisible(False)
            self._start_generation(self._last_request)

    def _on_clear_clicked(self):
        self._chat_appender.clear()
        self.action_buttons_widget.setVisible(False)
        self._pending_code = None

    def _on_settings_clicked(self):
        """Open settings dialog for LLM configuration."""
        dialog = QDialog(self)
        dialog.setWindowTitle("LLM Settings")
        dialog.setMinimumWidth(400)

        layout = QFormLayout(dialog)

        # Endpoint field
        endpoint_edit = QLineEdit(self.llm_service.api_endpoint)
        endpoint_edit.setPlaceholderText("http://localhost:11434/api/generate")
        layout.addRow("API Endpoint:", endpoint_edit)

        # Model dropdown - fetch available models
        model_combo = QComboBox()
        model_combo.setEditable(True)  # Allow custom model names
        available_models = self.llm_service._get_available_models()
        if available_models:
            model_combo.addItems(available_models)
            # Select current model if available
            if self.llm_service.model and self.llm_service.model in available_models:
                model_combo.setCurrentText(self.llm_service.model)
            elif self.llm_service.model:
                model_combo.setCurrentText(self.llm_service.model)
        else:
            model_combo.addItem("(no models found - check Ollama)")
            if self.llm_service.model:
                model_combo.setCurrentText(self.llm_service.model)

        layout.addRow("Model:", model_combo)

        # Buttons
        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel
        )
        buttons.accepted.connect(dialog.accept)
        buttons.rejected.connect(dialog.reject)
        layout.addRow(buttons)

        if dialog.exec() == QDialog.DialogCode.Accepted:
            new_endpoint = endpoint_edit.text().strip()
            new_model = model_combo.currentText().strip()

            if new_endpoint and new_model and not new_model.startswith("("):
                service_cls = self.llm_service.__class__
                try:
                    self.llm_service = service_cls(api_endpoint=new_endpoint, model=new_model)
                    register_llm_service(self.llm_service)
                except Exception as e:
                    QMessageBox.critical(self, "LLM Settings", f"Failed to reconfigure LLM service: {e}")
                    return

                # Update status indicator's check function
                self._status_indicator._check_fn = self.llm_service.test_connection
                self._status_indicator.refresh(force=True)

    def closeEvent(self, event):
        self._generation_tasks.cleanup()
        super().closeEvent(event)
