"""
Plate Manager Widget for PyQt6

Manages plate selection, initialization, and execution with full feature parity
to the Textual TUI version. Uses hybrid approach: extracted business logic + clean PyQt6 UI.
"""

import logging
import asyncio
import inspect
import copy
import sys
import subprocess
import tempfile
from typing import List, Dict, Optional, Callable
from pathlib import Path

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QListWidget,
    QListWidgetItem, QLabel, QProgressBar,
    QSplitter
)
from PyQt6.QtCore import Qt, pyqtSignal, pyqtSlot
from PyQt6.QtGui import QFont

from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.config import PipelineConfig
from openhcs.io.filemanager import FileManager
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator, OrchestratorState
from openhcs.core.pipeline import Pipeline
from openhcs.constants.constants import VariableComponents
from openhcs.pyqt_gui.widgets.mixins import (
    preserve_selection_during_update,
    handle_selection_change_with_prevention
)
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme

logger = logging.getLogger(__name__)


class PlateManagerWidget(QWidget):
    """
    PyQt6 Plate Manager Widget.
    
    Manages plate selection, initialization, compilation, and execution.
    Preserves all business logic from Textual version with clean PyQt6 UI.
    """
    
    # Signals
    plate_selected = pyqtSignal(str)  # plate_path
    status_message = pyqtSignal(str)  # status message
    orchestrator_state_changed = pyqtSignal(str, str)  # plate_path, state
    orchestrator_config_changed = pyqtSignal(str, object)  # plate_path, effective_config

    # Configuration change signals for tier 3 UI-code conversion
    global_config_changed = pyqtSignal()  # global config updated
    pipeline_data_changed = pyqtSignal()  # pipeline data updated

    # Log viewer integration signals
    subprocess_log_started = pyqtSignal(str)  # base_log_path
    subprocess_log_stopped = pyqtSignal()
    clear_subprocess_logs = pyqtSignal()

    # Progress update signals (thread-safe UI updates)
    progress_started = pyqtSignal(int)  # max_value
    progress_updated = pyqtSignal(int)  # current_value
    progress_finished = pyqtSignal()

    # Error handling signals (thread-safe error reporting)
    compilation_error = pyqtSignal(str, str)  # plate_name, error_message
    initialization_error = pyqtSignal(str, str)  # plate_name, error_message
    execution_error = pyqtSignal(str)  # error_message
    
    def __init__(self, file_manager: FileManager, service_adapter,
                 color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        """
        Initialize the plate manager widget.

        Args:
            file_manager: FileManager instance for file operations
            service_adapter: PyQt service adapter for dialogs and operations
            color_scheme: Color scheme for styling (optional, uses service adapter if None)
            parent: Parent widget
        """
        super().__init__(parent)

        # Core dependencies
        self.file_manager = file_manager
        self.service_adapter = service_adapter
        self.global_config = service_adapter.get_global_config()
        self.pipeline_editor = None  # Will be set by main window

        # Initialize color scheme and style generator
        self.color_scheme = color_scheme or service_adapter.get_current_color_scheme()
        self.style_generator = StyleSheetGenerator(self.color_scheme)
        
        # Business logic state (extracted from Textual version)
        self.plates: List[Dict] = []  # List of plate dictionaries
        self.selected_plate_path: str = ""
        self.orchestrators: Dict[str, PipelineOrchestrator] = {}
        self.plate_configs: Dict[str, Dict] = {}
        self.plate_compiled_data: Dict[str, tuple] = {}  # Store compiled pipeline data
        self.current_process = None
        self.zmq_client = None  # ZMQ execution client (when using ZMQ mode)
        self.current_execution_id = None  # Track current execution ID for cancellation
        self.execution_state = "idle"
        self.log_file_path: Optional[str] = None
        self.log_file_position: int = 0
        
        # UI components
        self.plate_list: Optional[QListWidget] = None
        self.buttons: Dict[str, QPushButton] = {}
        self.status_label: Optional[QLabel] = None
        self.progress_bar: Optional[QProgressBar] = None
        
        # Setup UI
        self.setup_ui()
        self.setup_connections()
        self.update_button_states()
        
        logger.debug("Plate manager widget initialized")

    # ========== UI Setup ==========

    def setup_ui(self):
        """Setup the user interface."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(2, 2, 2, 2)
        layout.setSpacing(2)
        
        # Title
        title_label = QLabel("Plate Manager")
        title_label.setFont(QFont("Arial", 12, QFont.Weight.Bold))
        title_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)}; padding: 5px;")
        layout.addWidget(title_label)
        
        # Main content splitter
        splitter = QSplitter(Qt.Orientation.Vertical)
        layout.addWidget(splitter)
        
        # Plate list
        self.plate_list = QListWidget()
        self.plate_list.setSelectionMode(QListWidget.SelectionMode.ExtendedSelection)
        # Apply explicit styling to plate list for consistent background
        self.plate_list.setStyleSheet(f"""
            QListWidget {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.panel_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
                border: none;
                padding: 5px;
            }}
            QListWidget::item {{
                padding: 8px;
                border: none;
                border-radius: 3px;
                margin: 2px;
            }}
            QListWidget::item:selected {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.selection_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.selection_text)};
            }}
            QListWidget::item:hover {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.hover_bg)};
            }}
        """)
        # Apply centralized styling to main widget
        self.setStyleSheet(self.style_generator.generate_plate_manager_style())
        splitter.addWidget(self.plate_list)

        # Button panel
        button_panel = self.create_button_panel()
        splitter.addWidget(button_panel)

        # Status section
        status_frame = self.create_status_section()
        layout.addWidget(status_frame)

        # Set splitter proportions - make button panel much smaller
        splitter.setSizes([400, 80])
    
    def create_button_panel(self) -> QWidget:
        """
        Create the button panel with all plate management actions.

        Returns:
            Widget containing action buttons
        """
        panel = QWidget()
        # Set consistent background
        panel.setStyleSheet(f"""
            QWidget {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.window_bg)};
                border: none;
                padding: 0px;
            }}
        """)

        layout = QVBoxLayout(panel)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(2)
        
        # Button configurations (extracted from Textual version)
        button_configs = [
            ("Add", "add_plate", "Add new plate directory"),
            ("Del", "del_plate", "Delete selected plates"),
            ("Edit", "edit_config", "Edit plate configuration"),
            ("Init", "init_plate", "Initialize selected plates"),
            ("Compile", "compile_plate", "Compile plate pipelines"),
            ("Run", "run_plate", "Run/Stop plate execution"),
            ("Code", "code_plate", "Generate Python code"),
            ("Meta", "view_metadata", "View plate metadata"),
        ]
        
        # Create buttons in rows
        for i in range(0, len(button_configs), 4):
            row_layout = QHBoxLayout()
            row_layout.setContentsMargins(2, 2, 2, 2)
            row_layout.setSpacing(2)

            for j in range(4):
                if i + j < len(button_configs):
                    name, action, tooltip = button_configs[i + j]

                    button = QPushButton(name)
                    button.setToolTip(tooltip)
                    button.setMinimumHeight(30)
                    # Apply explicit button styling to ensure it works
                    button.setStyleSheet(self.style_generator.generate_button_style())

                    # Connect button to action
                    button.clicked.connect(lambda checked, a=action: self.handle_button_action(a))

                    self.buttons[action] = button
                    row_layout.addWidget(button)
                else:
                    row_layout.addStretch()

            layout.addLayout(row_layout)

        # Set maximum height to constrain the button panel (2 rows of buttons)
        panel.setMaximumHeight(80)

        return panel
    
    def create_status_section(self) -> QWidget:
        """
        Create the status section with progress bar and status label.

        Returns:
            Widget containing status information
        """
        frame = QWidget()
        # Set consistent background
        frame.setStyleSheet(f"""
            QWidget {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.window_bg)};
                border: none;
                padding: 2px;
            }}
        """)

        layout = QVBoxLayout(frame)
        layout.setContentsMargins(2, 2, 2, 2)
        layout.setSpacing(2)
        
        # Status label
        self.status_label = QLabel("Ready")
        self.status_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.status_success)}; font-weight: bold;")
        layout.addWidget(self.status_label)
        
        # Progress bar
        self.progress_bar = QProgressBar()
        self.progress_bar.setVisible(False)
        # Progress bar styling is handled by the main widget stylesheet
        layout.addWidget(self.progress_bar)
        
        return frame
    
    def setup_connections(self):
        """Setup signal/slot connections."""
        # Plate list selection
        self.plate_list.itemSelectionChanged.connect(self.on_selection_changed)
        self.plate_list.itemDoubleClicked.connect(self.on_item_double_clicked)
        
        # Internal signals
        self.status_message.connect(self.update_status)
        self.orchestrator_state_changed.connect(self.on_orchestrator_state_changed)

        # Progress signals for thread-safe UI updates
        self.progress_started.connect(self._on_progress_started)
        self.progress_updated.connect(self._on_progress_updated)
        self.progress_finished.connect(self._on_progress_finished)

        # Error handling signals for thread-safe error reporting
        self.compilation_error.connect(self._handle_compilation_error)
        self.initialization_error.connect(self._handle_initialization_error)
        self.execution_error.connect(self._handle_execution_error)
    
    def handle_button_action(self, action: str):
        """
        Handle button actions (extracted from Textual version).

        Args:
            action: Action identifier
        """
        # Action mapping (preserved from Textual version)
        action_map = {
            "add_plate": self.action_add_plate,
            "del_plate": self.action_delete_plate,
            "edit_config": self.action_edit_config,
            "init_plate": self.action_init_plate,
            "compile_plate": self.action_compile_plate,
            "code_plate": self.action_code_plate,
            "view_metadata": self.action_view_metadata,
        }

        if action in action_map:
            action_func = action_map[action]

            # Handle async actions
            if inspect.iscoroutinefunction(action_func):
                self.run_async_action(action_func)
            else:
                action_func()
        elif action == "run_plate":
            if self.is_any_plate_running():
                self.run_async_action(self.action_stop_execution)
            else:
                self.run_async_action(self.action_run_plate)
        else:
            logger.warning(f"Unknown action: {action}")
    
    def run_async_action(self, async_func: Callable):
        """
        Run async action using service adapter.

        Args:
            async_func: Async function to execute
        """
        self.service_adapter.execute_async_operation(async_func)

    def _update_orchestrator_global_config(self, orchestrator, new_global_config):
        """Update orchestrator's global config reference and rebuild pipeline config if needed."""
        from openhcs.config_framework.lazy_factory import rebuild_lazy_config_with_new_global_reference
        from openhcs.core.config import GlobalPipelineConfig

        # SIMPLIFIED: Update shared global context (dual-axis resolver handles context)
        from openhcs.config_framework.lazy_factory import ensure_global_config_context
        ensure_global_config_context(GlobalPipelineConfig, new_global_config)

        # Rebuild orchestrator-specific config if it exists
        if orchestrator.pipeline_config is not None:
            orchestrator.pipeline_config = rebuild_lazy_config_with_new_global_reference(
                orchestrator.pipeline_config,
                new_global_config,
                GlobalPipelineConfig
            )
            logger.info(f"Rebuilt orchestrator-specific config for plate: {orchestrator.plate_path}")

        # Get effective config and emit signal for UI refresh
        effective_config = orchestrator.get_effective_config()
        self.orchestrator_config_changed.emit(str(orchestrator.plate_path), effective_config)
    
    # ========== Business Logic Methods (Extracted from Textual) ==========
    
    def action_add_plate(self):
        """Handle Add Plate button (adapted from Textual version)."""
        from openhcs.core.path_cache import PathCacheKey

        # Use cached directory dialog (mirrors Textual TUI pattern)
        directory_path = self.service_adapter.show_cached_directory_dialog(
            cache_key=PathCacheKey.PLATE_IMPORT,
            title="Select Plate Directory",
            fallback_path=Path.home()
        )

        if directory_path:
            self.add_plate_callback([directory_path])
    
    def add_plate_callback(self, selected_paths: List[Path]):
        """
        Handle plate directory selection (extracted from Textual version).
        
        Args:
            selected_paths: List of selected directory paths
        """
        if not selected_paths:
            self.status_message.emit("Plate selection cancelled")
            return
        
        added_plates = []
        
        for selected_path in selected_paths:
            # Check if plate already exists
            if any(plate['path'] == str(selected_path) for plate in self.plates):
                continue
            
            # Add the plate to the list
            plate_name = selected_path.name
            plate_path = str(selected_path)
            plate_entry = {
                'name': plate_name,
                'path': plate_path,
            }
            
            self.plates.append(plate_entry)
            added_plates.append(plate_name)
        
        if added_plates:
            self.update_plate_list()
            self.status_message.emit(f"Added {len(added_plates)} plate(s): {', '.join(added_plates)}")
        else:
            self.status_message.emit("No new plates added (duplicates skipped)")
    
    def action_delete_plate(self):
        """Handle Delete Plate button (extracted from Textual version)."""
        selected_items = self.get_selected_plates()
        if not selected_items:
            self.service_adapter.show_error_dialog("No plate selected to delete.")
            return
        
        paths_to_delete = {p['path'] for p in selected_items}
        self.plates = [p for p in self.plates if p['path'] not in paths_to_delete]
        
        # Clean up orchestrators for deleted plates
        for path in paths_to_delete:
            if path in self.orchestrators:
                del self.orchestrators[path]
        
        if self.selected_plate_path in paths_to_delete:
            self.selected_plate_path = ""
            # Notify pipeline editor that no plate is selected (mirrors Textual TUI)
            self.plate_selected.emit("")

        self.update_plate_list()
        self.status_message.emit(f"Deleted {len(paths_to_delete)} plate(s)")
    
    def _validate_plates_for_operation(self, plates, operation_type):
        """Unified functional validator for all plate operations."""
        # Functional validation mapping
        validators = {
            'init': lambda p: True,  # Init can work on any plates
            'compile': lambda p: (
                self.orchestrators.get(p['path']) and
                self._get_current_pipeline_definition(p['path'])
            ),
            'run': lambda p: (
                self.orchestrators.get(p['path']) and
                self.orchestrators[p['path']].state in ['COMPILED', 'COMPLETED']
            )
        }

        # Functional pattern: filter invalid plates in one pass
        validator = validators.get(operation_type, lambda p: True)
        return [p for p in plates if not validator(p)]

    async def action_init_plate(self):
        """Handle Initialize Plate button with unified validation."""
        # CRITICAL: Set up global context in worker thread
        # The service adapter runs this entire function in a worker thread,
        # so we need to establish the global context here
        from openhcs.config_framework.lazy_factory import ensure_global_config_context
        from openhcs.core.config import GlobalPipelineConfig
        ensure_global_config_context(GlobalPipelineConfig, self.global_config)

        selected_items = self.get_selected_plates()

        # Unified validation - let it fail if no plates
        invalid_plates = self._validate_plates_for_operation(selected_items, 'init')

        self.progress_started.emit(len(selected_items))

        # Functional pattern: async map with enumerate
        async def init_single_plate(i, plate):
            plate_path = plate['path']
            # Create orchestrator in main thread (has access to global context)
            orchestrator = PipelineOrchestrator(
                plate_path=plate_path,
                storage_registry=self.file_manager.registry
            )
            # Only run heavy initialization in worker thread
            # Need to set up context in worker thread too since initialize() runs there
            def initialize_with_context():
                from openhcs.config_framework.lazy_factory import ensure_global_config_context
                from openhcs.core.config import GlobalPipelineConfig
                ensure_global_config_context(GlobalPipelineConfig, self.global_config)
                return orchestrator.initialize()

            await asyncio.get_event_loop().run_in_executor(
                None,
                initialize_with_context
            )

            self.orchestrators[plate_path] = orchestrator
            self.orchestrator_state_changed.emit(plate_path, "READY")

            if not self.selected_plate_path:
                self.selected_plate_path = plate_path
                self.plate_selected.emit(plate_path)

            self.progress_updated.emit(i + 1)

        # Process all plates functionally
        await asyncio.gather(*[
            init_single_plate(i, plate)
            for i, plate in enumerate(selected_items)
        ])

        self.progress_finished.emit()
        self.status_message.emit(f"Initialized {len(selected_items)} plate(s)")
    
    # Additional action methods would be implemented here following the same pattern...
    # (compile_plate, run_plate, code_plate, view_metadata, edit_config)
    
    def action_edit_config(self):
        """
        Handle Edit Config button - create per-orchestrator PipelineConfig instances.

        This enables per-orchestrator configuration without affecting global configuration.
        Shows resolved defaults from GlobalPipelineConfig with "Pipeline default: {value}" placeholders.
        """
        selected_items = self.get_selected_plates()

        if not selected_items:
            self.service_adapter.show_error_dialog("No plates selected for configuration.")
            return

        # Get selected orchestrators
        selected_orchestrators = [
            self.orchestrators[item['path']] for item in selected_items
            if item['path'] in self.orchestrators
        ]

        if not selected_orchestrators:
            self.service_adapter.show_error_dialog("No initialized orchestrators selected.")
            return

        # Load existing config or create new one for editing
        representative_orchestrator = selected_orchestrators[0]

        # CRITICAL FIX: Don't change thread-local context - preserve orchestrator context
        # The config window should work with the current orchestrator context
        # Reset behavior will be handled differently to avoid corrupting step editor context

        # CRITICAL FIX: Create PipelineConfig that preserves user-set values but shows placeholders for inherited fields
        # The orchestrator's pipeline_config has concrete values filled in from global config inheritance,
        # but we need to distinguish between user-set values (keep concrete) and inherited values (show as placeholders)
        from openhcs.config_framework.lazy_factory import create_dataclass_for_editing
        from dataclasses import fields

        # CRITICAL FIX: Create config for editing that preserves user values while showing placeholders for inherited fields
        if representative_orchestrator.pipeline_config is not None:
            # Orchestrator has existing config - preserve explicitly set fields, reset others to None for placeholders
            existing_config = representative_orchestrator.pipeline_config
            explicitly_set_fields = getattr(existing_config, '_explicitly_set_fields', set())

            # Create field values: keep explicitly set values, use None for inherited fields
            field_values = {}
            for field in fields(PipelineConfig):
                if field.name in explicitly_set_fields:
                    # User explicitly set this field - preserve the concrete value
                    field_values[field.name] = object.__getattribute__(existing_config, field.name)
                else:
                    # Field was inherited from global config - use None to show placeholder
                    field_values[field.name] = None

            # Create config with preserved user values and None for inherited fields
            current_plate_config = PipelineConfig(**field_values)
            # Preserve the explicitly set fields tracking (bypass frozen restriction)
            object.__setattr__(current_plate_config, '_explicitly_set_fields', explicitly_set_fields.copy())
        else:
            # No existing config - create fresh config with all None values (all show as placeholders)
            current_plate_config = create_dataclass_for_editing(PipelineConfig, self.global_config)

        def handle_config_save(new_config: PipelineConfig) -> None:
            """Apply per-orchestrator configuration without global side effects."""
            # SIMPLIFIED: Debug logging without thread-local context
            from dataclasses import fields
            logger.debug(f"🔍 CONFIG SAVE - new_config type: {type(new_config)}")
            for field in fields(new_config):
                raw_value = object.__getattribute__(new_config, field.name)
                logger.debug(f"🔍 CONFIG SAVE - new_config.{field.name} = {raw_value}")

            for orchestrator in selected_orchestrators:
                # Direct synchronous call - no async needed
                orchestrator.apply_pipeline_config(new_config)
                # Emit signal for UI components to refresh
                effective_config = orchestrator.get_effective_config()
                self.orchestrator_config_changed.emit(str(orchestrator.plate_path), effective_config)

            # Auto-sync handles context restoration automatically when pipeline_config is accessed
            if self.selected_plate_path and self.selected_plate_path in self.orchestrators:
                logger.debug(f"Orchestrator context automatically maintained after config save: {self.selected_plate_path}")

            count = len(selected_orchestrators)
            # Success message dialog removed for test automation compatibility

        # Open configuration window using PipelineConfig (not GlobalPipelineConfig)
        # PipelineConfig already imported from openhcs.core.config
        self._open_config_window(
            config_class=PipelineConfig,
            current_config=current_plate_config,
            on_save_callback=handle_config_save,
            orchestrator=representative_orchestrator  # Pass orchestrator for context persistence
        )

    def _open_config_window(self, config_class, current_config, on_save_callback, orchestrator=None):
        """
        Open configuration window with specified config class and current config.

        Args:
            config_class: Configuration class type (PipelineConfig or GlobalPipelineConfig)
            current_config: Current configuration instance
            on_save_callback: Function to call when config is saved
            orchestrator: Optional orchestrator reference for context persistence
        """
        from openhcs.pyqt_gui.windows.config_window import ConfigWindow
        from openhcs.config_framework.context_manager import config_context


        # SIMPLIFIED: ConfigWindow now uses the dataclass instance directly for context
        # No need for external context management - the form manager handles it automatically
        with config_context(orchestrator.pipeline_config):
            config_window = ConfigWindow(
                config_class,           # config_class
                current_config,         # current_config
                on_save_callback,       # on_save_callback
                self.color_scheme,      # color_scheme
                self,                   # parent
            )

            # CRITICAL: Connect to orchestrator config changes for automatic refresh
            # This ensures the config window stays in sync when tier 3 edits change the underlying config
            if orchestrator and hasattr(config_window, 'refresh_config'):
                def handle_orchestrator_config_change(plate_path: str, effective_config):
                    # Only refresh if this is for the same orchestrator
                    if plate_path == str(orchestrator.plate_path):
                        # Get the updated pipeline config from the orchestrator
                        updated_pipeline_config = orchestrator.pipeline_config
                        if updated_pipeline_config:
                            config_window.refresh_config(updated_pipeline_config)
                            logger.debug(f"Auto-refreshed config window for orchestrator: {plate_path}")

                # Connect the signal
                self.orchestrator_config_changed.connect(handle_orchestrator_config_change)

                # Store the connection so we can disconnect it when the window closes
                config_window._orchestrator_signal_connection = handle_orchestrator_config_change

            # Show as non-modal window (like main window configuration)
            config_window.show()
            config_window.raise_()
            config_window.activateWindow()

    def action_edit_global_config(self):
        """
        Handle global configuration editing - affects all orchestrators.

        Uses concrete GlobalPipelineConfig for direct editing with static placeholder defaults.
        """
        from openhcs.core.config import GlobalPipelineConfig

        # Get current global config from service adapter or use default
        current_global_config = self.service_adapter.get_global_config() or GlobalPipelineConfig()

        def handle_global_config_save(new_config: GlobalPipelineConfig) -> None:
            """Apply global configuration to all orchestrators and save to cache."""
            self.service_adapter.set_global_config(new_config)  # Update app-level config

            # Update thread-local storage for MaterializationPathConfig defaults
            from openhcs.core.config import GlobalPipelineConfig
            from openhcs.config_framework.global_config import set_global_config_for_editing
            set_global_config_for_editing(GlobalPipelineConfig, new_config)

            # Save to cache for persistence between sessions
            self._save_global_config_to_cache(new_config)

            for orchestrator in self.orchestrators.values():
                self._update_orchestrator_global_config(orchestrator, new_config)

            # SIMPLIFIED: Dual-axis resolver handles context discovery automatically
            if self.selected_plate_path and self.selected_plate_path in self.orchestrators:
                logger.debug(f"Global config applied to selected orchestrator: {self.selected_plate_path}")

            self.service_adapter.show_info_dialog("Global configuration applied to all orchestrators")

        # Open configuration window using concrete GlobalPipelineConfig
        self._open_config_window(
            config_class=GlobalPipelineConfig,
            current_config=current_global_config,
            on_save_callback=handle_global_config_save
        )

    def _save_global_config_to_cache(self, config: GlobalPipelineConfig):
        """Save global config to cache for persistence between sessions."""
        try:
            # Use synchronous saving to ensure it completes
            from openhcs.core.config_cache import _sync_save_config
            from openhcs.core.xdg_paths import get_config_file_path

            cache_file = get_config_file_path("global_config.config")
            success = _sync_save_config(config, cache_file)

            if success:
                logger.info("Global config saved to cache for session persistence")
            else:
                logger.error("Failed to save global config to cache - sync save returned False")
        except Exception as e:
            logger.error(f"Failed to save global config to cache: {e}")
            # Don't show error dialog as this is not critical for immediate functionality

    async def action_compile_plate(self):
        """Handle Compile Plate button - compile pipelines for selected plates."""
        selected_items = self.get_selected_plates()

        if not selected_items:
            logger.warning("No plates available for compilation")
            return

        # Unified validation using functional validator
        invalid_plates = self._validate_plates_for_operation(selected_items, 'compile')

        # Let validation failures bubble up as status messages
        if invalid_plates:
            invalid_names = [p['name'] for p in invalid_plates]
            self.status_message.emit(f"Cannot compile invalid plates: {', '.join(invalid_names)}")
            return

        # Start async compilation
        await self._compile_plates_worker(selected_items)

    async def _compile_plates_worker(self, selected_items: List[Dict]) -> None:
        """Background worker for plate compilation."""
        # CRITICAL: Set up global context in worker thread
        # The service adapter runs this entire function in a worker thread,
        # so we need to establish the global context here
        from openhcs.config_framework.lazy_factory import ensure_global_config_context
        from openhcs.core.config import GlobalPipelineConfig
        ensure_global_config_context(GlobalPipelineConfig, self.global_config)

        # Use signals for thread-safe UI updates
        self.progress_started.emit(len(selected_items))

        for i, plate_data in enumerate(selected_items):
            plate_path = plate_data['path']

            # Get definition pipeline - this is the ORIGINAL pipeline from the editor
            # It should have func attributes intact
            definition_pipeline = self._get_current_pipeline_definition(plate_path)
            if not definition_pipeline:
                logger.warning(f"No pipeline defined for {plate_data['name']}, using empty pipeline")
                definition_pipeline = []

            # Validate that steps have func attribute (required for ZMQ execution)
            for i, step in enumerate(definition_pipeline):
                if not hasattr(step, 'func'):
                    logger.error(f"Step {i} ({step.name}) missing 'func' attribute! Cannot execute via ZMQ.")
                    raise AttributeError(f"Step '{step.name}' is missing 'func' attribute. "
                                       "This usually means the pipeline was loaded from a compiled state instead of the original definition.")

            try:
                # Get or create orchestrator for compilation
                if plate_path in self.orchestrators:
                    orchestrator = self.orchestrators[plate_path]
                    if not orchestrator.is_initialized():
                        # Only run heavy initialization in worker thread
                        # Need to set up context in worker thread too since initialize() runs there
                        def initialize_with_context():
                            from openhcs.config_framework.lazy_factory import ensure_global_config_context
                            from openhcs.core.config import GlobalPipelineConfig
                            ensure_global_config_context(GlobalPipelineConfig, self.global_config)
                            return orchestrator.initialize()

                        import asyncio
                        loop = asyncio.get_event_loop()
                        await loop.run_in_executor(None, initialize_with_context)
                else:
                    # Create orchestrator in main thread (has access to global context)
                    orchestrator = PipelineOrchestrator(
                        plate_path=plate_path,
                        storage_registry=self.file_manager.registry
                    )
                    # Only run heavy initialization in worker thread
                    # Need to set up context in worker thread too since initialize() runs there
                    def initialize_with_context():
                        from openhcs.config_framework.lazy_factory import ensure_global_config_context
                        from openhcs.core.config import GlobalPipelineConfig
                        ensure_global_config_context(GlobalPipelineConfig, self.global_config)
                        return orchestrator.initialize()

                    import asyncio
                    loop = asyncio.get_event_loop()
                    await loop.run_in_executor(None, initialize_with_context)
                    self.orchestrators[plate_path] = orchestrator
                self.orchestrators[plate_path] = orchestrator

                # Make fresh copy for compilation
                execution_pipeline = copy.deepcopy(definition_pipeline)

                # Fix step IDs after deep copy to match new object IDs
                for step in execution_pipeline:
                    step.step_id = str(id(step))
                    # Ensure variable_components is never None - use FunctionStep default
                    if step.variable_components is None:
                        logger.warning(f"Step '{step.name}' has None variable_components, setting FunctionStep default")
                        step.variable_components = [VariableComponents.SITE]
                    # Also ensure it's not an empty list
                    elif not step.variable_components:
                        logger.warning(f"Step '{step.name}' has empty variable_components, setting FunctionStep default")
                        step.variable_components = [VariableComponents.SITE]

                # Get wells and compile (async - run in executor to avoid blocking UI)
                # Wrap in Pipeline object like test_main.py does
                pipeline_obj = Pipeline(steps=execution_pipeline)

                # Run heavy operations in executor to avoid blocking UI (works in Qt thread)
                import asyncio
                loop = asyncio.get_event_loop()
                # Get wells using multiprocessing axis (WELL in default config)
                from openhcs.constants import MULTIPROCESSING_AXIS
                wells = await loop.run_in_executor(None, lambda: orchestrator.get_component_keys(MULTIPROCESSING_AXIS))

                # Wrap compilation with context setup for worker thread
                def compile_with_context():
                    from openhcs.config_framework.lazy_factory import ensure_global_config_context
                    from openhcs.core.config import GlobalPipelineConfig
                    ensure_global_config_context(GlobalPipelineConfig, self.global_config)
                    return orchestrator.compile_pipelines(pipeline_obj.steps, wells)

                compilation_result = await loop.run_in_executor(None, compile_with_context)

                # Extract compiled_contexts from the dict returned by compile_pipelines
                # compile_pipelines now returns {'pipeline_definition': ..., 'compiled_contexts': ...}
                compiled_contexts = compilation_result['compiled_contexts']

                # Store compiled data AND original definition pipeline
                # ZMQ mode needs the original definition, direct mode needs the compiled execution pipeline
                self.plate_compiled_data[plate_path] = {
                    'definition_pipeline': definition_pipeline,  # Original uncompiled pipeline for ZMQ
                    'execution_pipeline': execution_pipeline,    # Compiled pipeline for direct mode
                    'compiled_contexts': compiled_contexts
                }
                logger.info(f"Successfully compiled {plate_path}")

                # Update orchestrator state change signal
                self.orchestrator_state_changed.emit(plate_path, "COMPILED")

            except Exception as e:
                logger.error(f"COMPILATION ERROR: Pipeline compilation failed for {plate_path}: {e}", exc_info=True)
                plate_data['error'] = str(e)
                # Don't store anything in plate_compiled_data on failure
                self.orchestrator_state_changed.emit(plate_path, "COMPILE_FAILED")
                # Use signal for thread-safe error reporting instead of direct dialog call
                self.compilation_error.emit(plate_data['name'], str(e))

            # Use signal for thread-safe progress update
            self.progress_updated.emit(i + 1)

        # Use signal for thread-safe progress completion
        self.progress_finished.emit()
        self.status_message.emit(f"Compilation completed for {len(selected_items)} plate(s)")
        self.update_button_states()
    
    async def action_run_plate(self):
        """Handle Run Plate button - execute compiled plates."""
        selected_items = self.get_selected_plates()
        if not selected_items:
            self.service_adapter.show_error_dialog("No plates selected to run.")
            return

        ready_items = [item for item in selected_items if item.get('path') in self.plate_compiled_data]
        if not ready_items:
            self.service_adapter.show_error_dialog("Selected plates are not compiled. Please compile first.")
            return

        # Check if ZMQ execution is enabled (default: True)
        import os
        use_zmq = os.environ.get('OPENHCS_USE_ZMQ_EXECUTION', 'true').lower() in ('true', '1', 'yes')

        if use_zmq:
            await self._run_plates_zmq(ready_items)
        else:
            await self._run_plates_subprocess(ready_items)

    async def _run_plates_subprocess(self, ready_items):
        """Run plates using legacy subprocess runner (deprecated)."""
        import warnings
        warnings.warn(
            "Subprocess runner is deprecated. Set OPENHCS_USE_ZMQ_EXECUTION=true to use ZMQ execution.",
            DeprecationWarning,
            stacklevel=2
        )

        try:
            # Use subprocess approach like Textual TUI
            logger.debug("Using subprocess approach for clean isolation")

            plate_paths_to_run = [item['path'] for item in ready_items]

            # Pass both pipeline definition and pre-compiled contexts to subprocess
            pipeline_data = {}
            effective_configs = {}
            for plate_path in plate_paths_to_run:
                compiled_data = self.plate_compiled_data[plate_path]
                pipeline_data[plate_path] = {
                    'pipeline_definition': compiled_data['execution_pipeline'],  # Use execution pipeline (stripped)
                    'compiled_contexts': compiled_data['compiled_contexts']      # Pre-compiled contexts
                }

                # Get effective config for this plate (includes pipeline config if set)
                # For subprocess execution, we need the merged config since subprocess doesn't use dual-axis resolver
                if plate_path in self.orchestrators:
                    # Get merged config from orchestrator (this resolves lazy values)
                    effective_configs[plate_path] = self.orchestrators[plate_path].get_effective_config()
                else:
                    effective_configs[plate_path] = self.global_config

            logger.info(f"Starting subprocess for {len(plate_paths_to_run)} plates")

            # Clear subprocess logs before starting new execution
            self.clear_subprocess_logs.emit()

            # Create data file for subprocess
            data_file = tempfile.NamedTemporaryFile(mode='wb', delete=False, suffix='.pkl')

            # Generate unique ID for this subprocess
            import time
            subprocess_timestamp = int(time.time())
            plate_names = [Path(path).name for path in plate_paths_to_run]
            unique_id = f"plates_{'_'.join(plate_names[:2])}_{subprocess_timestamp}"

            # Build subprocess log name using log utilities
            from openhcs.core.log_utils import get_current_log_file_path
            try:
                tui_log_path = get_current_log_file_path()
                if tui_log_path.endswith('.log'):
                    tui_base = tui_log_path[:-4]  # Remove .log extension
                else:
                    tui_base = tui_log_path
                log_file_base = f"{tui_base}_subprocess_{subprocess_timestamp}"
            except RuntimeError:
                # Fallback if no main log found
                log_dir = Path.home() / ".local" / "share" / "openhcs" / "logs"
                log_dir.mkdir(parents=True, exist_ok=True)
                log_file_base = str(log_dir / f"pyqt_gui_subprocess_{subprocess_timestamp}")

            # Pickle data for subprocess
            subprocess_data = {
                'plate_paths': plate_paths_to_run,
                'pipeline_data': pipeline_data,
                'global_config': self.global_config,      # Fallback global config
                'effective_configs': effective_configs    # Per-plate effective configs (includes pipeline config)
            }

            # Resolve all lazy configurations to concrete values before pickling
            from openhcs.config_framework.lazy_factory import resolve_lazy_configurations_for_serialization
            resolved_subprocess_data = resolve_lazy_configurations_for_serialization(subprocess_data)

            # Write pickle data
            def _write_pickle_data():
                import dill as pickle
                with open(data_file.name, 'wb') as f:
                    pickle.dump(resolved_subprocess_data, f)
                data_file.close()

            # Write pickle data in executor (works in Qt thread)
            import asyncio
            loop = asyncio.get_event_loop()
            await loop.run_in_executor(None, _write_pickle_data)

            logger.debug(f"Created data file: {data_file.name}")

            # Create subprocess
            subprocess_script = Path(__file__).parent.parent.parent / "textual_tui" / "subprocess_runner.py"

            # Generate actual log file path that subprocess will create
            actual_log_file_path = f"{log_file_base}_{unique_id}.log"
            logger.debug(f"Log file base: {log_file_base}")
            logger.debug(f"Unique ID: {unique_id}")
            logger.debug(f"Actual log file: {actual_log_file_path}")

            # Store log file path for monitoring
            self.log_file_path = actual_log_file_path
            self.log_file_position = 0

            logger.debug(f"Subprocess command: {sys.executable} {subprocess_script} {data_file.name} {log_file_base} {unique_id}")

            # Create subprocess
            def _create_subprocess():
                return subprocess.Popen([
                    sys.executable, str(subprocess_script),
                    data_file.name, log_file_base, unique_id
                ],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                text=True,
                )

            # Create subprocess in executor (works in Qt thread)
            import asyncio
            loop = asyncio.get_event_loop()
            self.current_process = await loop.run_in_executor(None, _create_subprocess)

            logger.info(f"Subprocess started with PID: {self.current_process.pid}")

            # Emit signal for log viewer to start monitoring
            self.subprocess_log_started.emit(log_file_base)

            # Update orchestrator states to show running state
            for plate in ready_items:
                plate_path = plate['path']
                if plate_path in self.orchestrators:
                    self.orchestrators[plate_path]._state = OrchestratorState.EXECUTING

            self.execution_state = "running"
            self.status_message.emit(f"Running {len(ready_items)} plate(s) in subprocess...")
            self.update_button_states()

            # Start monitoring
            await self._start_monitoring()

        except Exception as e:
            logger.error(f"Failed to start plate execution: {e}", exc_info=True)
            self.service_adapter.show_error_dialog(f"Failed to start execution: {e}")
            self.execution_state = "idle"
            self.update_button_states()
    
    async def _run_plates_zmq(self, ready_items):
        """Run plates using ZMQ execution client (recommended)."""
        try:
            from openhcs.runtime.zmq_execution_client import ZMQExecutionClient

            plate_paths_to_run = [item['path'] for item in ready_items]
            logger.info(f"Starting ZMQ execution for {len(plate_paths_to_run)} plates")

            # Clear subprocess logs before starting new execution
            self.clear_subprocess_logs.emit()

            # Create ZMQ client (persistent mode - server stays alive like Napari)
            self.zmq_client = ZMQExecutionClient(
                port=7777,
                persistent=True,  # Server persists across executions
                progress_callback=self._on_zmq_progress
            )

            # Connect to server (will spawn if needed)
            def _connect():
                return self.zmq_client.connect(timeout=15)

            import asyncio
            loop = asyncio.get_event_loop()
            connected = await loop.run_in_executor(None, _connect)

            if not connected:
                raise RuntimeError("Failed to connect to ZMQ execution server")

            logger.info("Connected to ZMQ execution server")

            # Update orchestrator states to show running state
            for plate in ready_items:
                plate_path = plate['path']
                if plate_path in self.orchestrators:
                    self.orchestrators[plate_path]._state = OrchestratorState.EXECUTING
                    self.orchestrator_state_changed.emit(plate_path, OrchestratorState.EXECUTING.value)

            self.execution_state = "running"
            self.status_message.emit(f"Running {len(ready_items)} plate(s) via ZMQ...")
            self.update_button_states()

            # Execute each plate
            for plate_path in plate_paths_to_run:
                compiled_data = self.plate_compiled_data[plate_path]

                # Use DEFINITION pipeline for ZMQ (server will compile)
                # NOT the execution_pipeline (which is already compiled)
                definition_pipeline = compiled_data['definition_pipeline']

                # Get config for this plate
                # CRITICAL: Send GlobalPipelineConfig (concrete) and PipelineConfig (lazy overrides) separately
                # The server will merge them via the dual-axis resolver
                if plate_path in self.orchestrators:
                    # Send the global config (concrete values) + pipeline config (lazy overrides)
                    global_config_to_send = self.global_config
                    pipeline_config = self.orchestrators[plate_path].pipeline_config
                else:
                    # No orchestrator - send global config with empty pipeline config
                    global_config_to_send = self.global_config
                    from openhcs.core.config import PipelineConfig
                    pipeline_config = PipelineConfig()

                logger.info(f"Executing plate: {plate_path}")

                # Execute via ZMQ (in executor to avoid blocking UI)
                # Send original definition pipeline - server will compile it
                def _execute():
                    return self.zmq_client.execute_pipeline(
                        plate_id=str(plate_path),
                        pipeline_steps=definition_pipeline,
                        global_config=global_config_to_send,
                        pipeline_config=pipeline_config
                    )

                response = await loop.run_in_executor(None, _execute)

                # Track execution ID for cancellation
                if response.get('execution_id'):
                    self.current_execution_id = response['execution_id']

                logger.info(f"Plate {plate_path} execution response: {response.get('status')}")

                # Handle different response statuses
                status = response.get('status')
                if status == 'cancelled':
                    # Cancellation is expected, not an error - just log it
                    logger.info(f"Plate {plate_path} execution was cancelled")
                    self.status_message.emit(f"Execution cancelled for {plate_path}")
                elif status != 'complete':
                    # Actual error - show error dialog
                    error_msg = response.get('message', 'Unknown error')
                    logger.error(f"Plate {plate_path} execution failed: {error_msg}")
                    self.service_adapter.show_error_dialog(f"Execution failed for {plate_path}: {error_msg}")

            # Execution complete
            self.execution_state = "idle"
            self.current_execution_id = None
            self.status_message.emit(f"Completed {len(ready_items)} plate(s)")

            # Update orchestrator states
            for plate in ready_items:
                plate_path = plate['path']
                if plate_path in self.orchestrators:
                    self.orchestrators[plate_path]._state = OrchestratorState.COMPLETED
                    self.orchestrator_state_changed.emit(plate_path, OrchestratorState.COMPLETED.value)

            self.update_button_states()

            # Disconnect from server
            def _disconnect():
                self.zmq_client.disconnect()

            await loop.run_in_executor(None, _disconnect)
            self.zmq_client = None

        except Exception as e:
            logger.error(f"Failed to execute plates via ZMQ: {e}", exc_info=True)
            # Use signal for thread-safe error reporting
            self.execution_error.emit(f"Failed to execute: {e}")
            self.execution_state = "idle"
            self.current_execution_id = None
            self.update_button_states()

            # Cleanup ZMQ client
            if hasattr(self, 'zmq_client') and self.zmq_client:
                try:
                    self.zmq_client.disconnect()
                except:
                    pass
                self.zmq_client = None

    def _on_zmq_progress(self, message):
        """
        Handle progress updates from ZMQ execution server.

        This is called from the progress listener thread (background thread),
        so we must use QMetaObject.invokeMethod to safely emit signals from the main thread.
        """
        try:
            well_id = message.get('well_id', 'unknown')
            step = message.get('step', 'unknown')
            status = message.get('status', 'unknown')

            # Emit progress message to UI (thread-safe)
            progress_text = f"[{well_id}] {step}: {status}"

            # Use QMetaObject.invokeMethod to emit signal from main thread
            from PyQt6.QtCore import QMetaObject, Qt
            QMetaObject.invokeMethod(
                self,
                "_emit_status_message",
                Qt.ConnectionType.QueuedConnection,
                progress_text
            )

            logger.debug(f"Progress: {progress_text}")

        except Exception as e:
            logger.warning(f"Failed to handle progress update: {e}")

    @pyqtSlot(str)
    def _emit_status_message(self, message: str):
        """Emit status message from main thread (called via QMetaObject.invokeMethod)."""
        self.status_message.emit(message)

    async def action_stop_execution(self):
        """Handle Stop Execution - cancel ZMQ execution or terminate subprocess."""
        logger.info("🛑 Stop button pressed.")
        self.status_message.emit("Terminating execution...")

        # Check if using ZMQ execution
        if self.zmq_client:
            try:
                logger.info("🛑 Requesting graceful cancellation via ZMQ...")

                import asyncio
                loop = asyncio.get_event_loop()

                # Cancel specific execution if we have an ID
                if self.current_execution_id:
                    logger.info(f"🛑 Cancelling execution {self.current_execution_id}")

                    def _cancel():
                        return self.zmq_client.cancel_execution(self.current_execution_id)

                    response = await loop.run_in_executor(None, _cancel)

                    if response.get('status') == 'ok':
                        logger.info("🛑 Cancellation request accepted, waiting for graceful shutdown...")
                        self.status_message.emit("Cancellation requested, waiting...")

                        # Wait for graceful cancellation with timeout
                        timeout = 5  # seconds
                        start_time = asyncio.get_event_loop().time()

                        while (asyncio.get_event_loop().time() - start_time) < timeout:
                            # Check if execution is still running
                            def _check_status():
                                return self.zmq_client.get_status(self.current_execution_id)

                            status_response = await loop.run_in_executor(None, _check_status)

                            if status_response.get('status') == 'error':
                                # Execution no longer exists (completed or cancelled)
                                logger.info("🛑 Execution completed/cancelled gracefully")
                                break

                            await asyncio.sleep(0.5)
                        else:
                            # Timeout reached - execution still running
                            logger.warning("🛑 Graceful cancellation timeout - execution may still be running")
                            self.status_message.emit("Cancellation timeout - execution may still be running")
                    else:
                        logger.warning(f"🛑 Cancellation failed: {response.get('message')}")
                        self.status_message.emit(f"Cancellation failed: {response.get('message')}")

                # Disconnect client
                def _disconnect():
                    self.zmq_client.disconnect()

                await loop.run_in_executor(None, _disconnect)

                self.zmq_client = None
                self.current_execution_id = None
                self.execution_state = "idle"

                # Update orchestrator states
                for orchestrator in self.orchestrators.values():
                    if orchestrator.state == OrchestratorState.EXECUTING:
                        orchestrator._state = OrchestratorState.COMPILED

                self.status_message.emit("Execution cancelled by user")
                self.update_button_states()

            except Exception as e:
                logger.error(f"🛑 Error cancelling ZMQ execution: {e}")
                self.service_adapter.show_error_dialog(f"Failed to cancel execution: {e}")

        elif self.current_process and self.current_process.poll() is None:  # Still running subprocess
            try:
                # Kill the entire process group, not just the parent process (matches TUI)
                # The subprocess creates its own process group, so we need to kill that group
                logger.info(f"🛑 Killing process group for PID {self.current_process.pid}...")

                # Get the process group ID (should be same as PID since subprocess calls os.setpgrp())
                process_group_id = self.current_process.pid

                # Kill entire process group (negative PID kills process group)
                import os
                import signal
                os.killpg(process_group_id, signal.SIGTERM)

                # Give processes time to exit gracefully
                import asyncio
                await asyncio.sleep(1)

                # Force kill if still alive
                try:
                    os.killpg(process_group_id, signal.SIGKILL)
                    logger.info(f"🛑 Force killed process group {process_group_id}")
                except ProcessLookupError:
                    logger.info(f"🛑 Process group {process_group_id} already terminated")

                # Reset execution state
                self.execution_state = "idle"
                self.current_process = None

                # Update orchestrator states
                for orchestrator in self.orchestrators.values():
                    if orchestrator.state == OrchestratorState.EXECUTING:
                        orchestrator._state = OrchestratorState.COMPILED

                self.status_message.emit("Execution terminated by user")
                self.update_button_states()

                # Emit signal for log viewer
                self.subprocess_log_stopped.emit()

            except Exception as e:
                logger.warning(f"🛑 Error killing process group: {e}, falling back to single process kill")
                # Fallback to killing just the main process (original behavior)
                self.current_process.terminate()
                try:
                    self.current_process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    self.current_process.kill()
                    self.current_process.wait()

                # Reset state even on fallback
                self.execution_state = "idle"
                self.current_process = None
                self.status_message.emit("Execution terminated by user")
                self.update_button_states()
                self.subprocess_log_stopped.emit()
        else:
            self.service_adapter.show_info_dialog("No execution is currently running.")
    
    def action_code_plate(self):
        """Generate Python code for selected plates and their pipelines (Tier 3)."""
        logger.debug("Code button pressed - generating Python code for plates")

        selected_items = self.get_selected_plates()
        if not selected_items:
            self.service_adapter.show_error_dialog("No plates selected for code generation")
            return

        try:
            # Collect plate paths, pipeline data, and per-plate pipeline configs
            plate_paths = []
            pipeline_data = {}
            per_plate_configs = {}  # Store pipeline config for each plate

            for plate_data in selected_items:
                plate_path = plate_data['path']
                plate_paths.append(plate_path)

                # Get pipeline definition for this plate
                definition_pipeline = self._get_current_pipeline_definition(plate_path)
                if not definition_pipeline:
                    logger.warning(f"No pipeline defined for {plate_data['name']}, using empty pipeline")
                    definition_pipeline = []

                pipeline_data[plate_path] = definition_pipeline

                # Get the actual pipeline config from this plate's orchestrator
                if plate_path in self.orchestrators:
                    orchestrator = self.orchestrators[plate_path]
                    if orchestrator.pipeline_config:
                        per_plate_configs[plate_path] = orchestrator.pipeline_config

            # Generate complete orchestrator code using new per_plate_configs parameter
            from openhcs.debug.pickle_to_python import generate_complete_orchestrator_code

            python_code = generate_complete_orchestrator_code(
                plate_paths=plate_paths,
                pipeline_data=pipeline_data,
                global_config=self.global_config,
                per_plate_configs=per_plate_configs if per_plate_configs else None,
                clean_mode=True  # Default to clean mode - only show non-default values
            )

            # Create simple code editor service (same pattern as tiers 1 & 2)
            from openhcs.pyqt_gui.services.simple_code_editor import SimpleCodeEditorService
            editor_service = SimpleCodeEditorService(self)

            # Check if user wants external editor (check environment variable)
            import os
            use_external = os.environ.get('OPENHCS_USE_EXTERNAL_EDITOR', '').lower() in ('1', 'true', 'yes')

            # Prepare code data for clean mode toggle
            code_data = {
                'clean_mode': True,
                'plate_paths': plate_paths,
                'pipeline_data': pipeline_data,
                'global_config': self.global_config,
                'per_plate_configs': per_plate_configs
            }

            # Launch editor with callback
            editor_service.edit_code(
                initial_content=python_code,
                title="Edit Orchestrator Configuration",
                callback=self._handle_edited_orchestrator_code,
                use_external=use_external,
                code_type='orchestrator',
                code_data=code_data
            )

        except Exception as e:
            logger.error(f"Failed to generate plate code: {e}")
            self.service_adapter.show_error_dialog(f"Failed to generate code: {str(e)}")

    def _patch_lazy_constructors(self):
        """Context manager that patches lazy dataclass constructors to preserve None vs concrete distinction."""
        from contextlib import contextmanager
        from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
        import dataclasses

        @contextmanager
        def patch_context():
            # Store original constructors
            original_constructors = {}

            # Find all lazy dataclass types that need patching
            from openhcs.core.config import LazyZarrConfig, LazyStepMaterializationConfig, LazyWellFilterConfig
            lazy_types = [LazyZarrConfig, LazyStepMaterializationConfig, LazyWellFilterConfig]

            # Add any other lazy types that might be used
            for lazy_type in lazy_types:
                if LazyDefaultPlaceholderService.has_lazy_resolution(lazy_type):
                    # Store original constructor
                    original_constructors[lazy_type] = lazy_type.__init__

                    # Create patched constructor that uses raw values
                    def create_patched_init(original_init, dataclass_type):
                        def patched_init(self, **kwargs):
                            # Use raw value approach instead of calling original constructor
                            # This prevents lazy resolution during code execution
                            for field in dataclasses.fields(dataclass_type):
                                value = kwargs.get(field.name, None)
                                object.__setattr__(self, field.name, value)

                            # Initialize any required lazy dataclass attributes
                            if hasattr(dataclass_type, '_is_lazy_dataclass'):
                                object.__setattr__(self, '_is_lazy_dataclass', True)

                        return patched_init

                    # Apply the patch
                    lazy_type.__init__ = create_patched_init(original_constructors[lazy_type], lazy_type)

            try:
                yield
            finally:
                # Restore original constructors
                for lazy_type, original_init in original_constructors.items():
                    lazy_type.__init__ = original_init

        return patch_context()

    def _handle_edited_orchestrator_code(self, edited_code: str):
        """Handle edited orchestrator code and update UI state (same logic as Textual TUI)."""
        logger.debug("Orchestrator code edited, processing changes...")
        try:
            # CRITICAL FIX: Execute code with lazy dataclass constructor patching to preserve None vs concrete distinction
            namespace = {}
            with self._patch_lazy_constructors():
                exec(edited_code, namespace)

            # Extract variables from executed code (same logic as Textual TUI)
            if 'plate_paths' in namespace and 'pipeline_data' in namespace:
                new_plate_paths = namespace['plate_paths']
                new_pipeline_data = namespace['pipeline_data']

                # Update global config if present
                if 'global_config' in namespace:
                    new_global_config = namespace['global_config']
                    # Update the global config (trigger UI refresh)
                    self.global_config = new_global_config

                    # CRITICAL: Apply new global config to all orchestrators (was missing!)
                    # This ensures orchestrators use the updated global config from tier 3 edits
                    for orchestrator in self.orchestrators.values():
                        self._update_orchestrator_global_config(orchestrator, new_global_config)

                    # SIMPLIFIED: Update service adapter (dual-axis resolver handles context)
                    self.service_adapter.set_global_config(new_global_config)

                    self.global_config_changed.emit()

                # Handle per-plate configs (preferred) or single pipeline_config (legacy)
                if 'per_plate_configs' in namespace:
                    # New per-plate config system
                    per_plate_configs = namespace['per_plate_configs']

                    # CRITICAL FIX: Match string keys to actual plate path objects
                    # The keys in per_plate_configs are strings, but orchestrators dict uses Path/str objects
                    for plate_path_str, new_pipeline_config in per_plate_configs.items():
                        # Find matching orchestrator by comparing string representations
                        matched_orchestrator = None
                        for orch_key, orchestrator in self.orchestrators.items():
                            if str(orch_key) == str(plate_path_str):
                                matched_orchestrator = orchestrator
                                matched_key = orch_key
                                break

                        if matched_orchestrator:
                            matched_orchestrator.apply_pipeline_config(new_pipeline_config)
                            # Emit signal for UI components to refresh (including config windows)
                            effective_config = matched_orchestrator.get_effective_config()
                            self.orchestrator_config_changed.emit(str(matched_key), effective_config)
                            logger.debug(f"Applied per-plate pipeline config to orchestrator: {matched_key}")
                        else:
                            logger.warning(f"No orchestrator found for plate path: {plate_path_str}")
                elif 'pipeline_config' in namespace:
                    # Legacy single pipeline_config for all plates
                    new_pipeline_config = namespace['pipeline_config']
                    # Apply the new pipeline config to all affected orchestrators
                    for plate_path in new_plate_paths:
                        if plate_path in self.orchestrators:
                            orchestrator = self.orchestrators[plate_path]
                            orchestrator.apply_pipeline_config(new_pipeline_config)
                            # Emit signal for UI components to refresh (including config windows)
                            effective_config = orchestrator.get_effective_config()
                            self.orchestrator_config_changed.emit(str(plate_path), effective_config)
                            logger.debug(f"Applied tier 3 pipeline config to orchestrator: {plate_path}")

                # Update pipeline data for ALL affected plates with proper state invalidation
                if self.pipeline_editor and hasattr(self.pipeline_editor, 'plate_pipelines'):
                    current_plate = getattr(self.pipeline_editor, 'current_plate', None)

                    for plate_path, new_steps in new_pipeline_data.items():
                        # Update pipeline data in the pipeline editor
                        self.pipeline_editor.plate_pipelines[plate_path] = new_steps
                        logger.debug(f"Updated pipeline for {plate_path} with {len(new_steps)} steps")

                        # CRITICAL: Invalidate orchestrator state for ALL affected plates
                        self._invalidate_orchestrator_compilation_state(plate_path)

                        # If this is the currently displayed plate, trigger UI cascade
                        if plate_path == current_plate:
                            # Update the current pipeline steps to trigger cascade
                            self.pipeline_editor.pipeline_steps = new_steps
                            # Trigger UI refresh for the current plate
                            self.pipeline_editor.update_step_list()
                            # Emit pipeline changed signal to cascade to step editors
                            self.pipeline_editor.pipeline_changed.emit(new_steps)
                            logger.debug(f"Triggered UI cascade refresh for current plate: {plate_path}")
                else:
                    logger.warning("No pipeline editor available to update pipeline data")

                # Trigger UI refresh
                self.pipeline_data_changed.emit()
                self.service_adapter.show_info_dialog("Orchestrator configuration updated successfully")

            else:
                raise ValueError("No valid assignments found in edited code")

        except (SyntaxError, Exception) as e:
            import traceback
            full_traceback = traceback.format_exc()
            logger.error(f"Failed to parse edited orchestrator code: {e}\nFull traceback:\n{full_traceback}")
            # Re-raise so the code editor can handle it (keep dialog open, move cursor to error line)
            raise

    def _invalidate_orchestrator_compilation_state(self, plate_path: str):
        """Invalidate compilation state for an orchestrator when its pipeline changes.

        This ensures that tier 3 changes properly invalidate ALL affected orchestrators,
        not just the currently visible one.

        Args:
            plate_path: Path of the plate whose orchestrator state should be invalidated
        """
        # Clear compiled data from simple state
        if plate_path in self.plate_compiled_data:
            del self.plate_compiled_data[plate_path]
            logger.debug(f"Cleared compiled data for {plate_path}")

        # Reset orchestrator state to READY (initialized) if it was compiled
        orchestrator = self.orchestrators.get(plate_path)
        if orchestrator:
            from openhcs.constants.constants import OrchestratorState
            if orchestrator.state == OrchestratorState.COMPILED:
                orchestrator._state = OrchestratorState.READY
                logger.debug(f"Reset orchestrator state to READY for {plate_path}")

                # Emit state change signal for UI refresh
                self.orchestrator_state_changed.emit(plate_path, "READY")

        logger.debug(f"Invalidated compilation state for orchestrator: {plate_path}")

    def action_view_metadata(self):
        """View plate images and metadata in tabbed window. Opens one window per selected plate."""
        selected_items = self.get_selected_plates()

        if not selected_items:
            self.service_adapter.show_error_dialog("No plates selected.")
            return

        # Open plate viewer for each selected plate
        from openhcs.pyqt_gui.windows.plate_viewer_window import PlateViewerWindow

        for item in selected_items:
            plate_path = item['path']

            # Check if orchestrator is initialized
            if plate_path not in self.orchestrators:
                self.service_adapter.show_error_dialog(f"Plate must be initialized to view: {plate_path}")
                continue

            orchestrator = self.orchestrators[plate_path]

            try:
                # Create plate viewer window with tabs (Image Browser + Metadata)
                viewer = PlateViewerWindow(
                    orchestrator=orchestrator,
                    color_scheme=self.color_scheme,
                    parent=self
                )
                viewer.show()  # Use show() instead of exec() to allow multiple windows
            except Exception as e:
                logger.error(f"Failed to open plate viewer for {plate_path}: {e}", exc_info=True)
                self.service_adapter.show_error_dialog(f"Failed to open plate viewer: {str(e)}")

    # ========== UI Helper Methods ==========
    
    def update_plate_list(self):
        """Update the plate list widget using selection preservation mixin."""
        def format_plate_item(plate):
            """Format plate item for display."""
            display_text = f"{plate['name']} ({plate['path']})"

            # Add status indicators
            status_indicators = []
            if plate['path'] in self.orchestrators:
                orchestrator = self.orchestrators[plate['path']]
                if orchestrator.state == OrchestratorState.READY:
                    status_indicators.append("✓ Init")
                elif orchestrator.state == OrchestratorState.COMPILED:
                    status_indicators.append("✓ Compiled")
                elif orchestrator.state == OrchestratorState.EXECUTING:
                    status_indicators.append("🔄 Running")
                elif orchestrator.state == OrchestratorState.COMPLETED:
                    status_indicators.append("✅ Complete")
                elif orchestrator.state == OrchestratorState.COMPILE_FAILED:
                    status_indicators.append("❌ Compile Failed")
                elif orchestrator.state == OrchestratorState.EXEC_FAILED:
                    status_indicators.append("❌ Exec Failed")

            if status_indicators:
                display_text = f"[{', '.join(status_indicators)}] {display_text}"

            return display_text, plate

        def update_func():
            """Update function that clears and rebuilds the list."""
            self.plate_list.clear()

            for plate in self.plates:
                display_text, plate_data = format_plate_item(plate)
                item = QListWidgetItem(display_text)
                item.setData(Qt.ItemDataRole.UserRole, plate_data)

                # Add tooltip
                if plate['path'] in self.orchestrators:
                    orchestrator = self.orchestrators[plate['path']]
                    item.setToolTip(f"Status: {orchestrator.state.value}")

                self.plate_list.addItem(item)

            # Auto-select first plate if no selection and plates exist
            if self.plates and not self.selected_plate_path:
                self.plate_list.setCurrentRow(0)

        # Use utility to preserve selection during update
        preserve_selection_during_update(
            self.plate_list,
            lambda item_data: item_data['path'] if isinstance(item_data, dict) and 'path' in item_data else str(item_data),
            lambda: bool(self.orchestrators),
            update_func
        )
        self.update_button_states()
    
    def get_selected_plates(self) -> List[Dict]:
        """
        Get currently selected plates.

        Returns:
            List of selected plate dictionaries
        """
        selected_items = []
        for item in self.plate_list.selectedItems():
            plate_data = item.data(Qt.ItemDataRole.UserRole)
            if plate_data:
                selected_items.append(plate_data)
        return selected_items

    def get_selected_orchestrator(self):
        """
        Get the orchestrator for the currently selected plate.

        Returns:
            PipelineOrchestrator or None if no plate selected or not initialized
        """
        if self.selected_plate_path and self.selected_plate_path in self.orchestrators:
            return self.orchestrators[self.selected_plate_path]
        return None
    
    def update_button_states(self):
        """Update button enabled/disabled states based on selection."""
        selected_plates = self.get_selected_plates()
        has_selection = len(selected_plates) > 0
        has_initialized = any(plate['path'] in self.orchestrators for plate in selected_plates)
        has_compiled = any(plate['path'] in self.plate_compiled_data for plate in selected_plates)
        is_running = self.is_any_plate_running()

        # Update button states (logic extracted from Textual version)
        self.buttons["del_plate"].setEnabled(has_selection and not is_running)
        self.buttons["edit_config"].setEnabled(has_initialized and not is_running)
        self.buttons["init_plate"].setEnabled(has_selection and not is_running)
        self.buttons["compile_plate"].setEnabled(has_initialized and not is_running)
        self.buttons["code_plate"].setEnabled(has_initialized and not is_running)
        self.buttons["view_metadata"].setEnabled(has_initialized and not is_running)

        # Run button - enabled if plates are compiled or if currently running (for stop)
        if is_running:
            self.buttons["run_plate"].setEnabled(True)
            self.buttons["run_plate"].setText("Stop")
        else:
            self.buttons["run_plate"].setEnabled(has_compiled)
            self.buttons["run_plate"].setText("Run")
    
    def is_any_plate_running(self) -> bool:
        """
        Check if any plate is currently running.
        
        Returns:
            True if any plate is running, False otherwise
        """
        return self.execution_state == "running"
    
    def update_status(self, message: str):
        """
        Update status label.
        
        Args:
            message: Status message to display
        """
        self.status_label.setText(message)
    
    def on_selection_changed(self):
        """Handle plate list selection changes using utility."""
        def on_selected(selected_plates):
            self.selected_plate_path = selected_plates[0]['path']
            self.plate_selected.emit(self.selected_plate_path)

            # SIMPLIFIED: Dual-axis resolver handles context discovery automatically
            if self.selected_plate_path in self.orchestrators:
                logger.debug(f"Selected orchestrator: {self.selected_plate_path}")

        def on_cleared():
            self.selected_plate_path = ""

        # Use utility to handle selection with prevention
        handle_selection_change_with_prevention(
            self.plate_list,
            self.get_selected_plates,
            lambda item_data: item_data['path'] if isinstance(item_data, dict) and 'path' in item_data else str(item_data),
            lambda: bool(self.orchestrators),
            lambda: self.selected_plate_path,
            on_selected,
            on_cleared
        )

        self.update_button_states()





    def on_item_double_clicked(self, item: QListWidgetItem):
        """Handle double-click on plate item."""
        plate_data = item.data(Qt.ItemDataRole.UserRole)
        if plate_data:
            # Double-click could trigger initialization or configuration
            if plate_data['path'] not in self.orchestrators:
                self.run_async_action(self.action_init_plate)
    
    def on_orchestrator_state_changed(self, plate_path: str, state: str):
        """
        Handle orchestrator state changes.
        
        Args:
            plate_path: Path of the plate
            state: New orchestrator state
        """
        self.update_plate_list()
        logger.debug(f"Orchestrator state changed: {plate_path} -> {state}")
    
    def on_config_changed(self, new_config: GlobalPipelineConfig):
        """
        Handle global configuration changes.

        Args:
            new_config: New global configuration
        """
        self.global_config = new_config

        # Apply new global config to all existing orchestrators
        # This rebuilds their pipeline configs preserving concrete values
        for orchestrator in self.orchestrators.values():
            self._update_orchestrator_global_config(orchestrator, new_config)

        # REMOVED: Thread-local modification - dual-axis resolver handles orchestrator context automatically

        logger.info(f"Applied new global config to {len(self.orchestrators)} orchestrators")

        # SIMPLIFIED: Dual-axis resolver handles placeholder updates automatically

    # REMOVED: _refresh_all_parameter_form_placeholders and _refresh_widget_parameter_forms
    # SIMPLIFIED: Dual-axis resolver handles placeholder updates automatically

    # ========== Helper Methods ==========

    def _get_current_pipeline_definition(self, plate_path: str) -> List:
        """
        Get the current pipeline definition for a plate.

        Args:
            plate_path: Path to the plate

        Returns:
            List of pipeline steps or empty list if no pipeline
        """
        if not self.pipeline_editor:
            logger.warning("No pipeline editor reference - using empty pipeline")
            return []

        # Get pipeline for specific plate (same logic as Textual TUI)
        if hasattr(self.pipeline_editor, 'plate_pipelines') and plate_path in self.pipeline_editor.plate_pipelines:
            pipeline_steps = self.pipeline_editor.plate_pipelines[plate_path]
            logger.debug(f"Found pipeline for plate {plate_path} with {len(pipeline_steps)} steps")
            return pipeline_steps
        else:
            logger.debug(f"No pipeline found for plate {plate_path}, using empty pipeline")
            return []

    def set_pipeline_editor(self, pipeline_editor):
        """
        Set the pipeline editor reference.

        Args:
            pipeline_editor: Pipeline editor widget instance
        """
        self.pipeline_editor = pipeline_editor
        logger.debug("Pipeline editor reference set in plate manager")

    async def _start_monitoring(self):
        """Start monitoring subprocess execution."""
        if not self.current_process:
            return

        # Simple monitoring - check if process is still running
        def check_process():
            if self.current_process and self.current_process.poll() is not None:
                # Process has finished
                return_code = self.current_process.returncode
                logger.info(f"Subprocess finished with return code: {return_code}")

                # Reset execution state
                self.execution_state = "idle"
                self.current_process = None

                # Update orchestrator states based on return code
                for orchestrator in self.orchestrators.values():
                    if orchestrator.state == OrchestratorState.EXECUTING:
                        if return_code == 0:
                            orchestrator._state = OrchestratorState.COMPLETED
                        else:
                            orchestrator._state = OrchestratorState.EXEC_FAILED

                if return_code == 0:
                    self.status_message.emit("Execution completed successfully")
                else:
                    self.status_message.emit(f"Execution failed with code {return_code}")

                self.update_button_states()

                # Emit signal for log viewer
                self.subprocess_log_stopped.emit()

                return False  # Stop monitoring
            return True  # Continue monitoring

        # Monitor process in background
        while check_process():
            await asyncio.sleep(1)  # Check every second

    def _on_progress_started(self, max_value: int):
        """Handle progress started signal (main thread)."""
        self.progress_bar.setVisible(True)
        self.progress_bar.setMaximum(max_value)
        self.progress_bar.setValue(0)

    def _on_progress_updated(self, value: int):
        """Handle progress updated signal (main thread)."""
        self.progress_bar.setValue(value)

    def _on_progress_finished(self):
        """Handle progress finished signal (main thread)."""
        self.progress_bar.setVisible(False)

    def _handle_compilation_error(self, plate_name: str, error_message: str):
        """Handle compilation error on main thread (slot)."""
        self.service_adapter.show_error_dialog(f"Compilation failed for {plate_name}: {error_message}")

    def _handle_initialization_error(self, plate_name: str, error_message: str):
        """Handle initialization error on main thread (slot)."""
        self.service_adapter.show_error_dialog(f"Failed to initialize {plate_name}: {error_message}")

    def _handle_execution_error(self, error_message: str):
        """Handle execution error on main thread (slot)."""
        self.service_adapter.show_error_dialog(error_message)
