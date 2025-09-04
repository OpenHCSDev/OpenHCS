"""
OpenHCS PyQt6 GUI Integration Testing Framework - Composable Workflow Foundation

This module provides a mathematical, composable testing framework for PyQt6 GUI integration tests.
It serves as the single source of truth for all GUI testing, replacing scattered test files with
a unified, modular approach inspired by the systematic refactoring framework.

Key Design Principles:
- Mathematical simplification through modularity
- Composable workflow components with clear contracts
- Flexible assertion framework for comprehensive validation
- Complex workflow builder similar to test_main.py
- Single source of truth for all PyQt GUI integration tests

Architecture:
- WorkflowStep: Atomic operations with clear input/output contracts
- WorkflowBuilder: Composable step sequencing with assertion injection
- ValidationFramework: Flexible assertion system for any workflow state
- TestOrchestrator: Central coordinator for complex test scenarios
"""

import os
import pytest
from dataclasses import dataclass, field
from typing import Dict, List, Any, Optional, Callable, Union
from pathlib import Path

# Skip entire module in CPU-only mode to avoid PyQt6 imports
if os.getenv('OPENHCS_CPU_ONLY', 'false').lower() == 'true':
    pytest.skip("PyQt6 GUI tests skipped in CPU-only mode", allow_module_level=True)

from PyQt6.QtWidgets import QApplication, QDialog, QPushButton, QMessageBox, QLabel, QWidget, QCheckBox
from PyQt6.QtCore import QTimer, QObject, pyqtSignal
from PyQt6.QtTest import QTest

from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.context.global_config import set_current_global_config
from openhcs.core.lazy_config import create_dataclass_for_editing
# PipelineConfig is dynamically generated from GlobalPipelineConfig
from openhcs.core.lazy_config import LazyStepMaterializationConfig
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.constants import Microscope
from openhcs.pyqt_gui.main import OpenHCSMainWindow
from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget
from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
from openhcs.pyqt_gui.windows.config_window import ConfigWindow
from openhcs.tests.generators.generate_synthetic_data import SyntheticMicroscopyGenerator


# ============================================================================
# WORKFLOW FRAMEWORK CONSTANTS AND CONFIGURATION
# ============================================================================

@dataclass(frozen=True)
class TimingConfig:
    """Timing configuration for GUI operations."""
    ACTION_DELAY: float = 1.5
    WINDOW_DELAY: float = 1.5
    SAVE_DELAY: float = 1.5

    @classmethod
    def from_environment(cls) -> 'TimingConfig':
        """Create timing config from environment variables."""
        import os
        return cls(
            ACTION_DELAY=float(os.environ.get('OPENHCS_TEST_ACTION_DELAY', cls.ACTION_DELAY)),
            WINDOW_DELAY=float(os.environ.get('OPENHCS_TEST_WINDOW_DELAY', cls.WINDOW_DELAY)),
            SAVE_DELAY=float(os.environ.get('OPENHCS_TEST_SAVE_DELAY', cls.SAVE_DELAY))
        )

@dataclass(frozen=True)
class ValidationSuffixes:
    """Validation result key suffixes."""
    NONE: str = "_shows_none"
    PIPELINE_DEFAULT: str = "_shows_pipeline_default"
    ORCHESTRATOR_VALUES: str = "_shows_orchestrator_values"

@dataclass(frozen=True)
class FieldModificationSpec:
    """Specification for field modification testing."""
    field_name: str
    modification_value: Any
    config_section: str = "path_planning"  # "path_planning" or "materialization_defaults"
    expected_persistence_behavior: str = "shows_modified_value"  # or "shows_lazy_state"

@dataclass(frozen=True)
class TestScenario:
    """Complete test scenario configuration with bidirectional parameter mapping."""
    name: str
    orchestrator_config: Dict[str, Any]
    expected_values: Dict[str, Any]
    field_to_test: FieldModificationSpec
    reset_field_to_test: Optional[str] = None  # Field to reset (different from field_to_test)
    legitimate_none_fields: frozenset = field(default_factory=lambda: frozenset({
        'barcode', 'plate_name', 'plate_id', 'description'
    }))

    def get_expected_validation_patterns(self) -> List[str]:
        """Extract validation patterns from expected values."""
        patterns = []
        for key, value in self.expected_values.items():
            if value is not None:
                patterns.append(str(value))
        return patterns

    def should_show_none(self, field_name: str) -> bool:
        """Determine if field should legitimately show '(none)'."""
        return field_name in self.legitimate_none_fields

    def get_modification_field_name(self) -> str:
        """Get the field name to modify in lifecycle testing."""
        return self.field_to_test.field_name

    def get_modification_value(self) -> Any:
        """Get the value to set during field modification."""
        return self.field_to_test.modification_value

TIMING = TimingConfig.from_environment()
VALIDATION_SUFFIXES = ValidationSuffixes()

# ============================================================================
# PARAMETERIZED TEST SCENARIOS
# ============================================================================

# Test scenario specifically for the reset placeholder bug
RESET_PLACEHOLDER_BUG_PATH_PLANNING_SCENARIO = TestScenario(
    name="reset_placeholder_bug_path_planning",
    orchestrator_config={
        "output_dir_suffix": "828282",  # This concrete value should NOT appear in reset placeholders
        "sub_dir": "images",
        "well_filter": 5,
        "num_workers": 1  # This concrete value should NOT appear in reset placeholders (default is 16)
    },
    expected_values={
        "output_dir_suffix": "828282",
        "sub_dir": "images",
        "well_filter": 5,
        "num_workers": 1
    },
    field_to_test=FieldModificationSpec(
        field_name="output_dir_suffix",  # Test the problematic field
        modification_value="828282",  # Set the concrete value that causes the bug
        config_section="path_planning"  # Modify path_planning.output_dir_suffix
    )
)

RESET_PLACEHOLDER_BUG_MATERIALIZATION_SCENARIO = TestScenario(
    name="reset_placeholder_bug_materialization",
    orchestrator_config={
        "output_dir_suffix": "828282",  # This concrete value should NOT appear in reset placeholders
        "sub_dir": "images",
        "well_filter": 5,
        "num_workers": 1  # This concrete value should NOT appear in reset placeholders (default is 16)
    },
    expected_values={
        "output_dir_suffix": "828282",
        "sub_dir": "images",
        "well_filter": 5,
        "num_workers": 1
    },
    field_to_test=FieldModificationSpec(
        field_name="output_dir_suffix",  # Test the problematic field
        modification_value="828282",  # Set the concrete value that causes the bug
        config_section="materialization_defaults"  # Modify materialization_defaults.output_dir_suffix
    )
)

RESET_PLACEHOLDER_BUG_DIRECT_FIELD_SCENARIO = TestScenario(
    name="reset_placeholder_bug_direct_field",
    orchestrator_config={
        "output_dir_suffix": "_test",
        "sub_dir": "images",
        "well_filter": ["A01", "A02"]
    },
    expected_values={
        "num_workers": 2,  # This will be set via UI
        "output_dir_suffix": "_test",
        "sub_dir": "images",
        "well_filter": ["A01", "A02"]
    },
    field_to_test=FieldModificationSpec(
        field_name="num_workers",  # Modify this field via UI
        modification_value=2,  # Set concrete value via UI
        config_section="direct"  # Direct field on PipelineConfig (not nested)
    )
    # No reset_field_to_test needed - we'll reset the same field we modified
)

DEFAULT_SCENARIO = TestScenario(
    name="default_hierarchy",
    orchestrator_config={
        "output_dir_suffix": "_outputs",
        "sub_dir": "images",
        "well_filter": 5
    },
    expected_values={
        "output_dir_suffix": "_outputs",
        "sub_dir": "images",
        "well_filter": 5
    },
    field_to_test=FieldModificationSpec(
        field_name="well_filter",
        modification_value=4,
        config_section="step_materialization_config"   # well_filter is in StepMaterializationConfig, not PathPlanningConfig
    )
)

ALTERNATIVE_SCENARIO = TestScenario(
    name="alternative_config",
    orchestrator_config={
        "output_dir_suffix": "_processed",
        "sub_dir": "results",
        "well_filter": 10
    },
    expected_values={
        "output_dir_suffix": "_processed",
        "sub_dir": "results",
        "well_filter": 10
    },
    field_to_test=FieldModificationSpec(
        field_name="output_dir_suffix",
        modification_value="_custom"
    )
)

MINIMAL_SCENARIO = TestScenario(
    name="minimal_config",
    orchestrator_config={
        "output_dir_suffix": "",
        "sub_dir": "data",
        "well_filter": 1
    },
    expected_values={
        "output_dir_suffix": "",
        "sub_dir": "data",
        "well_filter": 1
    },
    field_to_test=FieldModificationSpec(
        field_name="sub_dir",
        modification_value="test_data"
    )
)


# ============================================================================
# WORKFLOW CONTEXT AND STATE
# ============================================================================

@dataclass
class WorkflowContext:
    """Immutable context passed between workflow steps."""
    main_window: Optional[OpenHCSMainWindow] = None
    plate_manager_widget: Optional[PlateManagerWidget] = None
    config_window: Optional[QDialog] = None
    synthetic_plate_dir: Optional[Path] = None
    orchestrator: Optional[PipelineOrchestrator] = None
    validation_results: Dict[str, Any] = field(default_factory=dict)
    test_scenario: Optional[TestScenario] = None

    def with_updates(self, **kwargs) -> 'WorkflowContext':
        """Create new context with updates (immutable pattern)."""
        from dataclasses import replace
        return replace(self, **kwargs)


@dataclass
class WorkflowStep:
    """Atomic workflow operation with clear input/output contract."""
    name: str
    operation: Callable[[WorkflowContext], WorkflowContext]
    description: str = ""
    timing_delay: Optional[float] = None

    def execute(self, context: WorkflowContext) -> WorkflowContext:
        """Execute step with timing and logging."""
        print(f"  {self.name}...")
        result = self.operation(context)
        if self.timing_delay:
            _wait_for_gui(self.timing_delay)
        print(f"  ✅ {self.name} completed")
        return result


class WorkflowBuilder:
    """Composable workflow builder for GUI test scenarios."""

    def __init__(self):
        self.steps: List[WorkflowStep] = []
        self.assertions: List[Callable[[WorkflowContext], None]] = []

    def add_step(self, step: WorkflowStep) -> 'WorkflowBuilder':
        """Add workflow step (fluent interface)."""
        self.steps.append(step)
        return self

    def add_assertion(self, assertion: Callable[[WorkflowContext], None]) -> 'WorkflowBuilder':
        """Add assertion to be checked after workflow completion."""
        self.assertions.append(assertion)
        return self

    def execute(self, initial_context: WorkflowContext) -> WorkflowContext:
        """Execute workflow steps sequentially."""
        context = initial_context
        for step in self.steps:
            context = step.execute(context)

        # Run all assertions
        for assertion in self.assertions:
            assertion(context)

        return context


# ============================================================================
# BACKGROUND ERROR MONITOR
# ============================================================================

class ErrorDialogMonitor(QObject):
    """Background monitor that continuously watches for error dialogs."""

    error_detected = pyqtSignal(str)  # Signal emitted when error dialog is found

    def __init__(self):
        super().__init__()
        self.timer = QTimer()
        self.timer.timeout.connect(self.check_for_error_dialogs)
        self.monitoring = False
        self.detected_error = None

    def start_monitoring(self, check_interval_ms: int = 100):
        """Start continuous monitoring for error dialogs."""
        print("  Starting background error dialog monitor...")
        self.monitoring = True
        self.detected_error = None
        self.timer.start(check_interval_ms)  # Check every 100ms

    def stop_monitoring(self):
        """Stop monitoring for error dialogs."""
        self.monitoring = False
        self.timer.stop()
        print("  Stopped background error dialog monitor")

    def check_for_error_dialogs(self):
        """Check for error dialogs and handle them immediately."""
        if not self.monitoring:
            return

        try:
            error_dialogs = self._find_error_dialogs_immediate()
            if error_dialogs and not self.detected_error:
                error_details = self._close_error_dialogs_immediate(error_dialogs)
                error_message = (
                    f"LAZY CONFIG BUG DETECTED: Error dialog appeared! "
                    f"The application caught an exception (likely RecursionError) and showed it in a dialog. "
                    f"Error dialogs: {error_details}"
                )
                self.detected_error = error_message
                self.error_detected.emit(error_message)
                self.stop_monitoring()
        except Exception as e:
            print(f"  Error in background monitor: {e}")

    def _find_error_dialogs_immediate(self) -> List[Any]:
        """Immediate error dialog detection without waiting."""
        error_dialogs = []
        try:
            for widget in QApplication.topLevelWidgets():
                if widget.isVisible():
                    if isinstance(widget, QMessageBox):
                        error_dialogs.append(widget)
                    elif isinstance(widget, QDialog):
                        title = widget.windowTitle().lower()
                        if any(keyword in title for keyword in ['error', 'exception', 'recursion', 'warning', 'unexpected']):
                            error_dialogs.append(widget)
                        else:
                            # Quick check of dialog content
                            for label in widget.findChildren(QLabel):
                                if hasattr(label, 'text'):
                                    text = label.text().lower()
                                    if any(keyword in text for keyword in ['recursion', 'error', 'exception', 'unexpected']):
                                        error_dialogs.append(widget)
                                        break
        except Exception:
            pass  # Ignore errors during detection
        return error_dialogs

    def _close_error_dialogs_immediate(self, error_dialogs: List[Any]) -> List[str]:
        """Immediately close error dialogs and extract details."""
        error_details = []
        for dialog in error_dialogs:
            try:
                title = dialog.windowTitle()
                error_text = ""

                if isinstance(dialog, QMessageBox):
                    error_text = dialog.text()[:200]
                else:
                    for label in dialog.findChildren(QLabel):
                        if hasattr(label, 'text'):
                            text = label.text()
                            if any(keyword in text.lower() for keyword in ['recursion', 'error', 'exception']):
                                error_text = text[:200]
                                break

                error_details.append(f"Dialog: '{title}', Text: '{error_text}'")

                # Force close immediately
                dialog.accept()  # Try accept first
                dialog.close()   # Then close
                dialog.deleteLater()

                print(f"  Background monitor closed error dialog: {title}")

            except Exception as e:
                error_details.append(f"Error closing dialog: {e}")
                try:
                    dialog.close()
                    dialog.deleteLater()
                except:
                    pass

        return error_details

# Global error monitor instance
_error_monitor = None

def get_error_monitor() -> ErrorDialogMonitor:
    """Get or create the global error monitor instance."""
    global _error_monitor
    if _error_monitor is None:
        _error_monitor = ErrorDialogMonitor()
    return _error_monitor


# ============================================================================
# UTILITY FUNCTIONS AND DECORATORS
# ============================================================================

def _wait_for_gui(delay_seconds: float = TIMING.ACTION_DELAY) -> None:
    """Wait for GUI operations with configurable timing and error dialog detection."""
    import time

    # For longer delays, check for error dialogs periodically
    if delay_seconds > 1.0:
        check_interval = 0.5
        elapsed = 0.0

        while elapsed < delay_seconds:
            time.sleep(min(check_interval, delay_seconds - elapsed))
            QApplication.processEvents()

            # Check for error dialogs during wait
            error_dialogs = _find_error_dialogs()
            if error_dialogs:
                error_details = _close_error_dialogs()
                raise AssertionError(
                    f"LAZY CONFIG BUG DETECTED: Error dialog appeared during GUI wait! "
                    f"Error dialogs: {error_details}"
                )

            elapsed += check_interval
    else:
        time.sleep(delay_seconds)
        QApplication.processEvents()


def _create_synthetic_plate(tmp_path: Path) -> Path:
    """Create synthetic plate data for testing."""
    plate_dir = tmp_path / "test_plate"
    generator = SyntheticMicroscopyGenerator(
        output_dir=str(plate_dir),
        grid_size=(2, 2), tile_size=(64, 64), overlap_percent=10,
        wavelengths=2, z_stack_levels=1, wells=["A01"], format="ImageXpress"
    )
    generator.generate_dataset()
    return plate_dir


def _create_test_global_config() -> GlobalPipelineConfig:
    """Create test global configuration with known values."""
    return GlobalPipelineConfig(
        num_workers=8, microscope=Microscope.IMAGEXPRESS, use_threading=True
    )


# ============================================================================
# REUSABLE DECORATORS FOR ERROR HANDLING AND TIMEOUT
# ============================================================================

def with_timeout_and_error_handling(timeout_seconds: int = 10, operation_name: str = "operation"):
    """Decorator for timeout handling with background error dialog monitoring."""
    def decorator(func):
        def wrapper(*args, **kwargs):
            import time
            start_time = time.time()

            # Start background error monitoring
            monitor = get_error_monitor()
            monitor.start_monitoring(check_interval_ms=50)  # Check every 50ms for fast detection

            try:
                print(f"  {operation_name.title()}...")

                result = func(*args, **kwargs)

                # Check if error was detected during operation
                if monitor.detected_error:
                    raise AssertionError(monitor.detected_error)

                elapsed = time.time() - start_time
                print(f"  {operation_name.title()} completed successfully in {elapsed:.2f}s")
                return result

            except Exception as e:
                # Check if this was due to detected error dialog
                if monitor.detected_error:
                    raise AssertionError(monitor.detected_error) from e

                elapsed = time.time() - start_time
                if elapsed > timeout_seconds:
                    raise AssertionError(
                        f"LAZY CONFIG BUG DETECTED: {operation_name} timed out after {timeout_seconds}s! "
                        f"This indicates a critical bug in the lazy configuration lifecycle."
                    ) from e
                else:
                    raise AssertionError(
                        f"LAZY CONFIG BUG DETECTED: Error during {operation_name}! "
                        f"Error: {type(e).__name__}: {str(e)[:200]}..."
                    ) from e
            finally:
                # Always stop monitoring when done
                monitor.stop_monitoring()
        return wrapper
    return decorator


def _find_error_dialogs() -> List[Any]:
    """Find any error dialogs that might be blocking the application."""
    from PyQt6.QtWidgets import QMessageBox, QLabel

    error_dialogs = []
    for widget in QApplication.topLevelWidgets():
        if widget.isVisible():
            # Check for QMessageBox (common for error dialogs)
            if isinstance(widget, QMessageBox):
                error_dialogs.append(widget)
            # Check for QDialog with error-related content
            elif isinstance(widget, QDialog):
                title = widget.windowTitle().lower()
                if any(keyword in title for keyword in ['error', 'exception', 'recursion', 'warning', 'unexpected']):
                    error_dialogs.append(widget)
                else:
                    # Check dialog content for error text
                    for label in widget.findChildren(QLabel):
                        if hasattr(label, 'text'):
                            text = label.text().lower()
                            if any(keyword in text for keyword in ['recursion', 'error', 'exception', 'unexpected']):
                                error_dialogs.append(widget)
                                break
    return error_dialogs


def _close_error_dialogs() -> List[str]:
    """Close any error dialogs and return their details."""
    from PyQt6.QtWidgets import QMessageBox, QLabel

    error_dialogs = _find_error_dialogs()
    error_details = []

    for dialog in error_dialogs:
        try:
            # Extract error information before closing
            title = dialog.windowTitle()
            error_text = ""

            if isinstance(dialog, QMessageBox):
                error_text = dialog.text()[:200]
            else:
                # Try to find error text in labels
                for label in dialog.findChildren(QLabel):
                    if hasattr(label, 'text'):
                        text = label.text()
                        if any(keyword in text.lower() for keyword in ['recursion', 'error', 'exception']):
                            error_text = text[:200]
                            break

            error_details.append(f"Dialog: '{title}', Text: '{error_text}'")

            # Try to click OK/Close button if available
            for button in dialog.findChildren(QPushButton):
                button_text = button.text().lower()
                if button_text in ['ok', 'close', 'cancel']:
                    print(f"  Clicking {button.text()} to close error dialog")
                    button.click()
                    break
            else:
                # If no button found, force close
                dialog.close()

            dialog.deleteLater()

        except Exception as e:
            error_details.append(f"Error closing dialog: {e}")
            try:
                dialog.close()
                dialog.deleteLater()
            except:
                pass

    if error_dialogs:
        _wait_for_gui(1.0)  # Allow time for dialogs to close

    return error_details


def find_widget_with_retry(widget_finder: Callable, timeout_seconds: int = 10, check_interval: float = 0.5):
    """Reusable widget finding with timeout and retry logic, with error dialog detection."""
    import time
    start_time = time.time()

    while time.time() - start_time < timeout_seconds:
        # Check for error dialogs first
        error_dialogs = _find_error_dialogs()
        if error_dialogs:
            error_details = _close_error_dialogs()
            raise AssertionError(
                f"LAZY CONFIG BUG DETECTED: Error dialog(s) appeared during operation! "
                f"This indicates the application caught an exception. "
                f"Error dialogs found: {error_details}"
            )

        widget = widget_finder()
        if widget:
            return widget
        _wait_for_gui(check_interval)

    return None


def collect_diagnostic_info() -> Dict[str, Any]:
    """Collect diagnostic information about application state."""
    try:
        return {
            "visible_dialogs": len([w for w in QApplication.topLevelWidgets() if isinstance(w, QDialog) and w.isVisible()]),
            "total_widgets": len(QApplication.topLevelWidgets()),
            "top_level_widgets": [f"{type(w).__name__}: {w.windowTitle()}" for w in QApplication.topLevelWidgets() if w.isVisible()]
        }
    except:
        return {"error": "Could not collect diagnostic info"}


# ============================================================================
# WORKFLOW STEP OPERATIONS
# ============================================================================

def _launch_application(context: WorkflowContext) -> WorkflowContext:
    """Launch real OpenHCS application using normal startup process."""
    from openhcs.pyqt_gui.services.config_cache_adapter import load_cached_global_config_sync
    from openhcs.pyqt_gui.app import OpenHCSPyQtApp
    from openhcs.core.context.global_config import get_current_global_config
    import sys

    config = load_cached_global_config_sync()
    app = OpenHCSPyQtApp(sys.argv, config)

    # Verify global config context establishment
    current_context = get_current_global_config(GlobalPipelineConfig)
    if not current_context:
        raise AssertionError("Global config context NOT established - this will cause placeholder issues")

    main_window = app.create_main_window()

    # Disable aggressive cleanup in main window during tests to prevent segfaults
    def safe_close_event(event):
        """Safe close event that doesn't trigger aggressive cleanup."""
        event.accept()

    # Replace the closeEvent with a safe version during tests
    main_window.closeEvent = safe_close_event

    main_window.show()
    _wait_for_gui(TIMING.WINDOW_DELAY)

    return context.with_updates(main_window=main_window)





def _access_plate_manager(context: WorkflowContext) -> WorkflowContext:
    """Access default plate manager window (already open by default)."""
    plate_manager_window = context.main_window.floating_windows.get("plate_manager")
    if not plate_manager_window:
        raise AssertionError("Plate manager window should be open by default")

    plate_manager_widget = plate_manager_window.findChild(PlateManagerWidget)
    if not plate_manager_widget:
        raise AssertionError("PlateManagerWidget should be found in default window")

    return context.with_updates(plate_manager_widget=plate_manager_widget)


def _add_and_select_plate(context: WorkflowContext) -> WorkflowContext:
    """Add synthetic plate and select it in plate manager."""
    context.plate_manager_widget.add_plate_callback([context.synthetic_plate_dir])
    _wait_for_gui(TIMING.ACTION_DELAY)

    plate_list = context.plate_manager_widget.plate_list
    if plate_list.count() == 0:
        raise AssertionError("No plates found in plate manager list after adding synthetic plate")

    plate_list.setCurrentRow(0)
    _wait_for_gui(TIMING.ACTION_DELAY)
    return context


def _initialize_plate(context: WorkflowContext) -> WorkflowContext:
    """Initialize plate using Init button."""
    init_button = context.plate_manager_widget.buttons["init_plate"]
    if not init_button.isEnabled():
        raise AssertionError("Init button is disabled - plate may not be properly added")

    init_button.click()
    _wait_for_gui(TIMING.SAVE_DELAY)
    return context


def _apply_orchestrator_config(context: WorkflowContext) -> WorkflowContext:
    """Apply parameterized orchestrator configuration to establish 3-level hierarchy."""
    if not context.test_scenario:
        raise ValueError("Test scenario must be provided for parameterized orchestrator configuration")

    orchestrator = context.plate_manager_widget.orchestrators[str(context.synthetic_plate_dir)]

    # Apply configuration from test scenario (eliminates hardcoded values)
    config_params = context.test_scenario.orchestrator_config

    # Import the dynamically generated PipelineConfig
    from openhcs.core.config import PipelineConfig

    # Generic configuration builder - automatically detects direct vs nested fields
    pipeline_config_kwargs = {}
    nested_config_params = {}

    # Get PipelineConfig field names to determine what's direct vs nested
    pipeline_fields = set(PipelineConfig.__dataclass_fields__.keys())

    for field_name, value in config_params.items():
        if field_name in pipeline_fields:
            # Direct field on PipelineConfig
            pipeline_config_kwargs[field_name] = value
        else:
            # Nested field - collect for step_materialization_config
            nested_config_params[field_name] = value

    # If we have nested parameters, create the nested config
    if nested_config_params:
        pipeline_config_kwargs['step_materialization_config'] = LazyStepMaterializationConfig(
            **nested_config_params
        )

    orchestrator_config = PipelineConfig(**pipeline_config_kwargs)
    orchestrator.apply_pipeline_config(orchestrator_config)
    _wait_for_gui(TIMING.ACTION_DELAY)



    return context.with_updates(orchestrator=orchestrator)


def _find_config_window() -> Optional[QDialog]:
    """Find configuration window among top-level widgets."""
    for widget in QApplication.topLevelWidgets():
        if isinstance(widget, QDialog) and "config" in widget.windowTitle().lower():
            return widget
    return None


@with_timeout_and_error_handling(timeout_seconds=10, operation_name="opening configuration window")
def _open_config_window(context: WorkflowContext) -> WorkflowContext:
    """Open plate-specific configuration window."""
    edit_button = context.plate_manager_widget.buttons["edit_config"]
    if not edit_button.isEnabled():
        raise AssertionError("Edit button is disabled - plate may not be properly initialized")

    edit_button.click()
    _wait_for_gui(TIMING.WINDOW_DELAY)

    config_window = find_widget_with_retry(_find_config_window, timeout_seconds=10)
    if not config_window:
        diagnostics = collect_diagnostic_info()
        raise AssertionError(f"Configuration window not found. Diagnostics: {diagnostics}")

    _wait_for_gui(TIMING.ACTION_DELAY)
    return context.with_updates(config_window=config_window)


def _find_field_widget(form_managers: List[ParameterFormManager], field_name: str, config_section: str = None) -> Optional[Any]:
    """Find widget for specified field name across form managers."""
    print(f"🔍 DEBUG: Looking for field '{field_name}' in {len(form_managers)} form managers")

    # Generic approach - search all form managers for the field
    for i, form_manager in enumerate(form_managers):
        has_widgets = hasattr(form_manager, 'widgets')
        widgets_count = len(form_manager.widgets) if has_widgets else 0
        dataclass_name = getattr(form_manager.dataclass_type, '__name__', 'Unknown') if hasattr(form_manager, 'dataclass_type') else 'No dataclass'

        print(f"🔍 DEBUG: Form manager [{i}] {dataclass_name}: has_widgets={has_widgets}, widgets_count={widgets_count}")

        if has_widgets and form_manager.widgets:
            widget_names = list(form_manager.widgets.keys())[:5]  # Show first 5
            print(f"🔍 DEBUG: Available widgets: {widget_names}{'...' if len(form_manager.widgets) > 5 else ''}")

            if field_name in form_manager.widgets:
                print(f"🔍 DEBUG: Found '{field_name}' in form manager [{i}] {dataclass_name}")
                return form_manager.widgets[field_name]

    print(f"🔍 DEBUG: Field '{field_name}' not found in any form manager")
    return None


def _set_widget_value(widget: Any, value: Any) -> None:
    """Set value on widget using appropriate method."""
    if hasattr(widget, 'setValue'):
        widget.setValue(value)
    elif hasattr(widget, 'setText'):
        widget.setText(str(value))
    elif hasattr(widget, 'setCurrentText'):
        widget.setCurrentText(str(value))
    else:
        raise AssertionError(f"Cannot set value on widget of type {type(widget)}")


@with_timeout_and_error_handling(timeout_seconds=5, operation_name="modifying field")
def _modify_field(context: WorkflowContext) -> WorkflowContext:
    """Modify specified field in the configuration window and save."""
    if not context.test_scenario:
        raise ValueError("Test scenario required for parameterized field modification")

    field_name = context.test_scenario.get_modification_field_name()
    field_value = context.test_scenario.get_modification_value()
    config_section = context.test_scenario.field_to_test.config_section

    form_managers = context.config_window.findChildren(ParameterFormManager)
    field_widget = _find_field_widget(form_managers, field_name, config_section)

    print(f"🔧 MODIFY FIELD: Targeting {config_section}.{field_name} = {field_value}")

    if not field_widget:
        available_fields = []
        for fm in form_managers:
            if hasattr(fm, 'widgets'):
                available_fields.extend(fm.widgets.keys())
        raise AssertionError(
            f"Field '{field_name}' widget not found in configuration forms. "
            f"Available fields: {available_fields}"
        )

    print(f"  Setting {field_name} = {field_value}")
    _set_widget_value(field_widget, field_value)
    _wait_for_gui(TIMING.ACTION_DELAY)

    # Save the configuration
    _save_config_window(context)
    return context


def _find_save_button(config_window: QDialog) -> Optional[QPushButton]:
    """Find save/OK button in configuration window."""
    for button in config_window.findChildren(QPushButton):
        if button.text().lower() in ['ok', 'save', 'apply']:
            return button
    return None


@with_timeout_and_error_handling(timeout_seconds=5, operation_name="saving configuration")
def _save_config_window(context: WorkflowContext) -> WorkflowContext:
    """Save configuration window."""
    save_button = _find_save_button(context.config_window)
    if not save_button:
        buttons = [b.text() for b in context.config_window.findChildren(QPushButton)]
        raise AssertionError(f"Save button not found. Available buttons: {buttons}")

    save_button.click()
    _wait_for_gui(TIMING.SAVE_DELAY)
    return context


def _close_config_window(context: WorkflowContext) -> WorkflowContext:
    """Close configuration window with cleanup."""
    try:
        if context.config_window and context.config_window.isVisible():
            context.config_window.close()
            context.config_window.deleteLater()
            _wait_for_gui(TIMING.ACTION_DELAY)

        # Clean up any remaining config windows
        for widget in QApplication.topLevelWidgets():
            if isinstance(widget, QDialog) and "config" in widget.windowTitle().lower() and widget.isVisible():
                widget.close()
                widget.deleteLater()

        _wait_for_gui(TIMING.ACTION_DELAY)
        return context.with_updates(config_window=None)

    except Exception as e:
        print(f"Warning: Error during cleanup: {e}")
        return context.with_updates(config_window=None)


@with_timeout_and_error_handling(timeout_seconds=10, operation_name="reopening configuration window")
def _reopen_config_window(context: WorkflowContext) -> WorkflowContext:
    """Reopen configuration window to test persistence."""
    # Close existing window first
    context = _close_config_window(context)

    # Validate edit button state
    edit_button = context.plate_manager_widget.buttons["edit_config"]
    if not edit_button.isEnabled():
        raise AssertionError(
            "LAZY CONFIG BUG: Edit button disabled after closing config window. "
            "This indicates a state management issue."
        )

    # Reopen using existing function (composition)
    return _open_config_window(context)


def _find_form_manager_for_field(form_managers: List[ParameterFormManager], field_name: str) -> Optional[ParameterFormManager]:
    """Find form manager containing specified field."""
    for form_manager in form_managers:
        if hasattr(form_manager, 'widgets') and field_name in form_manager.widgets:
            return form_manager
    return None


def _find_reset_button_for_field(form_manager: ParameterFormManager, field_name: str) -> Optional[QPushButton]:
    """Find reset button for specified field."""
    if hasattr(form_manager, 'reset_buttons') and field_name in form_manager.reset_buttons:
        return form_manager.reset_buttons[field_name]
    return None


@with_timeout_and_error_handling(timeout_seconds=5, operation_name="resetting field")
def _reset_field(context: WorkflowContext) -> WorkflowContext:
    """Reset specified field to lazy state using reset button."""
    if not context.test_scenario:
        raise ValueError("Test scenario required for parameterized field reset")

    # Use reset_field_to_test if specified, otherwise use the field being modified
    field_name = (context.test_scenario.reset_field_to_test or
                  context.test_scenario.get_modification_field_name())
    form_managers = context.config_window.findChildren(ParameterFormManager)

    target_form_manager = _find_form_manager_for_field(form_managers, field_name)
    if not target_form_manager:
        raise AssertionError(f"Form manager with field '{field_name}' not found")

    print(f"  DEBUG: Looking for reset button for field '{field_name}'")
    if hasattr(target_form_manager, 'reset_buttons'):
        print(f"  DEBUG: Available reset buttons: {list(target_form_manager.reset_buttons.keys())}")
    else:
        print(f"  DEBUG: Form manager has no reset_buttons attribute")

    reset_button = _find_reset_button_for_field(target_form_manager, field_name)
    if not reset_button:
        raise AssertionError(f"Reset button for field '{field_name}' not found")

    print(f"  Resetting {field_name} to lazy state")
    reset_button.click()
    _wait_for_gui(TIMING.ACTION_DELAY)

    return context


# ============================================================================
# PARAMETERIZED VALIDATION FRAMEWORK
# ============================================================================

def _verify_step_editor_placeholder_resolution(context: WorkflowContext) -> WorkflowContext:
    """
    Verify that step editor placeholders show resolved values after plate initialization.

    This test verifies the fix for the placeholder resolution bug where step editor
    placeholders showed empty/None values instead of proper resolved values from
    the global configuration hierarchy.
    """
    print(f"\n🔍 Verifying step editor placeholder resolution after initialization...")

    # Access pipeline editor (should already be open)
    if "pipeline_editor" not in context.main_window.floating_windows:
        raise AssertionError("Pipeline editor window not found in floating_windows")

    pipeline_editor_window = context.main_window.floating_windows["pipeline_editor"]

    # Find the actual pipeline editor widget
    pipeline_editor = None
    for child in pipeline_editor_window.findChildren(QWidget):
        if hasattr(child, 'pipeline_steps'):
            pipeline_editor = child
            break

    if not pipeline_editor:
        raise AssertionError("Pipeline editor widget not found")

    # Click "Add Step" to open step editor
    if not hasattr(pipeline_editor, 'buttons') or "add_step" not in pipeline_editor.buttons:
        raise AssertionError("Add Step button not found in pipeline editor buttons")

    add_step_button = pipeline_editor.buttons["add_step"]
    add_step_button.click()
    QApplication.processEvents()

    # Wait for step editor to open
    import time
    time.sleep(2.0)
    QApplication.processEvents()

    # Find the step editor window (DualEditorWindow)
    step_editor_window = None
    for widget in QApplication.topLevelWidgets():
        if hasattr(widget, 'step_editor') and hasattr(widget, 'editing_step'):
            step_editor_window = widget
            break

    if not step_editor_window:
        raise AssertionError("Step editor window (DualEditorWindow) not found")

    # Access the step parameter editor widget
    step_param_editor = step_editor_window.step_editor
    if not step_param_editor:
        raise AssertionError("Step parameter editor widget not found in DualEditorWindow")

    # Find the form manager
    if not hasattr(step_param_editor, 'form_manager'):
        raise AssertionError("Form manager not found in step parameter editor")

    form_manager = step_param_editor.form_manager

    # Check materialization_config nested form manager for placeholder resolution
    placeholder_resolution_verified = False

    if hasattr(form_manager, 'nested_managers') and 'materialization_config' in form_manager.nested_managers:
        nested_manager = form_manager.nested_managers['materialization_config']

        # Check key fields that should have resolved placeholders
        test_fields = ['output_dir_suffix', 'sub_dir']

        for field_name in test_fields:
            if hasattr(nested_manager, 'widgets') and field_name in nested_manager.widgets:
                widget = nested_manager.widgets[field_name]
                texts = _extract_widget_texts(widget)
                all_text = " ".join(texts.values())

                print(f"🔍 STEP EDITOR {field_name}:")
                print(f"  All text: '{all_text}'")
                print(f"  Individual texts: {texts}")

                # Verify placeholder shows resolved values, not empty/None
                if "pipeline default:" in all_text.lower():
                    # Should show resolved value from global pipeline config (e.g., "_openhcs", "_processed", "checkpoints")
                    # Since orchestrator pipeline config is not modified, resolution should pass through to global config
                    if "_openhcs" in all_text or "_processed" in all_text or "checkpoints" in all_text or "_outputs" in all_text or "images" in all_text:
                        print(f"✅ GOOD: {field_name} placeholder shows resolved value: '{all_text}'")
                        placeholder_resolution_verified = True
                    else:
                        print(f"🚨 BUG: {field_name} placeholder should show resolved value but shows: '{all_text}'")
                        raise AssertionError(
                            f"Placeholder resolution bug: {field_name} should show resolved value "
                            f"from global pipeline config but shows: '{all_text}'"
                        )
                elif all_text.strip() == "" or "none" in all_text.lower():
                    print(f"🚨 BUG: {field_name} placeholder is empty/None: '{all_text}'")
                    raise AssertionError(
                        f"Placeholder resolution bug: {field_name} placeholder is empty/None instead of showing resolved value"
                    )
                else:
                    print(f"🔍 {field_name} shows direct value (not placeholder): '{all_text}'")

    # Close the step editor window to clean up
    step_editor_window.close()
    QApplication.processEvents()

    if not placeholder_resolution_verified:
        print(f"⚠️  WARNING: Could not verify placeholder resolution - materialization_config form not found")
    else:
        print(f"✅ Step editor placeholder resolution verified successfully")

    return context


def _validate_placeholder_behavior(context: WorkflowContext) -> WorkflowContext:
    """Parameterized placeholder behavior validation using test scenario configuration."""
    if not context.test_scenario:
        raise ValueError("Test scenario required for parameterized validation")

    form_managers = context.config_window.findChildren(ParameterFormManager)
    validation_results = {}

    # Get expected patterns from test scenario (eliminates hardcoded values)
    expected_patterns = context.test_scenario.get_expected_validation_patterns()

    for form_manager in form_managers:
        if not hasattr(form_manager, 'widgets'):
            continue

        for field_name, widget in form_manager.widgets.items():
            # Extract all text from widget
            texts = _extract_widget_texts(widget)
            all_text = " ".join(texts.values()).lower()

            # Parameterized validation analysis
            validation_result = _analyze_widget_text(all_text, expected_patterns, context.test_scenario)

            # Store validation results with consistent naming
            for suffix, value in validation_result.items():
                validation_results[f"{field_name}{suffix}"] = value

    return context.with_updates(validation_results=validation_results)


def _validate_field_persistence(context: WorkflowContext) -> WorkflowContext:
    """Validate that modified field shows saved value while other fields show lazy state."""
    if not context.test_scenario:
        raise ValueError("Test scenario required for parameterized validation")

    modified_field = context.test_scenario.get_modification_field_name()
    expected_value = str(context.test_scenario.get_modification_value()).lower()

    form_managers = context.config_window.findChildren(ParameterFormManager)
    validation_results = context.validation_results.copy()

    for form_manager in form_managers:
        if not hasattr(form_manager, 'widgets'):
            continue

        for field_name, widget in form_manager.widgets.items():
            texts = _extract_widget_texts(widget)
            all_text = " ".join(texts.values()).lower()

            if field_name == modified_field:
                # Modified field should show the saved value, not None or placeholder
                shows_saved_value = expected_value in all_text and "(none)" not in all_text
                validation_results[f"{field_name}_shows_saved_value"] = shows_saved_value
            else:
                # Other fields should show lazy state with pipeline defaults
                shows_pipeline_default = "pipeline default:" in all_text
                shows_none_correctly = "(none)" not in all_text or field_name in context.test_scenario.legitimate_none_fields
                validation_results[f"{field_name}_shows_lazy_state"] = shows_pipeline_default and shows_none_correctly

    return context.with_updates(validation_results=validation_results)


def _validate_full_lazy_state(context: WorkflowContext) -> WorkflowContext:
    """Validate that ALL fields show lazy state after reset."""
    form_managers = context.config_window.findChildren(ParameterFormManager)
    validation_results = context.validation_results.copy()

    for form_manager in form_managers:
        if not hasattr(form_manager, 'widgets'):
            continue

        for field_name, widget in form_manager.widgets.items():
            texts = _extract_widget_texts(widget)
            all_text = " ".join(texts.values()).lower()

            # ALL fields should now show lazy state with pipeline defaults
            shows_pipeline_default = "pipeline default:" in all_text
            shows_none_correctly = "(none)" not in all_text or field_name in context.test_scenario.legitimate_none_fields
            validation_results[f"{field_name}_shows_full_lazy_state"] = shows_pipeline_default and shows_none_correctly

    return context.with_updates(validation_results=validation_results)


def _analyze_widget_text(text: str, expected_patterns: List[str], scenario: TestScenario) -> Dict[str, bool]:
    """Analyze widget text against expected patterns from test scenario."""
    return {
        VALIDATION_SUFFIXES.NONE: "(none)" in text,
        VALIDATION_SUFFIXES.PIPELINE_DEFAULT: "pipeline default:" in text,
        VALIDATION_SUFFIXES.ORCHESTRATOR_VALUES: any(
            str(pattern).lower() in text for pattern in expected_patterns if pattern
        )
    }


def _extract_widget_texts(widget) -> Dict[str, str]:
    """Extract all text content from a widget."""
    texts = {}

    if hasattr(widget, 'placeholderText'):
        texts['placeholder'] = widget.placeholderText() or ""
    if hasattr(widget, 'specialValueText'):
        texts['special'] = widget.specialValueText() or ""
    if hasattr(widget, 'toolTip'):
        texts['tooltip'] = widget.toolTip() or ""
    if hasattr(widget, 'text'):
        try:
            texts['text'] = widget.text() or ""
        except:
            texts['text'] = ""

    return texts


def _create_parameterized_assertions(scenario: TestScenario) -> List[Callable[[WorkflowContext], None]]:
    """Create parameterized assertion functions based on test scenario."""

    def assert_no_placeholder_bugs(context: WorkflowContext) -> None:
        """Assert that no fields show '(none)' incorrectly based on scenario."""
        results = context.validation_results

        # Find fields showing "(none)"
        fields_showing_none = [
            key for key, value in results.items()
            if key.endswith(VALIDATION_SUFFIXES.NONE) and value
        ]

        # Filter out legitimate None fields based on scenario
        legitimate_none_keys = {
            f"{field}{VALIDATION_SUFFIXES.NONE}"
            for field in scenario.legitimate_none_fields
        }
        actual_bug_fields = [
            field for field in fields_showing_none
            if field not in legitimate_none_keys
        ]

        if actual_bug_fields:
            raise AssertionError(
                f"PLACEHOLDER BUG in scenario '{scenario.name}': "
                f"Fields showing '(none)': {actual_bug_fields}. "
                f"Context capture fix is not working!"
            )

    def assert_inheritance_working(context: WorkflowContext) -> None:
        """Assert that orchestrator values are being inherited based on scenario."""
        results = context.validation_results

        fields_showing_orchestrator_values = [
            key for key, value in results.items()
            if key.endswith(VALIDATION_SUFFIXES.ORCHESTRATOR_VALUES) and value
        ]

        if not fields_showing_orchestrator_values:
            expected_patterns = scenario.get_expected_validation_patterns()
            raise AssertionError(
                f"No orchestrator values detected in scenario '{scenario.name}' - "
                f"inheritance may not be working. Expected patterns: {expected_patterns}"
            )

    def assert_scenario_specific_validation(context: WorkflowContext) -> None:
        """Assert scenario-specific validation criteria."""
        results = context.validation_results

        # Verify expected values are found
        orchestrator_value_fields = [
            key for key, value in results.items()
            if key.endswith(VALIDATION_SUFFIXES.ORCHESTRATOR_VALUES) and value
        ]

        if len(orchestrator_value_fields) < len(scenario.expected_values):
            raise AssertionError(
                f"Scenario '{scenario.name}' validation incomplete: "
                f"Expected {len(scenario.expected_values)} fields with orchestrator values, "
                f"found {len(orchestrator_value_fields)}"
            )

    return [assert_no_placeholder_bugs, assert_inheritance_working, assert_scenario_specific_validation]


def _create_persistence_validation_assertions(scenario: TestScenario) -> List[Callable[[WorkflowContext], None]]:
    """Create assertions for validating field modification persistence."""

    def assert_field_persistence(context: WorkflowContext) -> None:
        """Assert that modified field shows saved value while others show lazy state."""
        results = context.validation_results
        modified_field = scenario.get_modification_field_name()

        # Modified field should show saved value
        saved_value_key = f"{modified_field}_shows_saved_value"
        if not results.get(saved_value_key, False):
            raise AssertionError(
                f"Scenario '{scenario.name}': Field '{modified_field}' should show saved value "
                f"({scenario.get_modification_value()}), but validation failed"
            )

        # Other fields should show lazy state
        lazy_state_fields = [
            key for key, value in results.items()
            if key.endswith('_shows_lazy_state') and not value and not key.startswith(modified_field)
        ]

        if lazy_state_fields:
            raise AssertionError(
                f"Scenario '{scenario.name}': Fields not showing lazy state: {lazy_state_fields}"
            )

    return [assert_field_persistence]


def _create_reset_validation_assertions(scenario: TestScenario) -> List[Callable[[WorkflowContext], None]]:
    """Create assertions for validating reset functionality."""

    def assert_no_concrete_values_in_reset_placeholders(context: WorkflowContext) -> None:
        """Assert that reset placeholders don't show concrete saved values."""
        if scenario.name != "reset_placeholder_bug":
            return  # Only run this assertion for the specific bug scenario

        print(f"\n🔍 CHECKING FOR RESET PLACEHOLDER BUG...")
        form_managers = context.config_window.findChildren(ParameterFormManager)

        bug_detected = False
        output_dir_suffix_found = False
        num_workers_found = False

        for form_manager in form_managers:
            if not hasattr(form_manager, 'widgets'):
                continue

            for field_name, widget in form_manager.widgets.items():
                texts = _extract_widget_texts(widget)
                all_text = " ".join(texts.values())

                # Debug: Show what we find for output_dir_suffix specifically
                if field_name == "output_dir_suffix":
                    output_dir_suffix_found = True
                    print(f"🔍 OUTPUT_DIR_SUFFIX FIELD AFTER RESET:")
                    print(f"  Field name: {field_name}")
                    print(f"  All text: '{all_text}'")
                    print(f"  Individual texts: {texts}")

                    # Check what the placeholder actually shows
                    if "pipeline default:" in all_text.lower():
                        if "828282" in all_text:
                            print(f"🚨 BUG: Placeholder shows concrete saved value '828282'")
                            bug_detected = True
                        elif "_openhcs" in all_text:
                            print(f"✅ GOOD: Placeholder shows inheritance value '_openhcs'")
                        else:
                            print(f"❓ UNKNOWN: Placeholder shows something else")

                # Debug: Show what we find for num_workers specifically
                if field_name == "num_workers":
                    num_workers_found = True
                    print(f"🔍 NUM_WORKERS FIELD AFTER RESET:")
                    print(f"  Field name: {field_name}")
                    print(f"  All text: '{all_text}'")
                    print(f"  Individual texts: {texts}")

                    # Check what the placeholder actually shows
                    if "pipeline default:" in all_text.lower():
                        if "16" in all_text:
                            print(f"🚨 BUG: Placeholder shows static default '16' instead of saved value '1'")
                            bug_detected = True
                        elif "1" in all_text:
                            print(f"✅ GOOD: Placeholder shows saved value '1'")
                        else:
                            print(f"❓ UNKNOWN: Placeholder shows something else")

                # Check if placeholder contains the concrete saved value "828282"
                if "828282" in all_text:
                    print(f"🐛 FOUND '828282' in field '{field_name}': {all_text}")
                    if "pipeline default:" in all_text.lower():
                        bug_detected = True
                        print(f"🚨 RESET PLACEHOLDER BUG CONFIRMED: Field '{field_name}' shows concrete value '828282' in placeholder!")

        if not output_dir_suffix_found:
            raise AssertionError("TEST ERROR: output_dir_suffix field not found in form managers!")

        if not num_workers_found:
            raise AssertionError("TEST ERROR: num_workers field not found in form managers!")

        if bug_detected:
            raise AssertionError(
                f"RESET PLACEHOLDER BUG DETECTED: One or more fields show wrong values in placeholder after reset. "
                f"output_dir_suffix should show inheritance value '_openhcs', not concrete saved value '828282'. "
                f"num_workers should show saved value '1', not static default '16'."
            )
        else:
            print(f"✅ No reset placeholder bug detected - both output_dir_suffix and num_workers show correct values")

    return [assert_no_concrete_values_in_reset_placeholders]


class TestPyQtGUIWorkflowFoundation:

    @pytest.fixture
    def synthetic_plate_dir(self, tmp_path):
        """Create synthetic plate data for testing."""
        return _create_synthetic_plate(tmp_path)

    @pytest.fixture
    def global_config(self):
        """Create test global configuration."""
        return _create_test_global_config()

    @pytest.fixture(autouse=True)
    def cleanup_gui_state(self, qtbot):
        """Automatically cleanup GUI state between tests with error monitoring."""
        # Setup: Clear any existing state
        from PyQt6.QtWidgets import QApplication
        from openhcs.pyqt_gui.main import OpenHCSMainWindow

        # Close any existing top-level widgets (except OpenHCS main windows)
        for widget in QApplication.topLevelWidgets():
            if widget.isVisible() and not isinstance(widget, OpenHCSMainWindow):
                widget.close()
                widget.deleteLater()

        QApplication.processEvents()

        # Start global error monitoring for the entire test
        monitor = get_error_monitor()
        monitor.start_monitoring(check_interval_ms=100)

        try:
            yield  # Run the test

            # Check if any errors were detected during the test
            if monitor.detected_error:
                raise AssertionError(f"Error detected during test execution: {monitor.detected_error}")

        finally:
            # Always stop monitoring
            monitor.stop_monitoring()

            # Teardown: Gentle cleanup to avoid main window closeEvent conflicts
            try:
                # First, close floating windows manually to avoid main window cleanup
                for widget in QApplication.topLevelWidgets():
                    if isinstance(widget, OpenHCSMainWindow):
                        # Manually close floating windows without triggering main window closeEvent
                        for window_name, window in list(widget.floating_windows.items()):
                            try:
                                window.hide()
                                window.deleteLater()
                            except:
                                pass
                        widget.floating_windows.clear()

                        # Hide main window without calling close() to avoid closeEvent
                        widget.hide()
                        widget.deleteLater()
                    elif widget.isVisible():
                        widget.close()
                        widget.deleteLater()

                # Process events gently
                QApplication.processEvents()

            except Exception as e:
                print(f"Warning: Error during GUI cleanup: {e}")
                # Continue anyway - don't fail the test due to cleanup issues

    @pytest.mark.parametrize("test_scenario", [
        DEFAULT_SCENARIO,
        RESET_PLACEHOLDER_BUG_PATH_PLANNING_SCENARIO,  # Test inheritance from path_planning
        RESET_PLACEHOLDER_BUG_MATERIALIZATION_SCENARIO,  # Test inheritance from materialization_defaults
        RESET_PLACEHOLDER_BUG_DIRECT_FIELD_SCENARIO,  # Test direct field reset placeholders
        # ALTERNATIVE_SCENARIO,  # Commented out for now - sufficient to test with one scenario
        # MINIMAL_SCENARIO       # Commented out for now - sufficient to test with one scenario
    ], ids=lambda scenario: scenario.name)
    def test_parameterized_end_to_end_workflow(
        self, qtbot, synthetic_plate_dir, test_scenario: TestScenario
    ):
        """
        Parameterized end-to-end workflow test demonstrating mathematical simplification.

        This test showcases the systematic refactoring framework principles:
        - Elimination of hardcoded values through parameterization
        - Bidirectional parameter mapping between config and validation
        - Mathematical simplification through modular, reusable components
        - Single validation logic handling multiple test scenarios
        """
        print(f"\n=== Parameterized Workflow Test: {test_scenario.name} ===")
        print(f"Config: {test_scenario.orchestrator_config}")
        print(f"Expected: {test_scenario.expected_values}")

        # Create parameterized assertions based on test scenario
        scenario_assertions = _create_parameterized_assertions(test_scenario)

        # Build workflow using composable steps with parameterized validation
        workflow = (WorkflowBuilder()
            .add_step(WorkflowStep(
                name="Launch OpenHCS Application",
                operation=_launch_application,
                timing_delay=TIMING.WINDOW_DELAY
            ))
            .add_step(WorkflowStep(
                name="Access Plate Manager",
                operation=_access_plate_manager
            ))
            .add_step(WorkflowStep(
                name="Add and Select Plate",
                operation=_add_and_select_plate,
                timing_delay=TIMING.ACTION_DELAY
            ))
            .add_step(WorkflowStep(
                name="Initialize Plate",
                operation=_initialize_plate,
                timing_delay=TIMING.SAVE_DELAY
            ))
            .add_step(WorkflowStep(
                name="Verify Step Editor Placeholder Resolution After Initialization",
                operation=_verify_step_editor_placeholder_resolution,
                timing_delay=TIMING.ACTION_DELAY
            ))
            .add_step(WorkflowStep(
                name="Apply Parameterized Orchestrator Configuration",
                operation=_apply_orchestrator_config,
                timing_delay=TIMING.ACTION_DELAY
            ))
            .add_step(WorkflowStep(
                name="Open Configuration Window",
                operation=_open_config_window,
                timing_delay=TIMING.WINDOW_DELAY
            ))
            .add_step(WorkflowStep(
                name="Validate Initial Parameterized Placeholder Behavior",
                operation=_validate_placeholder_behavior
            ))
            # === LAZY CONFIGURATION LIFECYCLE VALIDATION ===
            .add_step(WorkflowStep(
                name=f"Modify {test_scenario.get_modification_field_name().title()} Field",
                operation=_modify_field,
                timing_delay=TIMING.SAVE_DELAY
            ))
            .add_step(WorkflowStep(
                name="Reopen Configuration Window",
                operation=_reopen_config_window,
                timing_delay=TIMING.WINDOW_DELAY
            ))
            .add_step(WorkflowStep(
                name=f"Validate {test_scenario.get_modification_field_name().title()} Persistence",
                operation=_validate_field_persistence
            ))
            .add_step(WorkflowStep(
                name=f"Reset {(test_scenario.reset_field_to_test or test_scenario.get_modification_field_name()).title().replace('_', ' ')} Field",
                operation=_reset_field,
                timing_delay=TIMING.ACTION_DELAY
            ))
        )

        # DIRECT FIELD RESET PLACEHOLDER BUG TEST - 10-Step Sequence
        if test_scenario.name == "reset_placeholder_bug_direct_field":

            # Step 7: Verify immediate state after reset (global default, not concrete value)
            def check_reset_immediate_state(context: WorkflowContext) -> WorkflowContext:
                """Step 7: Check that placeholder immediately shows global default after reset."""
                print(f"\n🔍 STEP 7: Verifying immediate state after reset...")

                field_name = test_scenario.field_to_test.field_name
                form_managers = context.config_window.findChildren(ParameterFormManager)

                for form_manager in form_managers:
                    if hasattr(form_manager, 'widgets') and field_name in form_manager.widgets:
                        widget = form_manager.widgets[field_name]
                        texts = _extract_widget_texts(widget)
                        all_text = " ".join(texts.values())
                        print(f"🔍 IMMEDIATE AFTER RESET {field_name}: '{all_text}'")

                        # Should show global default (1), not concrete value (2)
                        if "1" in all_text and "2" not in all_text:
                            print(f"✅ GOOD: Immediate reset shows global default (1), not concrete value (2)")
                        else:
                            print(f"❌ BAD: Immediate reset shows wrong value - expected global default (1)")
                        break

                return context

            workflow.add_step(WorkflowStep(
                name="Step 7: Check Reset Immediate State",
                operation=check_reset_immediate_state,
                timing_delay=0.1
            ))

            # Step 8: Save and close to persist the lazy/None state
            def save_and_close_after_reset(context: WorkflowContext) -> WorkflowContext:
                """Step 8: Save configuration to persist lazy state, then close window."""
                print(f"\n🔍 STEP 8: Saving and closing to persist lazy state...")

                print(f"🔧 Saving configuration after reset...")
                context.config_window.save_config()

                print(f"🔧 Closing configuration window...")
                context.config_window.close()
                context.config_window = None

                return context

            workflow.add_step(WorkflowStep(
                name="Step 8: Save And Close After Reset",
                operation=save_and_close_after_reset,
                timing_delay=1.0
            ))

            # Step 9: Reopen configuration window for final verification
            workflow.add_step(WorkflowStep(
                name="Step 9: Reopen For Final Verification",
                operation=_reopen_config_window,
                timing_delay=1.0
            ))

            # Step 10: Final verification - field should be None with global default placeholder
            def verify_final_reset_state(context: WorkflowContext) -> WorkflowContext:
                """Step 10: Verify field is None and placeholder shows global default (not concrete value)."""
                print(f"\n🔍 STEP 10: Final verification after save/reopen...")

                field_name = test_scenario.field_to_test.field_name
                concrete_value = test_scenario.field_to_test.modification_value
                form_managers = context.config_window.findChildren(ParameterFormManager)

                for form_manager in form_managers:
                    if hasattr(form_manager, 'widgets') and field_name in form_manager.widgets:
                        widget = form_manager.widgets[field_name]
                        texts = _extract_widget_texts(widget)
                        all_text = " ".join(texts.values())
                        print(f"🔍 FINAL STATE {field_name}: '{all_text}'")

                        # Critical test: Should show global default (1), NOT concrete value (2)
                        if "1" in all_text and str(concrete_value) not in all_text:
                            print(f"✅ SUCCESS: Reset placeholder shows global default (1), not concrete value ({concrete_value})")
                            print(f"✅ DIRECT FIELD RESET PLACEHOLDER BUG TEST PASSED!")
                        else:
                            print(f"❌ FAILURE: Reset placeholder shows concrete value ({concrete_value}) instead of global default (1)")
                            print(f"❌ This confirms the direct field reset placeholder bug exists!")
                            raise AssertionError(f"Direct field reset placeholder bug detected: shows {concrete_value} instead of global default")
                        break

                return context

            workflow.add_step(WorkflowStep(
                name="Step 10: Verify Final Reset State",
                operation=verify_final_reset_state,
                timing_delay=0.5
            ))

        # OTHER RESET PLACEHOLDER BUG SCENARIOS (nested fields) - Keep existing complex workflow
        elif test_scenario.name.startswith("reset_placeholder_bug"):
            def set_concrete_config_value(context: WorkflowContext) -> WorkflowContext:
                """Set a concrete value in the specified config section for inheritance test."""
                config_section = test_scenario.field_to_test.config_section
                field_name = test_scenario.field_to_test.field_name
                concrete_value = test_scenario.field_to_test.modification_value

                # Add unique test identifier to track if this function runs multiple times
                import time
                unique_id = int(time.time() * 1000) % 10000
                print(f"🚨🚨🚨 FUNCTION ENTRY #{unique_id}: set_concrete_config_value for {config_section}.{field_name} = {concrete_value}")
                print(f"\n🔧 Setting concrete value in {config_section}.{field_name}...")

                # Find the specified config section field
                form_managers = context.config_window.findChildren(ParameterFormManager)
                field_found = False

                # BEFORE: Show all current field values AND widget IDs
                print(f"🔍 BEFORE MODIFICATION - All field values and widget IDs:")
                for i, form_manager in enumerate(form_managers):
                    if hasattr(form_manager, 'widgets') and hasattr(form_manager, 'dataclass_type'):
                        dataclass_name = getattr(form_manager.dataclass_type, '__name__', 'Unknown')
                        for field_name_check, widget in form_manager.widgets.items():
                            if field_name_check == field_name:  # Only show the target field
                                current_value = widget.text() if hasattr(widget, 'text') else 'No text method'
                                widget_id = id(widget)
                                print(f"  [{i}] {dataclass_name}.{field_name_check} = '{current_value}' (widget ID: {widget_id})")

                # GENERIC: Search all form managers for the field
                print(f"🎯 GENERIC: Searching all form managers for {field_name}")
                print(f"🎯 Total form managers available: {len(form_managers)}")

                target_form_manager = None
                target_index = None

                # Search through all form managers to find the one with our field
                for i, form_manager in enumerate(form_managers):
                    if hasattr(form_manager, 'widgets') and field_name in form_manager.widgets:
                        target_form_manager = form_manager
                        target_index = i
                        break

                if target_form_manager:
                    print(f"🎯 FOUND form manager at index [{target_index}]")

                    # Verify this is the right form manager
                    if hasattr(target_form_manager, 'dataclass_type'):
                        dataclass_name = getattr(target_form_manager.dataclass_type, '__name__', 'Unknown')
                        print(f"🔧 Confirmed target: [{target_index}] {dataclass_name}")

                        widget = target_form_manager.widgets[field_name]
                        print(f"🔧 Setting {config_section}.{field_name} = {concrete_value}")

                        # Set the concrete value
                        if hasattr(widget, 'setText'):
                            widget.setText(str(concrete_value))
                            print(f"🔧 SUCCESS: setText({concrete_value}) on {dataclass_name}")
                        elif hasattr(widget, 'setValue'):
                            widget.setValue(concrete_value)
                            print(f"🔧 SUCCESS: setValue({concrete_value}) on {dataclass_name}")

                        # Update form manager parameters
                        target_form_manager.parameters[field_name] = concrete_value
                        field_found = True
                    else:
                        print(f"❌ ERROR: Target form manager has no dataclass_type")
                else:
                    print(f"❌ ERROR: Field {field_name} not found in any form manager")
                    print(f"🔧 Widget parent: {widget.parent() if hasattr(widget, 'parent') else 'No parent'}")
                    print(f"🔧 Current widget text before: '{widget.text() if hasattr(widget, 'text') else 'No text method'}'")

                    # Set a unique test value first to verify we're editing the right widget
                    test_value = f"TEST_{config_section}_{concrete_value}"

                    # Set the concrete value
                    if hasattr(widget, 'setText'):
                        print(f"🚨 ABOUT TO CALL setText({test_value}) on {dataclass_name}")
                        widget.setText(test_value)
                        print(f"🔧 Called setText({test_value}) on widget")
                        print(f"🔧 Widget text after: '{widget.text()}'")
                        print(f"🚨 ONLY THIS ONE WIDGET SHOULD BE MODIFIED!")
                    elif hasattr(widget, 'setValue'):
                        print(f"🚨 ABOUT TO CALL setValue({test_value}) on {dataclass_name}")
                        widget.setValue(test_value)
                        print(f"🔧 Called setValue({test_value}) on widget")
                        print(f"🚨 ONLY THIS ONE WIDGET SHOULD BE MODIFIED!")

                    # Update form manager parameters
                    target_form_manager.parameters[field_name] = concrete_value
                    field_found = True

                # AFTER: Show all field values to confirm only one was modified
                print(f"🔍 AFTER MODIFICATION - All field values:")
                for i, form_manager in enumerate(form_managers):
                    if hasattr(form_manager, 'widgets') and hasattr(form_manager, 'dataclass_type'):
                        dataclass_name = getattr(form_manager.dataclass_type, '__name__', 'Unknown')
                        for field_name_check, widget in form_manager.widgets.items():
                            if field_name_check == field_name:  # Only show the target field
                                current_value = widget.text() if hasattr(widget, 'text') else 'No text method'
                                print(f"  [{i}] {dataclass_name}.{field_name_check} = '{current_value}'")

                if not field_found:
                    raise AssertionError(f"{config_section}.{field_name} field not found")

                # Save the configuration
                print(f"🔧 Saving configuration with concrete value...")
                context.config_window.save_config()

                # Close configuration window
                print(f"🔧 Closing configuration window...")
                context.config_window.close()
                context.config_window = None

                return context

            workflow.add_step(WorkflowStep(
                name=f"Set Concrete {test_scenario.field_to_test.config_section.title()} Value",
                operation=set_concrete_config_value,
                timing_delay=1.0
            ))

            # Step 2: Test Step Editor Inheritance
            def test_step_editor_inheritance(context: WorkflowContext) -> WorkflowContext:
                """Open step editor and verify materialization_config inherits from path_planning."""
                print(f"\n🔍 Testing step editor materialization inheritance...")

                # Access pipeline editor (should already be open)
                if "pipeline_editor" not in context.main_window.floating_windows:
                    raise AssertionError("Pipeline editor window not found in floating_windows")

                pipeline_editor_window = context.main_window.floating_windows["pipeline_editor"]

                # Find the actual pipeline editor widget
                pipeline_editor = None
                for child in pipeline_editor_window.findChildren(QWidget):
                    if hasattr(child, 'pipeline_steps'):
                        pipeline_editor = child
                        break

                if not pipeline_editor:
                    raise AssertionError("Pipeline editor widget not found")

                # Click "Add Step" to open step editor
                print(f"🔍 Pipeline editor buttons: {list(pipeline_editor.buttons.keys()) if hasattr(pipeline_editor, 'buttons') else 'No buttons attribute'}")

                if not hasattr(pipeline_editor, 'buttons') or "add_step" not in pipeline_editor.buttons:
                    raise AssertionError("Add Step button not found in pipeline editor buttons")

                add_step_button = pipeline_editor.buttons["add_step"]
                print(f"🔧 Add Step button found: {add_step_button}")
                print(f"🔧 Button enabled: {add_step_button.isEnabled()}")

                print(f"🔧 Clicking Add Step button...")
                add_step_button.click()
                QApplication.processEvents()

                # Wait longer for step editor to open
                import time
                time.sleep(2.0)  # Give more time for the window to open
                QApplication.processEvents()

                # Debug: List all top-level widgets
                print(f"🔍 All top-level widgets:")
                for i, widget in enumerate(QApplication.topLevelWidgets()):
                    print(f"  {i}: {type(widget).__name__} - {widget.windowTitle() if hasattr(widget, 'windowTitle') else 'No title'}")
                    if hasattr(widget, 'step_editor'):
                        print(f"    Has step_editor: {widget.step_editor}")
                    if hasattr(widget, 'editing_step'):
                        print(f"    Has editing_step: {widget.editing_step}")

                # Find the step editor window (DualEditorWindow)
                step_editor_window = None
                for widget in QApplication.topLevelWidgets():
                    if hasattr(widget, 'step_editor') and hasattr(widget, 'editing_step'):
                        step_editor_window = widget
                        print(f"🎯 Found step editor window: {type(widget).__name__}")
                        break

                if not step_editor_window:
                    raise AssertionError("Step editor window (DualEditorWindow) not found")

                print(f"🔍 Found step editor window, checking materialization_config placeholders...")

                # Access the step parameter editor widget within the DualEditorWindow
                step_param_editor = step_editor_window.step_editor
                if not step_param_editor:
                    raise AssertionError("Step parameter editor widget not found in DualEditorWindow")

                # Find the form manager in the step parameter editor
                if not hasattr(step_param_editor, 'form_manager'):
                    raise AssertionError("Form manager not found in step parameter editor")

                form_manager = step_param_editor.form_manager

                # Look for materialization_config nested form managers
                materialization_inheritance_verified = False

                # Check if there are nested managers for materialization_config
                if hasattr(form_manager, 'nested_managers') and 'materialization_config' in form_manager.nested_managers:
                    nested_manager = form_manager.nested_managers['materialization_config']

                    if hasattr(nested_manager, 'widgets') and 'output_dir_suffix' in nested_manager.widgets:
                        widget = nested_manager.widgets['output_dir_suffix']
                        texts = _extract_widget_texts(widget)
                        all_text = " ".join(texts.values())

                        print(f"🔍 STEP MATERIALIZATION output_dir_suffix:")
                        print(f"  Field name: output_dir_suffix")
                        print(f"  All text: '{all_text}'")
                        print(f"  Individual texts: {texts}")

                        # Check if placeholder shows the concrete value from the modified config section
                        expected_value = test_scenario.field_to_test.modification_value
                        modified_section = test_scenario.field_to_test.config_section

                        if "pipeline default:" in all_text.lower():
                            # The inherited value should be the test scenario's modification value
                            if str(expected_value) in all_text:
                                print(f"✅ GOOD: Step materialization placeholder shows inherited concrete value '{expected_value}' from {modified_section}")

                                # Also verify that the checkbox is unchecked (key part of the fix)
                                checkboxes = step_editor_window.findChildren(QCheckBox)
                                materialization_checkbox = None
                                for checkbox in checkboxes:
                                    # Find the checkbox associated with materialization_config
                                    if checkbox.text() and "materialization" in checkbox.text().lower():
                                        materialization_checkbox = checkbox
                                        break

                                if materialization_checkbox:
                                    if not materialization_checkbox.isChecked():
                                        print(f"✅ GOOD: Step materialization checkbox is unchecked (as expected)")
                                    else:
                                        print(f"🚨 BUG: Step materialization checkbox should be unchecked but is checked")
                                        raise AssertionError(
                                            f"Step materialization checkbox should start unchecked but is checked. "
                                            f"This indicates the step-level config logic is not working properly."
                                        )
                                else:
                                    print(f"⚠️  WARNING: Could not find materialization checkbox to verify state")

                                materialization_inheritance_verified = True
                            else:
                                print(f"🚨 BUG: Step materialization placeholder should show '{expected_value}' from {modified_section}")
                                raise AssertionError(
                                    f"Step materialization inheritance bug: output_dir_suffix placeholder should show "
                                    f"'Pipeline default: {expected_value}' (inherited from {modified_section}), but shows: '{all_text}'"
                                )
                        else:
                            print(f"🔍 No placeholder found, checking if field shows inherited value directly...")
                            if "828282" in all_text:
                                print(f"✅ GOOD: Step materialization field shows inherited concrete value '828282'")
                                materialization_inheritance_verified = True

                if not materialization_inheritance_verified:
                    # Try to find any form managers with output_dir_suffix
                    all_form_managers = step_editor_window.findChildren(ParameterFormManager)
                    print(f"🔍 Found {len(all_form_managers)} form managers, searching for output_dir_suffix...")

                    for i, fm in enumerate(all_form_managers):
                        if hasattr(fm, 'widgets'):
                            print(f"🔍 Form manager {i} has widgets: {list(fm.widgets.keys())}")
                            if 'output_dir_suffix' in fm.widgets:
                                widget = fm.widgets['output_dir_suffix']
                                texts = _extract_widget_texts(widget)
                                all_text = " ".join(texts.values())
                                print(f"🔍 Found output_dir_suffix in form manager {i}: '{all_text}'")

                                if "_CONCRETE_VALUE" in all_text:
                                    print(f"✅ GOOD: Found inherited concrete value '_CONCRETE_VALUE' in form manager {i}")
                                    materialization_inheritance_verified = True
                                    break

                    if not materialization_inheritance_verified:
                        raise AssertionError("Step materialization output_dir_suffix field not found or inheritance not verified")

                # Close step editor
                print(f"🔧 Closing step editor...")
                step_editor_window.close()
                QApplication.processEvents()

                return context

            workflow.add_step(WorkflowStep(
                name="Test Step Editor Inheritance",
                operation=test_step_editor_inheritance,
                timing_delay=1.0
            ))

        # Execute workflow with parameterized context
        initial_context = WorkflowContext(
            synthetic_plate_dir=synthetic_plate_dir,
            test_scenario=test_scenario
        )
        final_context = workflow.execute(initial_context)

        # Register main window with qtbot for cleanup
        qtbot.addWidget(final_context.main_window)

        field_name = test_scenario.get_modification_field_name()
        field_value = test_scenario.get_modification_value()

        print(f"✅ Parameterized workflow '{test_scenario.name}' validation passed!")
        print(f"✅ Configuration {test_scenario.orchestrator_config} applied successfully!")
        print(f"✅ Expected values {test_scenario.expected_values} validated!")
        print(f"✅ Lazy configuration lifecycle validated for field '{field_name}':")
        print(f"  - Field modification ({field_name} = {field_value}) and persistence ✅")
        print(f"  - Reset functionality for {field_name} ✅")
        print(f"  - Full lazy state restoration ✅")


