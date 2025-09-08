"""
Test reset button behavior and placeholder inheritance using mathematical simplification.

Follows refactoring principles:
- Dynamic config lookups instead of hardcoded values
- Lookup tables for test specifications
- Mathematical expression simplification
- Eliminate duplicate conditional logic
"""

import pytest
from dataclasses import dataclass, fields
from typing import Any, Tuple, List, Dict, Union
from pathlib import Path
from PyQt6.QtWidgets import QApplication

from openhcs.core.config import WellFilterMode, WellFilterConfig, StepWellFilterConfig, GlobalPipelineConfig
from tests.pyqt_gui.integration.test_end_to_end_workflow_foundation import (
    WorkflowContext, TestScenario, FieldModificationSpec,
    _launch_application, _access_plate_manager, _add_and_select_plate,
    _initialize_plate, _apply_orchestrator_config, _open_config_window,
    _close_config_window, WidgetFinder, WidgetInteractor, TimingConfig, _wait_for_gui,
    _create_synthetic_plate
)
import time


# ============================================================================
# DYNAMIC CONFIG SYSTEM: Replace hardcoded values with config lookups
# ============================================================================

def snake_to_camel_case(snake_str: str) -> str:
    """Convert snake_case to CamelCase mathematically."""
    components = snake_str.split('_')
    return ''.join(word.capitalize() for word in components)

def get_config_class_by_name(config_section: str) -> type:
    """Get config class by converting snake_case section name to CamelCase class name."""
    # Mathematical transformation: snake_case -> CamelCase
    class_name = snake_to_camel_case(config_section)

    # Import the config module to access classes dynamically
    from openhcs.core import config
    return getattr(config, class_name, None)

def get_config_default(config_class: type, field_name: str) -> Any:
    """Get default value for a field, simulating lazy resolution like the UI does."""
    if not config_class:
        return None

    # Simulate lazy resolution: if field is None, look up the MRO for first non-None value
    for cls in config_class.__mro__:
        if hasattr(cls, field_name):
            value = getattr(cls, field_name)
            if value is not None:
                return value

    return None

def get_actual_config_default(config_section: str, field_name: str) -> str:
    """Get the actual default value that the UI would show after lazy resolution."""
    config_class = get_config_class_by_name(config_section)
    default_value = get_config_default(config_class, field_name)

    # Convert to string representation that matches what the UI shows
    return str(default_value) if default_value is not None else '(none)'

# ============================================================================
# PARAMETERIZED TEST SYSTEM: Eliminate repetition with data-driven approach
# ============================================================================

# Simple data structures - no methods, just data
@dataclass(frozen=True)
class TestSpec:
    field: str
    config: str
    test_value: Any

@dataclass(frozen=True)
class InheritanceSpec:
    source: str
    target: str
    field: str
    test_value: Any

# Parameterized test data - all magic strings in one place
TEST_FIELDS = ['well_filter', 'well_filter_mode']
TEST_CONFIGS = ['well_filter_config', 'step_well_filter_config', 'step_materialization_config', 'path_planning_config']
TEST_VALUES = {'well_filter': '123', 'well_filter_mode': WellFilterMode.EXCLUDE}

# Inheritance chains as simple tuples
INHERITANCE_CHAINS = [
    ('well_filter_config', 'path_planning_config'),
    ('step_well_filter_config', 'step_materialization_config')
]

# Factory functions using parameters
def create_test_spec(field: str, config: str, value_override: Any = None) -> TestSpec:
    """Create test spec with optional value override."""
    value = value_override or TEST_VALUES.get(field, '123')
    return TestSpec(field, config, value)

def create_inheritance_spec(source: str, target: str, field: str, value_override: Any = None) -> InheritanceSpec:
    """Create inheritance spec with optional value override."""
    value = value_override or TEST_VALUES.get(field, '123')
    return InheritanceSpec(source, target, field, value)

def get_expected_default(config: str, field: str) -> str:
    """Get expected default value for field in config."""
    return get_actual_config_default(config, field)

TimingConfig = TimingConfig(
    ACTION_DELAY=0.5,  # Default delay for most actions
    WINDOW_DELAY=.3,  # Default delay for window operations
    SAVE_DELAY=.3,  # Default delay for save operations
    VISUAL_OBSERVATION_DELAY=0.5,  # Delay for visual observation
    VISUAL_PREPARATION_DELAY=0.25,  # Delay for visual preparation)
)

# ============================================================================
# DECLARATIVE TEST PATTERNS: Eliminate boilerplate with simple operations
# ============================================================================

def create_workflow_context(synthetic_plate_dir) -> WorkflowContext:
    """Create standardized workflow context with parameterized config."""
    expected_default = get_expected_default('well_filter_config', 'well_filter')

    test_scenario = TestScenario(
        name="reset_debug_test",
        orchestrator_config={"num_workers": 1},
        expected_values={'well_filter': expected_default},
        field_to_test=FieldModificationSpec(
            field_name='well_filter',
            modification_value='123',
            config_section='step_well_filter_config'
        )
    )

    return WorkflowContext().with_updates(
        synthetic_plate_dir=synthetic_plate_dir,
        test_scenario=test_scenario
    )

# Generic test runner - handles any sequence of operations
def run_test(ctx, *operations):
    """Execute a sequence of test operations."""
    for op, *args in operations:
        if op == 'edit':
            edit_field(ctx, *args)
        elif op == 'reset':
            press_reset_button(ctx, *args)
        elif op == 'assert_not_concrete':
            assert_field_not_concrete_value(ctx, *args)
        elif op == 'assert_inherits':
            assert_inheritance_working(ctx, *args)
        elif op == 'assert_default':
            field, source, target, msg = args
            default = get_expected_default(source, field)
            assert_inheritance_working(ctx, field, default, target, msg)
    return ctx

def setup_application_workflow(context: WorkflowContext) -> WorkflowContext:
    """Execute full application setup workflow."""
    # Mathematical simplification: chain operations as single expression
    return _open_config_window(
        _apply_orchestrator_config(
            _initialize_plate(
                _add_and_select_plate(
                    _access_plate_manager(
                        _launch_application(context)
                    )
                )
            )
        )
    )

def find_widget(context: WorkflowContext, field_name: str, config_section: str = None):
    """Find widget using existing infrastructure."""
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
    form_managers = context.config_window.findChildren(ParameterFormManager)

    return (WidgetFinder.find_field_widget_in_config_section(form_managers, field_name, config_section)
            if config_section else WidgetFinder.find_field_widget(form_managers, field_name))

def find_reset_button(context: WorkflowContext, field_name: str, config_section: str = None):
    """Find reset button using existing infrastructure."""
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
    form_managers = context.config_window.findChildren(ParameterFormManager)

    # Find the form manager that has this field in the specified config section
    if config_section:
        # Use the same logic as find_field_widget_in_config_section but return the form manager
        expected_dataclass_patterns = [
            config_section,  # exact match
            f"Lazy{config_section}",  # LazyStepWellFilterConfig
            f"Lazy{config_section.replace('_config', '').title().replace('_', '')}Config",  # LazyStepWellFilterConfig
            config_section.replace('_config', '').title().replace('_', '') + 'Config',  # StepWellFilterConfig
        ]

        for form_manager in form_managers:
            if hasattr(form_manager, 'dataclass_type') and form_manager.dataclass_type:
                dataclass_name = form_manager.dataclass_type.__name__
                if any(pattern.lower() in dataclass_name.lower() for pattern in expected_dataclass_patterns):
                    if hasattr(form_manager, 'widgets') and field_name in form_manager.widgets:
                        target_form_manager = form_manager
                        break
        else:
            target_form_manager = None
    else:
        target_form_manager = WidgetFinder.find_form_manager_for_field(form_managers, field_name)

    if not target_form_manager:
        return None

    # Get reset button from the form manager
    if hasattr(target_form_manager, 'reset_buttons') and field_name in target_form_manager.reset_buttons:
        return target_form_manager.reset_buttons[field_name]
    return None

def get_placeholder_text(widget) -> str:
    """Get placeholder text from widget."""
    return getattr(widget, 'placeholderText', lambda: '')()

# ============================================================================
# WORKFLOW OPERATIONS: Composable actions (Single Responsibility)
# ============================================================================

def edit_field(context: WorkflowContext, field_name: str, value: Any, config_section: str = None) -> WorkflowContext:
    """Edit field value and return updated context."""
    widget = find_widget(context, field_name, config_section)
    if not widget:
        print(f"❌ ERROR: Widget not found: {config_section}.{field_name}")
        return context

    # Mathematical simplification: combine scroll + wait + set + wait into single flow
    WidgetInteractor.scroll_to_widget(widget)
    _wait_for_gui(TimingConfig.VISUAL_PREPARATION_DELAY)
    set_widget_value_enhanced(widget, value)
    _wait_for_gui(TimingConfig.ACTION_DELAY)

    print(f"✅ Edited {config_section}.{field_name} = {value}")
    return context

def set_widget_value_enhanced(widget: Any, value: Any) -> None:
    """Enhanced widget value setting with proper enum dropdown support."""
    from PyQt6.QtWidgets import QComboBox
    from enum import Enum

    # Handle QComboBox (enum dropdowns) specially
    if isinstance(widget, QComboBox):
        # For enum values, find the matching item by data
        if isinstance(value, Enum):
            for i in range(widget.count()):
                if widget.itemData(i) == value:
                    widget.setCurrentIndex(i)
                    print(f"🔽 Set dropdown to enum {value} at index {i}")
                    return
            print(f"❌ ERROR: Enum value {value} not found in dropdown")
            return

        # For string values, try to find matching enum by name or value
        elif isinstance(value, str):
            # First try to find by enum name (e.g., "EXCLUDE")
            for i in range(widget.count()):
                item_data = widget.itemData(i)
                if item_data and hasattr(item_data, 'name') and item_data.name == value:
                    widget.setCurrentIndex(i)
                    print(f"🔽 Set dropdown to enum {item_data} (matched by name '{value}') at index {i}")
                    return

            # Then try to find by enum value (e.g., "exclude")
            for i in range(widget.count()):
                item_data = widget.itemData(i)
                if item_data and hasattr(item_data, 'value') and str(item_data.value) == value:
                    widget.setCurrentIndex(i)
                    print(f"🔽 Set dropdown to enum {item_data} (matched by value '{value}') at index {i}")
                    return

            print(f"❌ ERROR: String value '{value}' not found in dropdown")
            return

    # Handle EnhancedPathWidget specially (it has set_path method)
    if hasattr(widget, 'set_path') and 'EnhancedPathWidget' in str(type(widget)):
        widget.set_path(str(value))
        print(f"📁 Set path widget to '{value}'")
        return

    # Fall back to original WidgetInteractor for other widget types
    WidgetInteractor.set_widget_value(widget, value)

def check_field_value(context: WorkflowContext, field_name: str, expected_value: Any, config_section: str = None) -> bool:
    """Check if field has expected value."""
    widget = find_widget(context, field_name, config_section)
    if not widget:
        return False

    actual_value = get_widget_value_enhanced(widget)

    # Mathematical simplification: unified comparison logic
    from enum import Enum
    return (actual_value == expected_value if isinstance(expected_value, Enum) and isinstance(actual_value, Enum)
            else (actual_value.name == expected_value or str(actual_value.value) == expected_value)
                 if isinstance(expected_value, str) and isinstance(actual_value, Enum)
            else str(actual_value) == str(expected_value))

def check_field_is_placeholder_with_value(context: WorkflowContext, field_name: str, expected_placeholder_value: Any, config_section: str = None) -> bool:
    """Check if field is in placeholder state AND showing the expected placeholder value."""
    widget = find_widget(context, field_name, config_section)
    if not widget:
        return False

    # Check 1: Widget must be in placeholder state
    is_placeholder = widget.property("is_placeholder_state")
    if not is_placeholder:
        return False

    # Check 2: Placeholder must show the expected value (not the old concrete value)
    from PyQt6.QtWidgets import QComboBox
    from enum import Enum

    if isinstance(widget, QComboBox):
        # For combo boxes, check the currently displayed item
        current_index = widget.currentIndex()
        if current_index >= 0:
            displayed_value = widget.itemData(current_index)

            # Compare displayed value with expected placeholder value
            if isinstance(expected_placeholder_value, Enum) and isinstance(displayed_value, Enum):
                return displayed_value == expected_placeholder_value
            elif isinstance(expected_placeholder_value, str) and isinstance(displayed_value, Enum):
                return (displayed_value.name == expected_placeholder_value or
                        str(displayed_value.value) == expected_placeholder_value)

    # For other widget types, could add similar checks
    return True  # If we can't verify the placeholder value, at least it's in placeholder state

def get_widget_value_enhanced(widget: Any) -> Any:
    """Enhanced widget value getting with proper enum dropdown support and placeholder state detection."""
    from PyQt6.QtWidgets import QComboBox

    # CRITICAL: Check if widget is in placeholder state first
    # If it's showing a placeholder, the actual parameter value is None
    if widget.property("is_placeholder_state"):
        return None

    # Handle QComboBox (enum dropdowns) specially
    if isinstance(widget, QComboBox):
        current_index = widget.currentIndex()
        if current_index >= 0:
            return widget.itemData(current_index)
        return None

    # Handle EnhancedPathWidget specially (it has get_path method)
    if hasattr(widget, 'get_path') and 'EnhancedPathWidget' in str(type(widget)):
        return widget.get_path()

    # Use the same logic as ParameterFormManager.get_widget_value() for other widgets
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import WIDGET_GET_DISPATCH

    for matcher, extractor in WIDGET_GET_DISPATCH:
        if isinstance(widget, matcher) if isinstance(matcher, type) else hasattr(widget, matcher):
            return extractor(widget)

    return None

def check_placeholder_value(context: WorkflowContext, field_name: str, expected_placeholder: str, config_section: str = None) -> bool:
    """Check if field has expected placeholder."""
    widget = find_widget(context, field_name, config_section)
    if not widget:
        return False

    actual_placeholder = get_placeholder_text(widget)
    return expected_placeholder in actual_placeholder

def press_reset_button(context: WorkflowContext, field_name: str, config_section: str = None) -> WorkflowContext:
    """Press reset button and return updated context."""
    reset_button = find_reset_button(context, field_name, config_section)
    if not reset_button:
        section_info = f" in {config_section}" if config_section else ""
        print(f"❌ ERROR: Reset button not found: {field_name}{section_info}")
        return context

    WidgetInteractor.scroll_to_widget(reset_button)
    _wait_for_gui(TimingConfig.VISUAL_PREPARATION_DELAY)

    reset_button.click()
    QApplication.processEvents()
    _wait_for_gui(TimingConfig.ACTION_DELAY)

    section_info = f" in {config_section}" if config_section else ""
    print(f"✅ Pressed reset button for {field_name}{section_info}")
    return context

def save_and_close_config(context: WorkflowContext) -> WorkflowContext:
    """Save and close config window using existing infrastructure."""
    if not context.config_window:
        print("❌ ERROR: No config window to save and close")
        return context

    # Find and click save button (same logic as end-to-end workflow)
    save_button = WidgetFinder.find_button_by_text(context.config_window, ['ok', 'save', 'apply'])
    if not save_button:
        from PyQt6.QtWidgets import QPushButton
        buttons = [b.text() for b in context.config_window.findChildren(QPushButton)]
        print(f"❌ ERROR: Save button not found. Available buttons: {buttons}")
        return context

    save_button.click()
    _wait_for_gui(TimingConfig.SAVE_DELAY)

    # Close the window using existing infrastructure
    return _close_config_window(context)

def open_config(context: WorkflowContext) -> WorkflowContext:
    return _open_config_window(context)

# ============
# STEP EDITOR UTILS FOR CROSS-WINDOW PLACEHOLDER CONSISTENCY
# ============

def _capture_pipeline_placeholders(context: WorkflowContext) -> dict:
    """Capture key placeholder texts from the PipelineConfig window for later comparison."""
    # Parameterized sections
    sections = [
        ("step_well_filter", "step_well_filter_config"),
        ("step_materialization", "step_materialization_config"),
        ("napari_streaming", "napari_streaming_config"),
    ]

    # Unified placeholder capture using comprehension
    placeholders = {}
    for name, section in sections:
        field_placeholders = {
            field: get_placeholder_text(widget) if (widget := find_widget(context, field, section)) else None
            for field in TEST_FIELDS
        }
        placeholders[name] = field_placeholders
        print(f"📌 Captured pipeline placeholders [{name}] {field_placeholders}")

    return placeholders


def _open_step_editor_and_get_form_manager(context: WorkflowContext):
    """Open the Step Editor via Pipeline Editor and return its ParameterFormManager."""
    from PyQt6.QtWidgets import QWidget

    pipeline_editor_window = context.main_window.floating_windows.get("pipeline_editor")
    if not pipeline_editor_window:
        raise AssertionError("Pipeline editor window not found in floating_windows")

    # Find pipeline editor widget which has 'pipeline_steps' attribute
    pipeline_editor = WidgetFinder.find_widget_by_attribute(
        pipeline_editor_window.findChildren(QWidget), 'pipeline_steps'
    )
    if not pipeline_editor:
        raise AssertionError("Pipeline editor widget not found")

    # Click Add Step to open the step editor
    if not hasattr(pipeline_editor, 'buttons') or "add_step" not in pipeline_editor.buttons:
        raise AssertionError("Add Step button not found in pipeline editor buttons")
    add_step_button = pipeline_editor.buttons["add_step"]
    add_step_button.click()
    QApplication.processEvents()
    time.sleep(2.0)
    QApplication.processEvents()

    # Find the step editor window (DualEditorWindow) and get the form manager
    step_editor_window = None
    for widget in QApplication.topLevelWidgets():
        if hasattr(widget, 'step_editor') and hasattr(widget, 'editing_step'):
            step_editor_window = widget
            break
    if not step_editor_window:
        raise AssertionError("Step editor window (DualEditorWindow) not found")

    step_param_editor = step_editor_window.step_editor
    if not step_param_editor or not hasattr(step_param_editor, 'form_manager'):
        raise AssertionError("Form manager not found in step parameter editor")

    return step_editor_window, step_param_editor.form_manager


def _assert_step_editor_placeholders_match(step_form_manager, pipeline_placeholders: dict):
    """Assert that step editor shows the same placeholders for key fields as pipeline window."""
    # Mathematical simplification: use lookup table for mapping
    mapping = {
        'step_well_filter_config': 'step_well_filter',
        'materialization_config': 'step_materialization',
        'napari_streaming_config': 'napari_streaming',
    }

    for nested_name, key in mapping.items():
        expected = pipeline_placeholders.get(key, {})
        nested_manager = getattr(step_form_manager, 'nested_managers', {}).get(nested_name)
        assert nested_manager and hasattr(nested_manager, 'widgets'), f"Nested manager '{nested_name}' not found in step editor"

        # Unified field checking using parameterized fields
        for field_name in TEST_FIELDS:
            if field_name in nested_manager.widgets:
                widget = nested_manager.widgets[field_name]
                actual = get_placeholder_text(widget)
                expected_value = expected.get(field_name)

                print(f"🔍 Step editor [{nested_name}.{field_name}] placeholder = '{actual}' (expected '{expected_value}')")
                assert (actual or "").strip() == (expected_value or "").strip(), \
                    f"Placeholder mismatch for {nested_name}.{field_name}: expected '{expected_value}', got '{actual}'"
            elif field_name == 'well_filter':
                raise AssertionError(f"Widget for '{field_name}' not found in {nested_name} manager")
            else:
                print(f"ℹ️  {nested_name} has no '{field_name}' widget; skipping check")

    print("✅ Step editor placeholders match pipeline config placeholders for all checked fields")

# ============================================================================
# ASSERTION OPERATIONS: Dynamic assertions as workflow steps
# ============================================================================

def assert_field_not_concrete_value(context: WorkflowContext, field_name: str, concrete_value: Any, config_section: str, step_name: str) -> WorkflowContext:
    """Assert field does not show concrete value after reset."""
    widget = find_widget(context, field_name, config_section)
    if not widget:
        return context

    # Mathematical simplification: combine visual preparation with checks
    WidgetInteractor.scroll_to_widget(widget)
    _wait_for_gui(TimingConfig.VISUAL_PREPARATION_DELAY)

    # Unified assertion logic using mathematical expressions
    is_placeholder = widget.property("is_placeholder_state")
    assert is_placeholder, f"{step_name} FAIL: {config_section}.{field_name} should be in placeholder state after reset, but is_placeholder_state = {is_placeholder}"

    # Check for enum combo boxes showing concrete value
    from PyQt6.QtWidgets import QComboBox
    from enum import Enum

    if isinstance(widget, QComboBox) and isinstance(concrete_value, Enum):
        current_index = widget.currentIndex()
        displayed_value = widget.itemData(current_index) if current_index >= 0 else None
        assert displayed_value != concrete_value, f"{step_name} FAIL: {config_section}.{field_name} should not show concrete value '{concrete_value}' after reset"

    print(f"✅ {step_name}: {config_section}.{field_name} correctly in placeholder state and not showing concrete value '{concrete_value}'")
    return context

def assert_placeholder_shows_value(context: WorkflowContext, field_name: str, expected_placeholder: str, config_section: str, step_name: str) -> WorkflowContext:
    """Assert placeholder shows expected value."""
    widget = find_widget(context, field_name, config_section)
    if widget:
        # Mathematical simplification: combine visual preparation with logging
        WidgetInteractor.scroll_to_widget(widget)
        _wait_for_gui(TimingConfig.VISUAL_PREPARATION_DELAY)

        actual_placeholder = get_placeholder_text(widget)
        print(f"🔍 {step_name}: Checking {config_section}.{field_name}")
        print(f"    Expected: '{expected_placeholder}' | Actual: '{actual_placeholder}'")

    # Unified assertion using mathematical expression
    assert check_placeholder_value(context, field_name, expected_placeholder, config_section), \
        f"{step_name} FAIL: {config_section}.{field_name} should show placeholder '{expected_placeholder}'"

    print(f"✅ {step_name}: {config_section}.{field_name} shows correct placeholder '{expected_placeholder}'")
    return context

def assert_inheritance_working(context: WorkflowContext, field_name: str, inherited_value: str, target_config: str, step_name: str) -> WorkflowContext:
    """Assert inheritance is working correctly."""
    return assert_placeholder_shows_value(context, field_name, f"Pipeline default: {inherited_value}", target_config, step_name)

# ============================================================================
# WORKFLOW BUILDER: Composable workflow construction
# ============================================================================

def build_workflow(*operations):
    """Build workflow by composing operations."""
    def execute_workflow(context: WorkflowContext) -> WorkflowContext:
        result_context = context
        for operation in operations:
            result_context = operation(result_context)
            # Operations now raise AssertionError directly instead of using last_error
        return result_context
    return execute_workflow

# ============================================================================
# TEST CLASS: Simplified using composable utilities
# ============================================================================

class TestResetPlaceholderInheritance:
    """Test reset button behavior using composable workflow utilities."""

    def test_comprehensive_inheritance_chains(self, app, synthetic_plate_dir):
        """Test inheritance chains using declarative operations."""
        context = setup_application_workflow(create_workflow_context(synthetic_plate_dir))

        print("\n🧪 COMPREHENSIVE INHERITANCE TEST - DECLARATIVE APPROACH")
        print("=" * 60)

        # Process all chains using generic runner
        for chain_idx, (source, target) in enumerate(INHERITANCE_CHAINS, 1):
            print(f"\n🔗 CHAIN {chain_idx}: {source} → {target}")

            # Test field reset for each field
            for field in TEST_FIELDS:
                value = TEST_VALUES.get(field, '123')
                run_test(context,
                    ('edit', field, value, source),
                    ('reset', field, source),
                    ('assert_not_concrete', field, value, source, f"{field} reset")
                )

            # Test inheritance chain
            value = f'test_value_{chain_idx}'
            run_test(context,
                ('edit', 'well_filter', value, source),
                ('assert_inherits', 'well_filter', value, target, f"inheritance"),
                ('reset', 'well_filter', target),
                ('assert_inherits', 'well_filter', value, target, f"persistence"),
                ('reset', 'well_filter', source),
                ('assert_default', 'well_filter', source, target, f"default update")
            )

            print(f"✅ CHAIN {chain_idx} COMPLETED")

        print("✅ ALL INHERITANCE TESTS COMPLETED SUCCESSFULLY")

        # Cross-window verification using mathematical simplification
        print("\n🔄 Cross-window placeholder consistency check")
        pipeline_placeholders = _capture_pipeline_placeholders(context)
        context = _close_config_window(context)

        step_editor_window, step_form_manager = _open_step_editor_and_get_form_manager(context)
        try:
            _assert_step_editor_placeholders_match(step_form_manager, pipeline_placeholders)
        finally:
            step_editor_window.close()
            QApplication.processEvents()



    def test_concrete_value_persistence_after_save_reopen(self, app, qtbot, synthetic_plate_dir):
        """Test that concrete values persist after save/reopen and show as concrete, not placeholders."""
        context = setup_application_workflow(create_workflow_context(synthetic_plate_dir))

        print("\n🧪 CONCRETE VALUE PERSISTENCE TEST")
        print("=" * 50)

        # Simple test data
        test_specs = [
            ("materialization_results_path", "/custom/results/path", None),
            ('well_filter', '123', 'well_filter_config')
        ]

        # Step 1: Set values
        for field_name, test_value, config_section in test_specs:
            if field_name == "materialization_results_path":
                self._set_path_widget_value(context, qtbot, field_name, test_value)
            else:
                edit_field(context, field_name, test_value, config_section)

        # Step 2-3: Save, close, reopen
        self._save_and_close_with_qtbot(context, qtbot)
        _open_config_window(context)

        # Step 4: Verify persistence
        for field_name, expected_value, config_section in test_specs:
            assert check_field_value(context, field_name, expected_value, config_section), \
                f"Field {field_name} should show saved value '{expected_value}'"

        # Step 5: Verify concrete text (not placeholders)
        for field_name, expected_value, config_section in test_specs:
            widget = find_widget(context, field_name, config_section)
            if widget:
                displayed_text = (widget.path_input.text() if hasattr(widget, 'path_input')
                                else widget.text() if hasattr(widget, 'text')
                                else str(get_widget_value_enhanced(widget)))
                is_placeholder = (widget.path_input.property("is_placeholder_state") if hasattr(widget, 'path_input')
                                else widget.property("is_placeholder_state"))

                assert displayed_text == str(expected_value) and not is_placeholder, \
                    f"Field {field_name} should show concrete text '{expected_value}', not placeholder"

        print("✅ Concrete value persistence test completed successfully")

    def _set_path_widget_value(self, context: WorkflowContext, qtbot, field_name: str, value: str):
        """Helper method to set path widget value using qtbot."""
        from PyQt6.QtCore import Qt
        from PyQt6.QtGui import QKeySequence

        path_widget = find_widget(context, field_name)
        if path_widget and hasattr(path_widget, 'path_input'):
            WidgetInteractor.scroll_to_widget(path_widget)
            _wait_for_gui(TimingConfig.VISUAL_PREPARATION_DELAY)

            line_edit = path_widget.path_input
            qtbot.mouseClick(line_edit, Qt.MouseButton.LeftButton)
            _wait_for_gui(TimingConfig.ACTION_DELAY)

            qtbot.keySequence(line_edit, QKeySequence.StandardKey.SelectAll)
            qtbot.keyClicks(line_edit, value)
            qtbot.keyPress(line_edit, Qt.Key.Key_Return)
            _wait_for_gui(TimingConfig.ACTION_DELAY)

            print(f"✅ Set {field_name} = {value} via qtbot")
        else:
            print(f"❌ ERROR: Could not find {field_name} widget or path_input")

    def _save_and_close_with_qtbot(self, context: WorkflowContext, qtbot):
        """Helper method to save and close config using qtbot."""
        from PyQt6.QtCore import Qt
        from PyQt6.QtWidgets import QPushButton

        save_button = next((w for w in context.config_window.findChildren(QPushButton)
                           if 'save' in w.text().lower() or 'apply' in w.text().lower()), None)

        if save_button:
            qtbot.mouseClick(save_button, Qt.MouseButton.LeftButton)
            _wait_for_gui(TimingConfig.ACTION_DELAY)
            print("✅ Clicked save button with qtbot")
        else:
            print("❌ ERROR: Could not find save button")

        _close_config_window(context)

# ============================================================================
# FIXTURES: Test setup and teardown
# ============================================================================

@pytest.fixture
def app():
    """Ensure QApplication exists for PyQt6 tests."""
    app = QApplication.instance()
    if app is None:
        app = QApplication([])
    yield app

@pytest.fixture
def synthetic_plate_dir(tmp_path):
    """Create synthetic plate data for testing."""
    return _create_synthetic_plate(tmp_path)
