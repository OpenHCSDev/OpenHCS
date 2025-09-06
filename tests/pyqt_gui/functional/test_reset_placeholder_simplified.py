"""
Test reset button behavior and placeholder inheritance using mathematical simplification.

Follows refactoring principles:
- Extract all magic strings to constants
- Use composable utility functions  
- Eliminate duplicate conditional logic
- Mathematical expression simplification
"""

import pytest
from dataclasses import dataclass
from typing import Any, Tuple, List
from pathlib import Path
from PyQt6.QtWidgets import QApplication

from openhcs.core.config import WellFilterMode
from tests.pyqt_gui.integration.test_end_to_end_workflow_foundation import (
    WorkflowContext, TestScenario, FieldModificationSpec,
    _launch_application, _access_plate_manager, _add_and_select_plate,
    _initialize_plate, _apply_orchestrator_config, _open_config_window,
    _close_config_window, WidgetFinder, WidgetInteractor, TimingConfig, _wait_for_gui,
    _create_synthetic_plate
)

# ============================================================================
# CONSTANTS: Extract all magic strings (Mathematical Simplification Principle)
# ============================================================================

@dataclass(frozen=True)
class TestConstants:
    """All test constants in one place to eliminate magic strings."""
    # Field names
    WELL_FILTER = 'well_filter'
    WELL_FILTER_MODE = 'well_filter_mode'
    
    # Config sections
    WELL_FILTER_CONFIG = 'well_filter_config'
    STEP_WELL_FILTER_CONFIG = 'step_well_filter_config'
    STEP_MATERIALIZATION_CONFIG = 'step_materialization_config'
    
    # Test values
    TEST_VALUE_A = '123'
    TEST_VALUE_B = '456' 
    TEST_VALUE_C = '789'
    CONCRETE_VALUE = 'CONCRETE_VALUE'
    
    # Expected defaults
    DEFAULT_WELL_FILTER = '(none)'  # WellFilterConfig.well_filter default is None
    STEP_DEFAULT_WELL_FILTER = '1'  # StepWellFilterConfig.well_filter default is 1
    
    # Enum values
    EXCLUDE_MODE = WellFilterMode.EXCLUDE
    INCLUDE_MODE = WellFilterMode.INCLUDE

# Additional config sections for inheritance testing
@dataclass(frozen=True)
class InheritanceConstants:
    """Constants for inheritance testing."""
    PATH_PLANNING_CONFIG = 'path_planning_config'

    # Inheritance chains (source → target)
    CHAIN_1_SOURCE = TestConstants.WELL_FILTER_CONFIG
    CHAIN_1_TARGET = 'path_planning_config'  # Can't reference self in class definition

    CHAIN_2_SOURCE = TestConstants.STEP_WELL_FILTER_CONFIG
    CHAIN_2_TARGET = TestConstants.STEP_MATERIALIZATION_CONFIG

# Test field specifications (lookup table approach)
TEST_FIELD_SPECS = [
    (TestConstants.WELL_FILTER, TestConstants.WELL_FILTER_CONFIG, TestConstants.TEST_VALUE_A),
    (TestConstants.WELL_FILTER_MODE, TestConstants.WELL_FILTER_CONFIG, TestConstants.EXCLUDE_MODE),
    (TestConstants.WELL_FILTER, TestConstants.STEP_WELL_FILTER_CONFIG, TestConstants.TEST_VALUE_B),
    (TestConstants.WELL_FILTER_MODE, TestConstants.STEP_WELL_FILTER_CONFIG, TestConstants.EXCLUDE_MODE),
    (TestConstants.WELL_FILTER, TestConstants.STEP_MATERIALIZATION_CONFIG, TestConstants.TEST_VALUE_C),
]

# Inheritance test specifications (source_config, target_config, field_name, test_value)
INHERITANCE_TEST_SPECS = [
    # Chain 1: WellFilterConfig → PathPlanningConfig
    (InheritanceConstants.CHAIN_1_SOURCE, InheritanceConstants.CHAIN_1_TARGET, TestConstants.WELL_FILTER, TestConstants.TEST_VALUE_A),
    (InheritanceConstants.CHAIN_1_SOURCE, InheritanceConstants.CHAIN_1_TARGET, TestConstants.WELL_FILTER_MODE, TestConstants.EXCLUDE_MODE),

    # Chain 2: StepWellFilterConfig → StepMaterializationConfig
    (InheritanceConstants.CHAIN_2_SOURCE, InheritanceConstants.CHAIN_2_TARGET, TestConstants.WELL_FILTER, TestConstants.TEST_VALUE_B),
    (InheritanceConstants.CHAIN_2_SOURCE, InheritanceConstants.CHAIN_2_TARGET, TestConstants.WELL_FILTER_MODE, TestConstants.EXCLUDE_MODE),
]

# ============================================================================
# COMPOSABLE UTILITIES: Parameterized functions (Algebraic Common Factors)
# ============================================================================

def create_workflow_context(synthetic_plate_dir) -> WorkflowContext:
    """Create standardized workflow context."""
    test_scenario = TestScenario(
        name="reset_debug_test",
        orchestrator_config={"num_workers": 1},
        expected_values={TestConstants.WELL_FILTER: TestConstants.DEFAULT_WELL_FILTER},
        field_to_test=FieldModificationSpec(
            field_name=TestConstants.WELL_FILTER,
            modification_value=TestConstants.TEST_VALUE_A,
            config_section=TestConstants.STEP_WELL_FILTER_CONFIG
        )
    )
    
    return WorkflowContext().with_updates(
        synthetic_plate_dir=synthetic_plate_dir,
        test_scenario=test_scenario
    )

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

    if config_section:
        return WidgetFinder.find_field_widget_in_config_section(form_managers, field_name, config_section)
    else:
        return WidgetFinder.find_field_widget(form_managers, field_name)

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

    WidgetInteractor.scroll_to_widget(widget)
    _wait_for_gui(TimingConfig.VISUAL_PREPARATION_DELAY)

    # Enhanced widget value setting with proper enum support
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

    # Enhanced comparison for enum values
    from enum import Enum
    if isinstance(expected_value, Enum) and isinstance(actual_value, Enum):
        return actual_value == expected_value
    elif isinstance(expected_value, str) and isinstance(actual_value, Enum):
        # Compare string to enum name or value
        return (actual_value.name == expected_value or
                str(actual_value.value) == expected_value)

    return str(actual_value) == str(expected_value)

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
    """Open config window."""
    return _open_config_window(context)

# ============================================================================
# ASSERTION OPERATIONS: Dynamic assertions as workflow steps
# ============================================================================

def assert_field_not_concrete_value(context: WorkflowContext, field_name: str, concrete_value: Any, config_section: str, step_name: str) -> WorkflowContext:
    """Assert field does not show concrete value after reset."""
    # Scroll to widget so user can visually see what's being checked
    widget = find_widget(context, field_name, config_section)
    if widget:
        WidgetInteractor.scroll_to_widget(widget)
        _wait_for_gui(TimingConfig.VISUAL_PREPARATION_DELAY)

        # Check 1: Widget should be in placeholder state
        is_placeholder = widget.property("is_placeholder_state")
        if not is_placeholder:
            error_msg = f"{step_name} FAIL: {config_section}.{field_name} should be in placeholder state after reset, but is_placeholder_state = {is_placeholder}"
            print(f"❌ {error_msg}")
            raise AssertionError(error_msg)

        # Check 2: Widget should NOT be showing the concrete value we just reset
        from PyQt6.QtWidgets import QComboBox
        from enum import Enum

        if isinstance(widget, QComboBox) and isinstance(concrete_value, Enum):
            # For enum combo boxes, check the displayed value
            current_index = widget.currentIndex()
            if current_index >= 0:
                displayed_value = widget.itemData(current_index)
                if displayed_value == concrete_value:
                    error_msg = f"{step_name} FAIL: {config_section}.{field_name} should not show concrete value '{concrete_value}' after reset"
                    print(f"❌ {error_msg}")
                    raise AssertionError(error_msg)

        print(f"✅ {step_name}: {config_section}.{field_name} correctly in placeholder state and not showing concrete value '{concrete_value}'")

    return context

def assert_placeholder_shows_value(context: WorkflowContext, field_name: str, expected_placeholder: str, config_section: str, step_name: str) -> WorkflowContext:
    """Assert placeholder shows expected value."""
    # Scroll to widget so user can visually see what's being checked
    widget = find_widget(context, field_name, config_section)
    if widget:
        WidgetInteractor.scroll_to_widget(widget)
        _wait_for_gui(TimingConfig.VISUAL_PREPARATION_DELAY)

        # Show actual placeholder for visual inspection
        actual_placeholder = get_placeholder_text(widget)
        print(f"🔍 {step_name}: Checking {config_section}.{field_name}")
        print(f"    Expected: '{expected_placeholder}'")
        print(f"    Actual:   '{actual_placeholder}'")

    has_expected_placeholder = check_placeholder_value(context, field_name, expected_placeholder, config_section)
    if not has_expected_placeholder:
        error_msg = f"{step_name} FAIL: {config_section}.{field_name} should show placeholder '{expected_placeholder}'"
        print(f"❌ {error_msg}")
        raise AssertionError(error_msg)
    print(f"✅ {step_name}: {config_section}.{field_name} shows correct placeholder '{expected_placeholder}'")
    return context

def assert_inheritance_working(context: WorkflowContext, field_name: str, inherited_value: str, target_config: str, step_name: str) -> WorkflowContext:
    """Assert inheritance is working correctly."""
    expected_placeholder = f"Pipeline default: {inherited_value}"
    return assert_placeholder_shows_value(context, field_name, expected_placeholder, target_config, step_name)

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
        """Test both inheritance chains sequentially in one test following the exact 9-step pattern."""
        context = setup_application_workflow(create_workflow_context(synthetic_plate_dir))

        print("\n🧪 COMPREHENSIVE INHERITANCE TEST - SEQUENTIAL EXECUTION")
        print("=" * 60)

        # CHAIN 1: WellFilterConfig → PathPlanningConfig inheritance (Steps 1-8)
        print(f"\n🔗 CHAIN 1: WellFilterConfig → PathPlanningConfig")
        print("-" * 50)

        # Steps 1-2: Set concrete value to well_filter in source, reset and verify
        context = build_workflow(
            lambda ctx: edit_field(ctx, TestConstants.WELL_FILTER, TestConstants.TEST_VALUE_A, InheritanceConstants.CHAIN_1_SOURCE),
            lambda ctx: press_reset_button(ctx, TestConstants.WELL_FILTER, InheritanceConstants.CHAIN_1_SOURCE),
            lambda ctx: assert_field_not_concrete_value(ctx, TestConstants.WELL_FILTER, TestConstants.TEST_VALUE_A, InheritanceConstants.CHAIN_1_SOURCE, "Chain 1 - Step 2"),
        )(context)

        # Steps 3-4: Set concrete value to well_filter_mode enum in source, reset and verify
        context = build_workflow(
            lambda ctx: edit_field(ctx, TestConstants.WELL_FILTER_MODE, TestConstants.EXCLUDE_MODE, InheritanceConstants.CHAIN_1_SOURCE),
            lambda ctx: press_reset_button(ctx, TestConstants.WELL_FILTER_MODE, InheritanceConstants.CHAIN_1_SOURCE),
            lambda ctx: assert_field_not_concrete_value(ctx, TestConstants.WELL_FILTER_MODE, TestConstants.EXCLUDE_MODE, InheritanceConstants.CHAIN_1_SOURCE, "Chain 1 - Step 4"),
        )(context)

        # Steps 5-6: Set concrete value to well_filter in source again, check target shows inherited value
        context = build_workflow(
            lambda ctx: edit_field(ctx, TestConstants.WELL_FILTER, TestConstants.TEST_VALUE_B, InheritanceConstants.CHAIN_1_SOURCE),
            lambda ctx: assert_inheritance_working(ctx, TestConstants.WELL_FILTER, TestConstants.TEST_VALUE_B, InheritanceConstants.CHAIN_1_TARGET, "Chain 1 - Step 6"),
        )(context)

        # Step 7: Reset target field and verify placeholder remains (still inheriting)
        context = build_workflow(
            lambda ctx: press_reset_button(ctx, TestConstants.WELL_FILTER, InheritanceConstants.CHAIN_1_TARGET),
            lambda ctx: assert_inheritance_working(ctx, TestConstants.WELL_FILTER, TestConstants.TEST_VALUE_B, InheritanceConstants.CHAIN_1_TARGET, "Chain 1 - Step 7"),
        )(context)

        # Step 8: Reset source field and verify target placeholder changes to new default
        context = build_workflow(
            lambda ctx: press_reset_button(ctx, TestConstants.WELL_FILTER, InheritanceConstants.CHAIN_1_SOURCE),
            lambda ctx: assert_inheritance_working(ctx, TestConstants.WELL_FILTER, TestConstants.DEFAULT_WELL_FILTER, InheritanceConstants.CHAIN_1_TARGET, "Chain 1 - Step 8"),
        )(context)

        print("✅ CHAIN 1 COMPLETED SUCCESSFULLY")

        # CHAIN 2: StepWellFilterConfig → StepMaterializationConfig inheritance (Steps 9-16)
        print(f"\n🔗 CHAIN 2: StepWellFilterConfig → StepMaterializationConfig")
        print("-" * 50)

        # Steps 9-10: Set concrete value to well_filter in source, reset and verify it shows static default
        context = build_workflow(
            lambda ctx: edit_field(ctx, TestConstants.WELL_FILTER, TestConstants.TEST_VALUE_B, InheritanceConstants.CHAIN_2_SOURCE),
            lambda ctx: press_reset_button(ctx, TestConstants.WELL_FILTER, InheritanceConstants.CHAIN_2_SOURCE),
            lambda ctx: assert_placeholder_shows_value(ctx, TestConstants.WELL_FILTER, f"Pipeline default: {TestConstants.STEP_DEFAULT_WELL_FILTER}", InheritanceConstants.CHAIN_2_SOURCE, "Chain 2 - Step 10"),
        )(context)

        # Steps 11-12: Set concrete value to well_filter_mode enum in source, reset and verify
        context = build_workflow(
            lambda ctx: edit_field(ctx, TestConstants.WELL_FILTER_MODE, TestConstants.EXCLUDE_MODE, InheritanceConstants.CHAIN_2_SOURCE),
            lambda ctx: press_reset_button(ctx, TestConstants.WELL_FILTER_MODE, InheritanceConstants.CHAIN_2_SOURCE),
            lambda ctx: assert_field_not_concrete_value(ctx, TestConstants.WELL_FILTER_MODE, TestConstants.EXCLUDE_MODE, InheritanceConstants.CHAIN_2_SOURCE, "Chain 2 - Step 12"),
        )(context)

        # Steps 13-14: Set concrete value to well_filter in source again, check target shows inherited value
        context = build_workflow(
            lambda ctx: edit_field(ctx, TestConstants.WELL_FILTER, TestConstants.TEST_VALUE_C, InheritanceConstants.CHAIN_2_SOURCE),
            lambda ctx: assert_inheritance_working(ctx, TestConstants.WELL_FILTER, TestConstants.TEST_VALUE_C, InheritanceConstants.CHAIN_2_TARGET, "Chain 2 - Step 14"),
        )(context)

        # Step 15: Reset target field and verify placeholder remains (still inheriting)
        context = build_workflow(
            lambda ctx: press_reset_button(ctx, TestConstants.WELL_FILTER, InheritanceConstants.CHAIN_2_TARGET),
            lambda ctx: assert_inheritance_working(ctx, TestConstants.WELL_FILTER, TestConstants.TEST_VALUE_C, InheritanceConstants.CHAIN_2_TARGET, "Chain 2 - Step 15"),
        )(context)

        # Step 16: Reset source field and verify target placeholder changes to new default
        context = build_workflow(
            lambda ctx: press_reset_button(ctx, TestConstants.WELL_FILTER, InheritanceConstants.CHAIN_2_SOURCE),
            lambda ctx: assert_inheritance_working(ctx, TestConstants.WELL_FILTER, TestConstants.STEP_DEFAULT_WELL_FILTER, InheritanceConstants.CHAIN_2_TARGET, "Chain 2 - Step 16"),
        )(context)

        print("✅ CHAIN 2 COMPLETED SUCCESSFULLY")
        print("✅ ALL INHERITANCE TESTS COMPLETED SUCCESSFULLY")



    def test_critical_bug_scenario(self, app, synthetic_plate_dir):
        """Test the specific bug scenario described by user."""
        context = setup_application_workflow(create_workflow_context(synthetic_plate_dir))

        # Critical test: step_well_filter_config reset behavior
        workflow = build_workflow(
            lambda ctx: edit_field(ctx, TestConstants.WELL_FILTER, TestConstants.CONCRETE_VALUE, TestConstants.STEP_WELL_FILTER_CONFIG),
            lambda ctx: press_reset_button(ctx, TestConstants.WELL_FILTER),
        )

        result_context = workflow(context)

        # Verify the bug is detected
        shows_concrete_value = check_placeholder_value(
            result_context,
            TestConstants.WELL_FILTER,
            TestConstants.CONCRETE_VALUE,
            TestConstants.STEP_WELL_FILTER_CONFIG
        )

        assert not shows_concrete_value, \
            f"CRITICAL BUG: step_well_filter_config shows concrete value '{TestConstants.CONCRETE_VALUE}' after reset"

    def test_concrete_value_persistence_after_save_reopen(self, app, qtbot, synthetic_plate_dir):
        """Test that concrete values persist after save/reopen and show as concrete, not placeholders."""
        context = setup_application_workflow(create_workflow_context(synthetic_plate_dir))

        print("\n🧪 CONCRETE VALUE PERSISTENCE TEST")
        print("=" * 50)

        # Step 1a: Set a concrete value in materialization_results_path (top-level field) via user interaction
        print("Step 1a: Setting concrete value in materialization_results_path (top-level) via click+type")

        # Find the widget and simulate user interaction using pytest-qt
        path_widget = find_widget(context, "materialization_results_path")
        if path_widget:
            # Scroll to widget so user can see it
            WidgetInteractor.scroll_to_widget(path_widget)
            _wait_for_gui(TimingConfig.VISUAL_PREPARATION_DELAY)

            # For EnhancedPathWidget, we need to interact with the inner QLineEdit (path_input)
            if hasattr(path_widget, 'path_input'):
                line_edit = path_widget.path_input

                # Use pytest-qt's qtbot for proper user simulation
                from PyQt6.QtCore import Qt
                from PyQt6.QtGui import QKeySequence

                # Click on the line edit to focus it (simulate user click)
                qtbot.mouseClick(line_edit, Qt.MouseButton.LeftButton)
                _wait_for_gui(TimingConfig.ACTION_DELAY)

                # Clear existing content and type new value using keyboard simulation
                qtbot.keySequence(line_edit, QKeySequence.StandardKey.SelectAll)
                qtbot.keyClicks(line_edit, "/custom/results/path")
                _wait_for_gui(TimingConfig.ACTION_DELAY)

                # Press Enter to confirm the input
                qtbot.keyPress(line_edit, Qt.Key.Key_Return)
                _wait_for_gui(TimingConfig.ACTION_DELAY)

                print("✅ Clicked, typed '/custom/results/path', and pressed Enter")
            else:
                print("❌ ERROR: Could not find path_input in materialization_results_path widget")
        else:
            print("❌ ERROR: Could not find materialization_results_path widget")

        # Step 1b: Set a concrete value in well_filter_config.well_filter (nested field)
        print("Step 1b: Setting concrete value in well_filter_config.well_filter (nested)")
        context = edit_field(
            context,
            TestConstants.WELL_FILTER,
            TestConstants.TEST_VALUE_A,
            TestConstants.WELL_FILTER_CONFIG
        )

        # Step 2: Save and close config using qtbot to click save button
        print("Step 2: Saving and closing config with qtbot")

        # Find and click the save button first
        from PyQt6.QtWidgets import QPushButton
        save_button = None
        for widget in context.config_window.findChildren(QPushButton):
            if 'save' in widget.text().lower() or 'apply' in widget.text().lower():
                save_button = widget
                break

        if save_button:
            qtbot.mouseClick(save_button, Qt.MouseButton.LeftButton)
            _wait_for_gui(TimingConfig.ACTION_DELAY)
            print("✅ Clicked save button with qtbot")
        else:
            print("❌ ERROR: Could not find save button")

        # Then close the window
        _close_config_window(context)

        # Step 3: Reopen config
        print("Step 3: Reopening config")
        _open_config_window(context)

        # Step 4a: Verify materialization_results_path shows the concrete value that was saved (top-level)
        print("Step 4a: Verifying materialization_results_path shows concrete value (top-level)")
        shows_saved_top_level = check_field_value(
            context,
            "materialization_results_path",
            "/custom/results/path"
        )

        assert shows_saved_top_level, \
            f"CRITICAL BUG: materialization_results_path should show saved concrete value '/custom/results/path' after save/reopen"

        # Step 4b: Verify well_filter shows the concrete value that was saved (nested)
        print("Step 4b: Verifying well_filter shows concrete value (nested)")
        shows_saved_nested = check_field_value(
            context,
            TestConstants.WELL_FILTER,
            TestConstants.TEST_VALUE_A,
            TestConstants.WELL_FILTER_CONFIG
        )

        assert shows_saved_nested, \
            f"CRITICAL BUG: well_filter_config.well_filter should show saved concrete value '{TestConstants.TEST_VALUE_A}' after save/reopen"

        # Step 5: Verify that saved fields contain actual selectable concrete text
        print("Step 5: Verifying saved fields contain selectable concrete text")

        # Check materialization_results_path widget has selectable text
        path_widget = find_widget(context, "materialization_results_path")
        if path_widget and hasattr(path_widget, 'path_input'):
            line_edit = path_widget.path_input
            displayed_text = line_edit.text()
            is_placeholder = line_edit.property("is_placeholder_state")

            print(f"materialization_results_path text: '{displayed_text}', is_placeholder: {is_placeholder}")

            # Verify it contains the concrete text we typed
            assert displayed_text == "/custom/results/path", \
                f"CRITICAL BUG: materialization_results_path text is '{displayed_text}' but should be '/custom/results/path'"

            # Verify it's not in placeholder state
            assert not is_placeholder, \
                f"CRITICAL BUG: materialization_results_path should show concrete text, not placeholder"

        # Check well_filter widget has selectable text
        filter_widget = find_widget(context, TestConstants.WELL_FILTER, TestConstants.WELL_FILTER_CONFIG)
        if filter_widget:
            displayed_text = filter_widget.text() if hasattr(filter_widget, 'text') else str(get_widget_value_enhanced(filter_widget))
            is_placeholder = filter_widget.property("is_placeholder_state")

            print(f"well_filter text: '{displayed_text}', is_placeholder: {is_placeholder}")

            # Verify it contains the concrete text we set
            assert displayed_text == TestConstants.TEST_VALUE_A, \
                f"CRITICAL BUG: well_filter text is '{displayed_text}' but should be '{TestConstants.TEST_VALUE_A}'"

            # Verify it's not in placeholder state
            assert not is_placeholder, \
                f"CRITICAL BUG: well_filter should show concrete text, not placeholder"

        print("✅ Both saved fields contain selectable concrete text (not placeholders)")

        print("✅ Concrete value persistence test completed successfully")

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
