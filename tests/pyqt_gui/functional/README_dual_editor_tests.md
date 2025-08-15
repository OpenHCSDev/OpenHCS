# Dual Editor Reset Functionality Tests

This directory contains comprehensive tests for the dual editor reset functionality in the PyQt6 GUI.

## Test Coverage

### 1. Core Reset Functionality (`test_dual_editor_reset_functionality.py`)

Tests the fundamental reset behavior across both step editor and function pattern editor:

- **Step Parameter Editor Reset**:
  - Individual parameter reset
  - Reset all parameters
  - Enum widget reset (GroupBy, VariableComponents)
  - Parameter state validation

- **Function Pane Reset**:
  - Reset all parameters functionality
  - Enhanced form manager integration
  - Widget state consistency after reset
  - Signal emission verification

- **Dual Editor Integration**:
  - Step tab reset functionality
  - Function tab reset functionality
  - Cross-tab state isolation

- **Placeholder Text Behavior**:
  - Lazy dataclass placeholder display
  - String field placeholder behavior
  - Enum field placeholder styling

### 2. Widget-Specific Validation (`test_dual_editor_widget_validation.py`)

Tests individual widget types to ensure proper reset behavior:

- **Widget Type Tests**:
  - QComboBox (enum fields) - placeholder styling, default selection
  - QLineEdit (string fields) - text clearing, placeholder text
  - QCheckBox (boolean fields) - state reset to defaults
  - QSpinBox/QDoubleSpinBox (numeric fields) - value reset

- **State Consistency Tests**:
  - Form manager and widget synchronization
  - Nested widget reset consistency
  - Parameter value vs. widget state alignment

- **Reset Button Integration**:
  - Individual parameter reset buttons
  - Reset all parameters button
  - Button behavior validation

### 3. Window Integration (`test_dual_editor_window_integration.py`)

Tests the complete dual editor window workflow:

- **Component Integration**:
  - Step editor component reset
  - Function editor component reset
  - Tab switching with state preservation

- **Signal Handling**:
  - Reset operation signaling
  - Event propagation
  - Error handling during reset

- **Cross-Tab Consistency**:
  - State isolation between tabs
  - Reset operation independence
  - UI state preservation

## Running the Tests

### Run All Tests
```bash
python tests/pyqt_gui/functional/test_runner_dual_editor.py
```

### Run Specific Test Categories
```bash
# Reset functionality tests
python tests/pyqt_gui/functional/test_runner_dual_editor.py --category reset

# Widget validation tests  
python tests/pyqt_gui/functional/test_runner_dual_editor.py --category widgets

# Integration tests
python tests/pyqt_gui/functional/test_runner_dual_editor.py --category integration
```

### Run with Coverage
```bash
python tests/pyqt_gui/functional/test_runner_dual_editor.py --coverage
```

### Run Individual Test Files
```bash
# Using pytest directly
pytest tests/pyqt_gui/functional/test_dual_editor_reset_functionality.py -v
pytest tests/pyqt_gui/functional/test_dual_editor_widget_validation.py -v
pytest tests/pyqt_gui/functional/test_dual_editor_window_integration.py -v
```

## Test Environment Setup

The tests require:
- PyQt6 installed
- QApplication instance (handled by fixtures)
- Headless display for CI (set via `QT_QPA_PLATFORM=offscreen`)

## Key Test Scenarios

### 1. Form Manager Integration
Tests verify that the dual editor components properly use the correct form managers:
- Function panes use enhanced PyQt6 form manager
- Step editors use PyQt6 parameter form manager
- Reset operations target the correct form manager instance

### 2. Widget State Validation
Tests ensure widgets properly reflect reset state:
- Enum dropdowns show default values with placeholder styling
- Text fields are cleared and show placeholder text
- Checkboxes return to default checked state
- Numeric fields reset to default values

### 3. Placeholder Behavior
Tests validate lazy dataclass placeholder functionality:
- Form manager stores `None` for reset parameters
- Widgets display resolved defaults with placeholder styling
- Placeholder text and styling are properly applied
- Reset operations preserve lazy context behavior

### 4. Error Handling
Tests verify robust error handling:
- Fallback to manual reset if form manager reset fails
- Graceful handling of missing widgets or parameters
- Signal emission even during error conditions

## Test Fixtures

- `qapp`: QApplication instance for PyQt widgets
- `mock_service_adapter`: Mock service adapter for testing
- `sample_function_step`: Sample FunctionStep for testing
- `sample_pipeline_config`: Sample PipelineConfig for testing

## Expected Behavior After Fixes

All tests should pass, validating that:

1. **Step Editor**: All parameter form widgets properly revert to default/placeholder states
2. **Function Pattern Editor**: All function parameter widgets correctly reset to default values  
3. **Widget Consistency**: Form manager state and widget display remain synchronized
4. **Placeholder Display**: Lazy dataclass fields show correct placeholder text and styling
5. **Signal Handling**: Reset operations emit appropriate signals for UI updates

## Debugging Failed Tests

If tests fail, check:

1. **Form Manager Integration**: Ensure reset methods target correct form manager
2. **Widget Creation**: Verify widgets are properly created and accessible
3. **Signal Connections**: Check that parameter change signals are connected
4. **Placeholder Logic**: Validate lazy context detection and placeholder application
5. **Default Values**: Ensure parameter defaults are correctly defined and accessible

## Continuous Integration

These tests are designed to run in CI environments:
- Use headless display mode (`QT_QPA_PLATFORM=offscreen`)
- Mock external dependencies (service adapters, file systems)
- Provide deterministic test data and expected outcomes
- Include proper setup and teardown for PyQt applications
