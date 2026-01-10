# plan_12_test_migration.md
## Component: Test Migration

### Objective
Create a comprehensive test suite for `pyqt-formgen` and ensure existing OpenHCS tests continue to pass through the compatibility shims.

### Plan

1. **Setup pytest-qt** in pyqt-formgen:
   - Add `pytest-qt` to dev dependencies
   - Create `conftest.py` with QApplication fixture:
   ```python
   import pytest
   from PyQt6.QtWidgets import QApplication
   
   @pytest.fixture(scope="session")
   def qapp():
       app = QApplication.instance() or QApplication([])
       yield app
   ```

2. **Create test_core.py**:
   ```python
   def test_debounce_timer_trigger(qapp):
       """Test DebounceTimer triggers after delay."""
       
   def test_debounce_timer_cancel(qapp):
       """Test DebounceTimer can be cancelled."""
       
   def test_reorderable_list_signal(qapp):
       """Test ReorderableListWidget emits reorder signal."""
   ```

3. **Create test_theming.py**:
   ```python
   def test_color_scheme_to_hex():
       """Test ColorScheme RGB to hex conversion."""
       
   def test_palette_manager_creates_palette(qapp):
       """Test PaletteManager creates valid QPalette."""
       
   def test_style_generator_produces_stylesheet():
       """Test StyleSheetGenerator produces valid CSS."""
   ```

4. **Create test_protocols.py**:
   ```python
   def test_line_edit_adapter_implements_abcs(qapp):
       """Test LineEditAdapter implements all required ABCs."""
       
   def test_value_roundtrip_all_adapters(qapp):
       """Test get_value/set_value for all adapters."""
   ```

5. **Create test_widgets.py**:
   ```python
   def test_no_scroll_spinbox_ignores_wheel(qapp):
       """Test NoScrollSpinBox ignores wheel events."""
       
   def test_none_aware_checkbox_none_state(qapp):
       """Test NoneAwareCheckBox handles None."""
   ```

6. **Create test_animation.py**:
   ```python
   def test_flash_config_interpolation():
       """Test FlashConfig color interpolation."""
       
   def test_flash_mixin_trigger(qapp):
       """Test FlashMixin can trigger flash."""
   ```

7. **Create test_services.py**:
   ```python
   def test_signal_service_blocks_signals(qapp):
       """Test SignalService.block_signals context manager."""
       
   def test_flag_context_manager_prevents_reentry():
       """Test FlagContextManager prevents reentrant calls."""
   ```

8. **Create test_forms.py** (comprehensive):
   ```python
   from dataclasses import dataclass
   from pyqt_formgen.forms import ParameterFormManager

   @dataclass
   class SimpleConfig:
       name: str = "default"
       count: int = 10

   def test_form_from_simple_dataclass(qapp):
       """Test ParameterFormManager with simple dataclass."""
       form = ParameterFormManager(SimpleConfig)
       assert form is not None

   def test_form_from_nested_dataclass(qapp):
       """Test ParameterFormManager with nested dataclass."""

   def test_form_with_objectstate(qapp):
       """Test ParameterFormManager with ObjectState integration."""
       from objectstate import ObjectState
       # Use objectstate directly, not openhcs

   def test_value_extraction(qapp):
       """Test collecting values from form."""

   def test_parameter_update(qapp):
       """Test updating parameter programmatically."""
   ```

9. **Run OpenHCS test suite**:
   - Ensure all existing tests pass after import updates
   - Fix any import issues
   - Document any behavioral changes

10. **Add CI configuration**:
    - Create `.github/workflows/test.yml` for pyqt-formgen
    - Run tests on Python 3.11, 3.12, 3.13
    - Include coverage reporting

### Findings

**Existing OpenHCS tests** that touch extracted code:
- Need to identify tests in `tests/` that use ParameterFormManager
- These will need import updates (done in plan 11)
- May need `pytest-qt` in OpenHCS dev deps

**Test isolation**: pyqt-formgen tests must be runnable independently:
- NO openhcs imports in pyqt-formgen tests
- Use simple test dataclasses defined in test files
- Import only from: pyqt_formgen, objectstate, python_introspect, PyQt6

### Implementation Draft
<!-- Only write code here AFTER smell loop passes -->

