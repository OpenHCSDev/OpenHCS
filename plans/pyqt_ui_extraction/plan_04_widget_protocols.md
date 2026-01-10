# plan_04_widget_protocols.md
## Component: Widget Protocols (ABCs)

### Objective
Extract the widget ABC contracts and Qt widget adapters into `pyqt_formgen/protocols/`. This provides the type-safe widget interface layer that eliminates duck typing.

### Plan

1. **Extract Widget ABCs** (`widget_protocols.py`):
   - Source: `openhcs/ui/shared/widget_protocols.py`
   - Target: `pyqt_formgen/protocols/widget_protocols.py`
   - Changes: None - already fully generic
   - ABCs to extract:
     - `ValueGettable` - get_value() contract
     - `ValueSettable` - set_value() contract
     - `PlaceholderCapable` - set_placeholder() contract
     - `RangeConfigurable` - configure_range() contract
     - `EnumSelectable` - enum dropdown contract
     - `ChangeSignalEmitter` - signal connection contract

2. **Extract Widget Adapters** (`widget_adapters.py`):
   - Source: `openhcs/ui/shared/widget_adapters.py`
   - Target: `pyqt_formgen/protocols/widget_adapters.py`
   - Changes:
     - Update import to use local `widget_protocols`
     - Remove import of `widget_registry` (will be in forms/)
   - Adapters to extract:
     - `LineEditAdapter`
     - `SpinBoxAdapter`
     - `DoubleSpinBoxAdapter`
     - `ComboBoxAdapter`
     - `CheckBoxAdapter`
     - `GroupBoxAdapter`

3. **Handle metaclass complexity**:
   - `PyQtWidgetMeta` class combines ABCMeta with Qt's metaclass
   - Must remain in widget_adapters.py
   - This is the critical pattern for ABC + QWidget inheritance

4. **Update protocols/__init__.py**:
   ```python
   from .widget_protocols import (
       ValueGettable, ValueSettable, PlaceholderCapable,
       RangeConfigurable, EnumSelectable, ChangeSignalEmitter,
   )
   from .widget_adapters import (
       LineEditAdapter, SpinBoxAdapter, DoubleSpinBoxAdapter,
       ComboBoxAdapter, CheckBoxAdapter, GroupBoxAdapter,
       PyQtWidgetMeta,
   )
   ```

5. **Delete original files from OpenHCS**:
   - Delete `openhcs/ui/shared/widget_protocols.py`
   - Delete `openhcs/ui/shared/widget_adapters.py`

6. **Update all imports in OpenHCS**:
   - Replace `from openhcs.ui.shared.widget_protocols import ValueGettable`
   - With `from pyqt_formgen.protocols import ValueGettable`

7. **Write tests** in `tests/test_protocols.py`:
   - Test that adapters implement all required ABCs
   - Test get_value/set_value round-trip for each adapter
   - Test signal connection for ChangeSignalEmitter

### Findings

**widget_protocols.py** (156 lines):
- Pure ABCs with no external dependencies
- FULLY GENERIC - only uses `abc` and `typing`

**widget_adapters.py** (~400 lines):
- Imports:
  - PyQt6 widgets (required)
  - widget_protocols (will be local)
  - widget_registry (needs separation - move to forms/)
- The WidgetMeta import from widget_registry is only used for auto-registration
- Can be made optional or moved to forms layer

**Dependency to resolve**:
- `widget_registry.py` has `WidgetMeta` for auto-registration
- This is a forms-layer concern, not protocols-layer
- Solution: Remove auto-registration from adapters, do it explicitly in forms layer

### Implementation Draft
<!-- Only write code here AFTER smell loop passes -->

