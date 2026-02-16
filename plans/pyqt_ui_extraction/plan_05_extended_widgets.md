# plan_05_extended_widgets.md
## Component: Extended Widgets

### Objective
Extract specialized widget subclasses that build on the protocol layer into `pyqt_formgen/widgets/`. These are reusable widgets with enhanced behavior.

### Plan

1. **Extract NoScrollSpinBox family** (`no_scroll_spinbox.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/no_scroll_spinbox.py`
   - Target: `pyqt_formgen/widgets/no_scroll_spinbox.py`
   - Classes:
     - `NoScrollSpinBox` - SpinBox ignoring wheel events
     - `NoScrollDoubleSpinBox` - DoubleSpinBox ignoring wheel events
     - `NoScrollComboBox` - ComboBox ignoring wheel events, with placeholder support
     - `NoneAwareCheckBox` - CheckBox with None state support
   - Changes:
     - Update imports to use `pyqt_formgen.protocols.widget_adapters`
     - Remove openhcs-specific protocol registration (done in forms layer)
   - Dependencies: protocols layer

2. **Extract FlashableGroupBox** (`flashable_groupbox.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/clickable_help_components.py` (partial)
   - Target: `pyqt_formgen/widgets/flashable_groupbox.py`
   - Only extract `FlashableGroupBox` class, not the help-specific components
   - Changes:
     - Remove OpenHCS-specific help functionality
     - Keep flash animation support
   - Dependencies: animation layer (circular - see below)

3. **Handle circular dependency with animation layer**:
   - FlashableGroupBox needs flash_mixin
   - flash_mixin needs widget references
   - Solution: Define `FlashableWidget` protocol in protocols layer
   - FlashableGroupBox implements this protocol
   - flash_mixin works with any FlashableWidget

4. **Extract StatusIndicator** (`status_indicator.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/status_indicator.py`
   - Target: `pyqt_formgen/widgets/status_indicator.py`
   - Visual status indicator widget
   - Dependencies: theming layer for colors

5. **Update widgets/__init__.py**:
   ```python
   from .no_scroll_spinbox import (
       NoScrollSpinBox, NoScrollDoubleSpinBox,
       NoScrollComboBox, NoneAwareCheckBox,
   )
   from .flashable_groupbox import FlashableGroupBox
   from .status_indicator import StatusIndicator
   ```

6. **Delete original files from OpenHCS**:
   - Delete `openhcs/pyqt_gui/widgets/shared/no_scroll_spinbox.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/status_indicator.py`
   - Note: `clickable_help_components.py` stays - only FlashableGroupBox extracted

7. **Update all imports in OpenHCS**:
   - Replace `from openhcs.pyqt_gui.widgets.shared.no_scroll_spinbox import NoScrollSpinBox`
   - With `from pyqt_formgen.widgets import NoScrollSpinBox`

8. **Write tests** in `tests/test_widgets.py`:
   - Test wheel event ignoring for NoScroll* widgets
   - Test placeholder rendering for NoScrollComboBox
   - Test None state for NoneAwareCheckBox

### Findings

**no_scroll_spinbox.py** (223 lines):
- Imports:
  - PyQt6 (required)
  - `openhcs.ui.shared.widget_adapters` (will be local protocols)
  - `openhcs.ui.shared.widget_protocols` (will be local protocols)
- The final lines register NoneAwareCheckBox with ABC - move to forms layer

**clickable_help_components.py**:
- Contains multiple classes - only FlashableGroupBox is generic
- Other classes (ClickableHelpLabel, etc.) are OpenHCS-specific
- Extract only FlashableGroupBox

**status_indicator.py**: 
- Need to review for OpenHCS dependencies

### Implementation Draft
<!-- Only write code here AFTER smell loop passes -->

