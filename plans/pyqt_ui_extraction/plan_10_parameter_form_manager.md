# plan_10_parameter_form_manager.md
## Component: ParameterFormManager (Core)

### Objective
Extract the main `ParameterFormManager` class into `pyqt_formgen/forms/`. This is the crown jewel - a React-quality reactive form manager for PyQt6.

### Plan

1. **Extract WidgetCreationTypes** (`widget_creation_types.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/widget_creation_types.py`
   - Target: `pyqt_formgen/forms/widget_creation_types.py`
   - Features:
     - `ParameterFormManager` ABC
     - `_CombinedMeta` metaclass (ABC + QWidget)
     - `WidgetCreationConfig` dataclass
     - Handler type aliases
   - Changes:
     - Update import for ParameterInfoBase to local
   - Dependencies: Local parameter_info_types

2. **Extract WidgetCreationConfig** (`widget_creation_config.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/widget_creation_config.py`
   - Target: `pyqt_formgen/forms/widget_creation_config.py`
   - Features:
     - `create_widget_parametric()` - Main widget creation orchestrator
     - Widget type detection and routing
   - Dependencies: widget_creation_types, widget_factory

3. **Extract FormManagerConfig** (in parameter_form_manager.py):
   - The `FormManagerConfig` dataclass from PFM
   - Configuration object for form initialization

4. **Extract ParameterFormManager** (`parameter_form_manager.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`
   - Target: `pyqt_formgen/forms/parameter_form_manager.py`
   - This is ~1000 lines - the main implementation
   - Changes:
     - Update ALL imports to use pyqt_formgen modules
     - Replace `openhcs.config_framework.object_state` → `objectstate`
     - Replace `openhcs.introspection` → `python_introspect`
     - Replace `openhcs.utils.performance_monitor` → optional or remove
   - Key features to preserve:
     - React-style lifecycle hooks
     - ObjectState integration (state parameter)
     - Nested form managers
     - Cross-window context changes
     - Async widget creation

5. **Handle ObjectState Integration**:
   - ObjectState is a required dependency
   - Import from `objectstate` package directly
   - Support both ObjectState-backed and plain dataclass forms

6. **Handle performance_monitor**:
   - Option A: Make it optional (try/except import)
   - Option B: Create minimal timer in pyqt_formgen
   - Option C: Remove timing decorators
   - Recommendation: Option A - optional import with no-op fallback

7. **Update forms/__init__.py** (final):
   ```python
   from .parameter_form_manager import ParameterFormManager, FormManagerConfig
   from .widget_creation_types import (
       ParameterFormManager as ParameterFormManagerABC,
       _CombinedMeta, WidgetCreationConfig,
   )
   ```

8. **Delete original files from OpenHCS**:
   - Delete `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/widget_creation_types.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/widget_creation_config.py`

9. **Write tests** in `tests/test_parameter_form_manager.py`:
   - Test form creation from simple dataclass
   - Test nested dataclass form
   - Test ObjectState-backed form
   - Test value extraction
   - Test parameter updates

### Findings

**ParameterFormManager imports to update** (from codebase search):
```python
# FROM openhcs → TO pyqt_formgen/objectstate/python_introspect
openhcs.pyqt_gui.widgets.shared.flash_mixin → pyqt_formgen.animation
openhcs.pyqt_gui.widgets.shared.clickable_help_components → pyqt_formgen.widgets
openhcs.pyqt_gui.widgets.shared.widget_creation_types → pyqt_formgen.forms
openhcs.utils.performance_monitor → optional/remove
openhcs.ui.shared.widget_operations → pyqt_formgen.forms
openhcs.ui.shared.widget_factory → pyqt_formgen.forms
openhcs.ui.shared.widget_creation_registry → pyqt_formgen.forms
openhcs.pyqt_gui.widgets.shared.services.* → pyqt_formgen.services
openhcs.introspection → python_introspect
openhcs.config_framework.object_state → objectstate
openhcs.pyqt_gui.shared.style_generator → pyqt_formgen.theming
```

**Critical path**: This is the most complex extraction. All previous plans must be complete.

### Implementation Draft
<!-- Only write code here AFTER smell loop passes -->

