# plan_09_form_init_service.md
## Component: Form Initialization Service

### Objective
Extract the form initialization and introspection integration from `openhcs/pyqt_gui/widgets/shared/services/form_init_service.py` into `pyqt_formgen/forms/`. This bridges introspection with widget creation.

### Plan

1. **Extract FormBuildOrchestrator** (`form_init_service.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/services/form_init_service.py`
   - Target: `pyqt_formgen/forms/form_init_service.py`
   - Features:
     - `FormBuildOrchestrator` - Coordinates form building
     - `ServiceFactoryService` - Creates services for form
     - Parameter introspection integration
   - Changes:
     - Update imports to use `python_introspect` directly
     - Update imports to use local modules
     - Replace `openhcs.config_framework` with `objectstate`
   - Dependencies:
     - python_introspect (UnifiedParameterAnalyzer)
     - objectstate (for lazy placeholder handling)
     - local services and widget factory

2. **Extract ParameterFormService** (`parameter_form_service.py`):
   - Source: `openhcs/ui/shared/parameter_form_service.py`
   - Target: `pyqt_formgen/forms/parameter_form_service.py`
   - Features:
     - Service layer for form operations
     - Parameter extraction from objects
   - Dependencies: python_introspect

3. **Extract ParameterFormBase** (`parameter_form_base.py`):
   - Source: `openhcs/ui/shared/parameter_form_base.py`
   - Target: `pyqt_formgen/forms/parameter_form_base.py`
   - Features:
     - Base class for form managers
     - Common form functionality
   - Dependencies: Local modules

4. **Extract ParameterInfoTypes** (`parameter_info_types.py`):
   - Source: `openhcs/ui/shared/parameter_info_types.py`
   - Target: `pyqt_formgen/forms/parameter_info_types.py`
   - Features:
     - `ParameterInfoBase` ABC
     - Type definitions for parameter metadata
   - Dependencies: Only typing, abc

5. **Extract ParameterTypeUtils** (`parameter_type_utils.py`):
   - Source: `openhcs/ui/shared/parameter_type_utils.py`
   - Target: `pyqt_formgen/forms/parameter_type_utils.py`
   - Features:
     - Type analysis utilities
     - Optional/Union unwrapping
   - Dependencies: Only typing

6. **Update forms/__init__.py** (extends plan 08):
   ```python
   from .form_init_service import FormBuildOrchestrator, ServiceFactoryService
   from .parameter_form_service import ParameterFormService
   from .parameter_info_types import ParameterInfoBase
   ```

7. **Delete original files from OpenHCS**:
   - Delete `openhcs/pyqt_gui/widgets/shared/services/form_init_service.py`
   - Delete `openhcs/ui/shared/parameter_form_service.py`
   - Delete `openhcs/ui/shared/parameter_form_base.py`
   - Delete `openhcs/ui/shared/parameter_info_types.py`
   - Delete `openhcs/ui/shared/parameter_type_utils.py`

8. **Update all imports in OpenHCS**:
   - Replace `from openhcs.pyqt_gui.widgets.shared.services.form_init_service import FormBuildOrchestrator`
   - With `from pyqt_formgen.forms import FormBuildOrchestrator`

9. **Write tests** in `tests/test_form_init.py`:
   - Test FormBuildOrchestrator with simple dataclass
   - Test parameter extraction from function signatures
   - Test nested dataclass handling

### Findings

**form_init_service.py**:
- Key imports to update:
  - `openhcs.introspection.UnifiedParameterAnalyzer` → `python_introspect`
  - `openhcs.config_framework` → `objectstate`
  - `openhcs.pyqt_gui.shared.color_scheme` → local theming
  - `openhcs.core.lazy_placeholder_simplified` → objectstate.placeholder

**parameter_form_service.py**:
- Uses UnifiedParameterAnalyzer from introspection
- Should be straightforward import update

**parameter_info_types.py**:
- Pure ABCs and TypedDicts
- FULLY GENERIC

### Implementation Draft
<!-- Only write code here AFTER smell loop passes -->

