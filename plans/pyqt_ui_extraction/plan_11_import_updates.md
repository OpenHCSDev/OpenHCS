# plan_11_import_updates.md
## Component: Import Updates and File Deletion

### Objective
Update ALL imports throughout OpenHCS to use `pyqt_formgen` directly, then delete the original extracted files. No compatibility shims - clean break.

### Plan

1. **Update pyproject.toml** to add dependency:
   ```toml
   [project.optional-dependencies]
   gui = [
       "pyqt-reactor>=0.1.0",
       # ... other gui deps
   ]
   ```

2. **Search and replace imports** in all OpenHCS files:

   **Core utilities:**
   ```
   OLD: from openhcs.pyqt_gui.widgets.shared.debounce_timer import DebounceTimer
   NEW: from pyqt_formgen.core import DebounceTimer

   OLD: from openhcs.pyqt_gui.widgets.shared.reorderable_list_widget import ReorderableListWidget
   NEW: from pyqt_formgen.core import ReorderableListWidget
   ```

   **Theming (note class rename):**
   ```
   OLD: from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
   NEW: from pyqt_formgen.theming import ColorScheme

   OLD: from openhcs.pyqt_gui.shared.palette_manager import PaletteManager
   NEW: from pyqt_formgen.theming import PaletteManager

   OLD: from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
   NEW: from pyqt_formgen.theming import StyleSheetGenerator
   ```

   **Protocols:**
   ```
   OLD: from openhcs.ui.shared.widget_protocols import ValueGettable, ValueSettable
   NEW: from pyqt_formgen.protocols import ValueGettable, ValueSettable

   OLD: from openhcs.ui.shared.widget_adapters import LineEditAdapter
   NEW: from pyqt_formgen.protocols import LineEditAdapter
   ```

   **Widgets:**
   ```
   OLD: from openhcs.pyqt_gui.widgets.shared.no_scroll_spinbox import NoScrollSpinBox
   NEW: from pyqt_formgen.widgets import NoScrollSpinBox
   ```

   **Animation:**
   ```
   OLD: from openhcs.pyqt_gui.widgets.shared.flash_mixin import FlashMixin
   NEW: from pyqt_formgen.animation import FlashMixin

   OLD: from openhcs.pyqt_gui.widgets.shared.flash_config import FlashConfig
   NEW: from pyqt_formgen.animation import FlashConfig
   ```

   **Services:**
   ```
   OLD: from openhcs.pyqt_gui.widgets.shared.services.signal_service import SignalService
   NEW: from pyqt_formgen.services import SignalService
   ```

   **Forms:**
   ```
   OLD: from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
   NEW: from pyqt_formgen.forms import ParameterFormManager

   OLD: from openhcs.ui.shared.widget_factory import WidgetFactory
   NEW: from pyqt_formgen.forms import WidgetFactory
   ```

3. **Handle class renames**:
   - `PyQt6ColorScheme` → `ColorScheme` (search and replace in all files)

4. **Delete extracted files from OpenHCS**:

   From `openhcs/pyqt_gui/widgets/shared/`:
   - `debounce_timer.py`
   - `reorderable_list_widget.py`
   - `flash_config.py`
   - `flash_mixin.py`
   - `flash_overlay_opengl.py`
   - `no_scroll_spinbox.py`
   - `parameter_form_manager.py`
   - `widget_creation_types.py`
   - `widget_creation_config.py`
   - `widget_strategies.py`

   From `openhcs/pyqt_gui/widgets/shared/services/`:
   - `signal_service.py`
   - `widget_service.py`
   - `value_collection_service.py`
   - `flag_context_manager.py`
   - `field_change_dispatcher.py`
   - `form_init_service.py`

   From `openhcs/pyqt_gui/shared/`:
   - `color_scheme.py`
   - `palette_manager.py`
   - `style_generator.py`

   From `openhcs/ui/shared/`:
   - `widget_protocols.py`
   - `widget_adapters.py`
   - `widget_registry.py`
   - `widget_factory.py`
   - `widget_operations.py`
   - `widget_creation_registry.py`
   - `widget_dispatcher.py`
   - `parameter_form_service.py`
   - `parameter_form_base.py`
   - `parameter_info_types.py`
   - `parameter_type_utils.py`

5. **Update __init__.py files** to remove deleted exports

6. **Files that STAY in OpenHCS** (not extracted):
   - `openhcs/pyqt_gui/widgets/shared/abstract_manager_widget.py`
   - `openhcs/pyqt_gui/widgets/shared/config_hierarchy_tree.py`
   - `openhcs/pyqt_gui/widgets/shared/time_travel_widget.py`
   - `openhcs/pyqt_gui/widgets/shared/clickable_help_components.py` (minus FlashableGroupBox)
   - `openhcs/pyqt_gui/widgets/shared/services/scope_color_service.py`
   - `openhcs/pyqt_gui/widgets/shared/services/scope_token_service.py`
   - `openhcs/pyqt_gui/widgets/shared/services/zmq_execution_service.py`
   - `openhcs/pyqt_gui/widgets/shared/services/enum_dispatch_service.py`
   - All files in `openhcs/pyqt_gui/windows/`
   - All files in `openhcs/pyqt_gui/dialogs/`

7. **Run tests** to verify all imports work:
   ```bash
   pytest tests/ -x
   ```

8. **Fix any remaining import errors** iteratively

### Findings

**Estimated import updates**: ~50-100 files will need import changes

**Command to find all affected files**:
```bash
grep -r "from openhcs.pyqt_gui.widgets.shared.parameter_form_manager" --include="*.py" | wc -l
grep -r "from openhcs.ui.shared.widget" --include="*.py" | wc -l
grep -r "from openhcs.pyqt_gui.shared.color_scheme" --include="*.py" | wc -l
```

### Implementation Draft
<!-- Only write code here AFTER smell loop passes -->

