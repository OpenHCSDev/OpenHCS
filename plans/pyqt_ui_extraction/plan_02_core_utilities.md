# plan_02_core_utilities.md
## Component: Core Utilities

### Objective
Extract pure PyQt6 utility components with zero external dependencies into `pyqt_formgen/core/`. These are foundational widgets and helpers that have no OpenHCS-specific logic.

### Plan

1. **Extract DebounceTimer** (`debounce_timer.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/debounce_timer.py`
   - Target: `pyqt_formgen/core/debounce_timer.py`
   - Changes: None - this is pure PyQt6
   - Dependencies: Only `PyQt6.QtCore.QTimer`

2. **Extract ReorderableListWidget** (`reorderable_list_widget.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/reorderable_list_widget.py`
   - Target: `pyqt_formgen/core/reorderable_list_widget.py`
   - Changes: None - this is pure PyQt6
   - Dependencies: Only `PyQt6.QtWidgets.QListWidget`, `PyQt6.QtCore`

3. **Extract RichTextAppender** (`rich_text_appender.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/rich_text_appender.py`
   - Target: `pyqt_formgen/core/rich_text_appender.py`
   - Changes: Review for any OpenHCS imports
   - Dependencies: Only PyQt6

4. **Extract BackgroundTask** (`background_task.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/background_task.py`
   - Target: `pyqt_formgen/core/background_task.py`
   - Changes: Review for any OpenHCS imports
   - Dependencies: Only PyQt6

5. **Extract CollapsibleSplitterHelper** (`collapsible_splitter.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/collapsible_splitter_helper.py`
   - Target: `pyqt_formgen/core/collapsible_splitter.py`
   - Changes: Review for any OpenHCS imports
   - Dependencies: Only PyQt6

6. **Update core/__init__.py** with public exports:
   ```python
   from .debounce_timer import DebounceTimer
   from .reorderable_list_widget import ReorderableListWidget
   ```

7. **Delete original files from OpenHCS**:
   - Delete `openhcs/pyqt_gui/widgets/shared/debounce_timer.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/reorderable_list_widget.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/rich_text_appender.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/background_task.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/collapsible_splitter_helper.py`

8. **Update all imports in OpenHCS** that reference these files:
   - Search for `from openhcs.pyqt_gui.widgets.shared.debounce_timer`
   - Replace with `from pyqt_formgen.core import DebounceTimer`
   - Same pattern for all extracted modules

9. **Write basic tests** in `tests/test_core.py`:
   - Test DebounceTimer trigger/cancel/force
   - Test ReorderableListWidget drag-drop signal emission

### Findings

**Files reviewed**:
- `debounce_timer.py`: 46 lines, FULLY GENERIC (only imports PyQt6.QtCore.QTimer)
- `reorderable_list_widget.py`: 56 lines, FULLY GENERIC (only imports PyQt6)

**No modifications needed** - these files are already pure PyQt6 utilities.

### Implementation Draft
<!-- Only write code here AFTER smell loop passes -->

