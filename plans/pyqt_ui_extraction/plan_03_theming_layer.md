# plan_03_theming_layer.md
## Component: Theming Layer

### Objective
Extract the complete theming system (color schemes, palette management, stylesheet generation) into `pyqt_formgen/theming/`. This provides application-wide theming capabilities.

### Plan

1. **Extract PyQt6ColorScheme** (`color_scheme.py`):
   - Source: `openhcs/pyqt_gui/shared/color_scheme.py`
   - Target: `pyqt_formgen/theming/color_scheme.py`
   - Changes: 
     - Rename class to `ColorScheme` (remove PyQt6 prefix - redundant in this package)
     - Update docstrings to be generic
   - Dependencies: Only `PyQt6.QtGui.QColor`, `dataclasses`, `pathlib`

2. **Extract PaletteManager** (`palette_manager.py`):
   - Source: `openhcs/pyqt_gui/shared/palette_manager.py`
   - Target: `pyqt_formgen/theming/palette_manager.py`
   - Changes:
     - Update import to use local `ColorScheme`
     - Update docstrings to be generic
   - Dependencies: PyQt6, local ColorScheme

3. **Extract StyleSheetGenerator** (`style_generator.py`):
   - Source: `openhcs/pyqt_gui/shared/style_generator.py`
   - Target: `pyqt_formgen/theming/style_generator.py`
   - Changes:
     - Update import to use local `ColorScheme`
     - Update docstrings to be generic
   - Dependencies: Local ColorScheme only

4. **Extract ThemeManager** (stays in `palette_manager.py`):
   - High-level theme coordination class
   - Already in same file as PaletteManager
   - Update imports to use local modules

5. **Update theming/__init__.py** with public exports:
   ```python
   from .color_scheme import ColorScheme
   from .palette_manager import PaletteManager, ThemeManager
   from .style_generator import StyleSheetGenerator

   __all__ = [
       'ColorScheme',
       'PaletteManager',
       'ThemeManager',
       'StyleSheetGenerator',
   ]
   ```

6. **Delete original files from OpenHCS**:
   - Delete `openhcs/pyqt_gui/shared/color_scheme.py`
   - Delete `openhcs/pyqt_gui/shared/palette_manager.py`
   - Delete `openhcs/pyqt_gui/shared/style_generator.py`

7. **Update all imports in OpenHCS**:
   - Replace `from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme`
   - With `from pyqt_formgen.theming import ColorScheme`
   - Note: Class renamed from `PyQt6ColorScheme` to `ColorScheme`

8. **Write tests** in `tests/test_theming.py`:
   - Test ColorScheme to_hex, to_qcolor methods
   - Test PaletteManager palette creation
   - Test StyleSheetGenerator stylesheet generation

### Findings

**Files reviewed**:
- `color_scheme.py`: ~310 lines, contains comprehensive color definitions
  - Only imports: PyQt6.QtGui.QColor, dataclasses, pathlib, logging, typing
  - FULLY GENERIC - no OpenHCS imports
  
- `palette_manager.py`: ~180 lines
  - Imports: PyQt6, local color_scheme
  - FULLY GENERIC after import update
  
- `style_generator.py`: ~360 lines
  - Imports: local color_scheme only
  - FULLY GENERIC after import update

**Class rename justification**: `PyQt6ColorScheme` → `ColorScheme`
- The PyQt6 prefix is redundant since the package is already PyQt6-specific
- Shorter, cleaner name
- Backwards compat via alias in OpenHCS shim

### Implementation Draft
<!-- Only write code here AFTER smell loop passes -->

