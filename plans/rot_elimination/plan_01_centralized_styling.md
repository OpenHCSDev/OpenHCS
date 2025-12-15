# plan_01_centralized_styling.md
## Component: PyQt Centralized Styling

### Objective
Eliminate duplicate `StyleSheetGenerator` instantiations and duplicate `_get_button_style()` methods across 25+ widgets. Every widget should access styling through a single centralized source — NOT by creating its own generator instance.

### Findings

**Current Rot:**

| Pattern | Count | Issue |
|---------|-------|-------|
| Widgets creating own `StyleSheetGenerator` | 25 | Duplicate instantiation, scattered state |
| Manual `.generate_*_style()` calls | 42 | Imperative styling, widgets know about styling |
| Duplicate `_get_button_style()` methods | 2+ | Same method copy-pasted (function_list_editor, step_parameter_editor) |

**Existing Infrastructure (Underutilized):**

1. `PaletteManager` — Already holds centralized `style_generator` instance
2. `generate_complete_application_style()` — Already generates app-wide stylesheet
3. `ThemeManager` — Already manages color scheme changes

**The Wrong Way (Current):**
```python
class MyWidget(QWidget):
    def __init__(self, color_scheme, ...):
        self.style_generator = StyleSheetGenerator(self.color_scheme)  # ❌ 25 copies
        
    def setup_ui(self):
        btn.setStyleSheet(self.style_generator.generate_button_style())  # ❌ Imperative
```

**The Cracked Way:**
```python
class MyWidget(QWidget):
    # No style_generator. No setStyleSheet calls. 
    # Application-level stylesheet targets widget types automatically.
    pass
```

### Plan

**Phase 1: Application-Level Stylesheet Completeness**

The `generate_complete_application_style()` already exists but doesn't cover all widget types.

1. Audit all widget types that currently need manual styling
2. Add rules to `generate_complete_application_style()` for each widget type
3. Ensure QSS specificity is correct (more specific rules override general ones)

**Phase 2: Remove Widget-Level StyleSheetGenerator Instantiation**

For each widget that creates its own `StyleSheetGenerator`:
1. Remove `self.style_generator = StyleSheetGenerator(...)` line
2. Remove all `btn.setStyleSheet(self.style_generator.generate_*())` calls
3. Widget inherits styling from application-level stylesheet automatically

**Phase 3: Eliminate Duplicate `_get_button_style()` Methods**

Files with duplicate methods:
- `openhcs/pyqt_gui/widgets/function_list_editor.py:241`
- `openhcs/pyqt_gui/widgets/step_parameter_editor.py:370`

1. Delete both `_get_button_style()` methods
2. Buttons inherit from application-level button style
3. If variant needed, use QSS object names or classes

**Phase 4: Dynamic Styling via Object Names**

For widgets that need variant styles (e.g., primary vs secondary buttons):
1. Widget sets `setObjectName("primary_button")` or `setObjectName("secondary_button")`
2. Application stylesheet has rules: `QPushButton#primary_button { ... }`
3. Widget code contains ZERO style strings

### Structural Properties

- **No StyleSheetGenerator in widgets** — Widgets don't import or instantiate StyleSheetGenerator
- **No setStyleSheet calls** — Except at application level
- **Style is derived from widget type** — QPushButton gets button style automatically
- **Variants via object names** — Not via method calls

### Cleanup — DELETE ALL OF THIS

**Code to DELETE from 25+ widget files:**
```python
self.style_gen = StyleSheetGenerator(self.color_scheme)  # DELETE all 25 instances
self.style_generator = StyleSheetGenerator(...)          # DELETE
self.setStyleSheet(self.style_gen.generate_*_style())    # DELETE all 42 calls
```

**Methods to DELETE:**
```python
def _get_button_style(self):  # DELETE from function_list_editor.py
def _get_button_style(self):  # DELETE from step_parameter_editor.py
```

**No wrappers. No backwards compatibility.**
- Widgets that call `style_gen.generate_*_style()` → DELETE the call entirely
- Application stylesheet handles all styling
- If a widget looks wrong, fix the application stylesheet — don't add widget-level styling

### Implementation Draft

(After smell loop approval)

