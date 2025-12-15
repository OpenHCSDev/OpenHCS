# plan_01_centralized_styling.md
## Component: PyQt Centralized Styling

### Objective

Eliminate 227 scattered `setStyleSheet()` calls and 25+ `StyleSheetGenerator` instantiations. Widgets should declare WHAT they are (via object names), not HOW they look (via style strings).

### The Rot

```python
# 25+ widgets do this:
class MyWidget(QWidget):
    def __init__(self, color_scheme, ...):
        self.style_generator = StyleSheetGenerator(self.color_scheme)  # ❌ Duplicate

    def setup_ui(self):
        btn.setStyleSheet(self.style_generator.generate_button_style())  # ❌ Imperative
        label.setStyleSheet(f"color: {self.color_scheme.to_hex(...)};")  # ❌ Inline
```

**Counts:**
- 227 `setStyleSheet()` calls across pyqt_gui/
- 25+ `StyleSheetGenerator` instantiations
- 2+ duplicate `_get_button_style()` methods

### The Insight

Qt stylesheets cascade like CSS. Application-level stylesheet applies to ALL widgets. Widget-level `setStyleSheet()` is only needed for:
1. **Dynamic state** — e.g., flash animations, error highlighting
2. **Variant styling** — e.g., primary vs secondary buttons

Everything else should be in the application stylesheet.

### Existing Infrastructure (Underutilized)

```python
# openhcs/pyqt_gui/shared/palette_manager.py
class PaletteManager:
    def __init__(self):
        self.style_generator = StyleSheetGenerator(self.color_scheme)  # ✅ ONE instance

# openhcs/pyqt_gui/shared/style_generator.py
def generate_complete_application_style(self) -> str:
    """Generate complete application-wide QStyleSheet."""  # ✅ Already exists
```

### Plan

**Step 1: Audit and Extend Application Stylesheet**

The `generate_complete_application_style()` exists but doesn't cover all widget types.

1. Grep all `setStyleSheet()` calls
2. Categorize: which are static (can move to app stylesheet) vs dynamic (must stay)
3. Add missing widget type rules to `generate_complete_application_style()`

**Step 2: Introduce Object Name Convention**

For variant styling, widgets declare their role:

```python
# Widget code (declaration only):
btn.setObjectName("primary_button")
btn.setObjectName("secondary_button")
btn.setObjectName("danger_button")

# Application stylesheet (styling only):
QPushButton#primary_button { background-color: ...; }
QPushButton#secondary_button { background-color: ...; }
QPushButton#danger_button { background-color: ...; }
```

**Step 3: Remove Widget-Level StyleSheetGenerator**

For each widget that creates its own `StyleSheetGenerator`:
1. DELETE `self.style_generator = StyleSheetGenerator(...)`
2. DELETE all static `setStyleSheet()` calls
3. Widget inherits from application stylesheet automatically

**Step 4: Keep Dynamic Styling Where Needed**

Some `setStyleSheet()` calls are legitimate:
- Flash animations (scope colors, dirty indicators)
- Error states (red borders)
- Runtime-computed styles

These stay, but should use a centralized helper:

```python
# Instead of inline style strings:
widget.setStyleSheet(f"border: 2px solid {color};")

# Use centralized helper:
from openhcs.pyqt_gui.shared.style_helpers import apply_flash_border
apply_flash_border(widget, scope_color)
```

### Qt Stylesheet Limitations (Acknowledged)

Qt stylesheets have quirks:
- Specificity rules differ from CSS
- Some properties don't cascade (e.g., `font` on QGroupBox)
- Pseudo-states (`:hover`, `:pressed`) can be finicky

**Mitigation:** Test each widget type after migration. If Qt fights back, document the exception and keep minimal widget-level styling.

### Cleanup — DELETE ALL OF THIS

**From 25+ widget files:**
```python
# DELETE all of these patterns:
self.style_gen = StyleSheetGenerator(self.color_scheme)
self.style_generator = StyleSheetGenerator(...)
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator  # (if unused after)

# DELETE static setStyleSheet calls:
btn.setStyleSheet(self.style_generator.generate_button_style())
label.setStyleSheet(f"color: {self.color_scheme.to_hex(...)};")
```

**DELETE duplicate methods:**
```python
def _get_button_style(self):  # function_list_editor.py
def _get_button_style(self):  # step_parameter_editor.py
```

**Estimated deletion:** ~200 lines of scattered styling code

**No wrappers. No backwards compatibility.**
- If a widget looks wrong after migration, fix the application stylesheet
- Don't add widget-level styling back

### Files to Modify

**Extend:**
- `openhcs/pyqt_gui/shared/style_generator.py` — Add missing widget type rules

**Clean up (remove StyleSheetGenerator):**
- `openhcs/pyqt_gui/dialogs/custom_function_manager_dialog.py`
- `openhcs/pyqt_gui/dialogs/function_selector_dialog.py`
- `openhcs/pyqt_gui/widgets/shared/abstract_table_browser.py`
- `openhcs/pyqt_gui/widgets/shared/column_filter_widget.py`
- `openhcs/pyqt_gui/widgets/shared/zmq_server_manager.py`
- ... and 20+ more

### Implementation Draft

*(Only after smell loop passes)*
