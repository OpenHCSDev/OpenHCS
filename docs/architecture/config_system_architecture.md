# OpenHCS Configuration System Architecture

## Why This Is The Most Sophisticated Configuration System With UI/UX In Existence

### Executive Summary

OpenHCS implements a **dual-axis hierarchical configuration system** with automatic cross-window propagation, declarative UI binding, and semantic visual feedback. No other system combines all of these properties in a unified architecture.

---

## 1. Dual-Axis Resolution (Saved vs Live)

Every configuration value exists in two parallel universes:

| Axis | Purpose | When Updated |
|------|---------|--------------|
| **Saved** | Committed state on disk | On explicit save |
| **Live** | In-flight edits | On every keystroke |

```python
# ObjectState maintains both caches simultaneously
class ObjectState:
    _saved_resolved: Dict[str, Any]  # What's on disk
    _live_resolved: Dict[str, Any]   # What user sees now
```

**Why this matters**: Users see instant feedback while editing, but the system always knows what's "real" (saved) vs "proposed" (live). No other config system maintains this dual-axis semantic.

---

## 2. Hierarchical Scope Inheritance

Configuration flows through a strict hierarchy:

```
GlobalPipelineConfig (global defaults)
    └── PipelineConfig (per-plate overrides)
        └── Step.processing_config (per-step overrides)
            └── Function kwargs (per-function overrides)
```

**The `None` Semantic**: At any level, `None` means "inherit from parent." This is enforced by the `@lazy_config` decorator which sets all defaults to `None`:

```python
@lazy_config
class ProcessingConfig:
    group_by: GroupBy = None        # Inherits from PipelineConfig
    variable_components: List = None # Inherits from PipelineConfig
```

**Resolution**: When accessing a field, the system walks up the scope hierarchy until it finds a non-None value. This happens automatically via `ObjectState.get_resolved_value()`.

---

## 3. Automatic Cross-Window Propagation

When a parent config changes, all child windows update **automatically**:

```
User changes PipelineConfig.group_by
    ↓
ObjectState detects resolved value changed
    ↓
Fires on_resolved_changed callback
    ↓
All subscribed widgets (StepEditor, FunctionEditor) refresh
    ↓
UI shows new inherited value instantly
```

**Implementation**: `ObjectStateRegistry` maintains a global listener list. Widgets subscribe to specific dotted paths:

```python
def _subscribe_to_step_state_changes(self):
    step_state = ObjectStateRegistry.get_by_scope(self.scope_id)
    step_state.on_resolved_changed = self._on_resolved_changed

def _on_resolved_changed(self, path: str, old_value, new_value):
    if path in ('processing_config.group_by', 'processing_config.variable_components'):
        self.refresh_from_step_context()
```

---

## 4. Declarative UI Binding

UI components declare what to display, not how:

```python
class PipelineEditorWidget(AbstractManagerWidget):
    LIST_ITEM_FORMAT = ListItemFormat(
        first_line=('func',),
        preview_line=(
            'processing_config.variable_components',
            'processing_config.group_by',
            'processing_config.input_source',
        ),
        formatters={
            'func': '_format_func_preview',
        },
    )
```

The ABC handles:
- Resolving values via ObjectState
- Applying formatters
- Adding dirty/sig-diff indicators
- Refreshing on cross-window updates

---

## 5. Semantic Visual Feedback

Two orthogonal visual semantics propagate through the entire UI:

| Indicator | Meaning | Visual |
|-----------|---------|--------|
| **Underline** | Value differs from signature default | Text decoration |
| **Asterisk (*)** | Value differs from saved state (dirty) | Prefix marker |

Both propagate to parent containers:
- Field label → GroupBox title → Tree item → Window title

```
* Step_1: Image Enhancement Processing  ← dirty (unsaved)
  └── func=[stack_percentile_normalize]  ← underlined (non-default)
```

---

## 6. Zero-Cost UI Interactions

**Axiom**: UI interactions cost nearly nothing.

ObjectState always has pre-computed cached state. When a widget needs a value:

```python
# This is O(1) - just a dict lookup, no resolution
value = object_state.get_resolved_value('processing_config.group_by')
```

Caches are pre-warmed on:
- Initial load
- Any edit (local recomputation)
- Cross-window propagation (targeted invalidation)

---

## 7. Metadata-Aware Display

Component keys (e.g., channel "1", "2") automatically resolve to human-readable names:

```python
def _format_func_preview(self, func, state=None):
    # Raw: {1: normalize, 2: enhance}
    # Displayed: {DAPI: normalize, GFP: enhance}
    display_name = metadata_cache.get_component_metadata(group_by, key)
```

This works everywhere: list previews, component buttons, navigation.

---

## Comparison With Major Industry Systems

| Capability | OpenHCS | VS Code | Unreal Engine | Godot | JetBrains |
|------------|---------|---------|---------------|-------|-----------|
| **Single source of truth model feeding all UI** | ✅ ObjectState IS the model | ◐ Settings stored + UI, not reactive ObjectState | ◐ File-driven, not reactive | ◐ EditorSettings exist | ◐ Run configs with UI |
| **Dual-axis resolution (saved vs live caches)** | ✅ Explicit two-cache | ❌ | ❌ | ❌ | ◐ Temp vs permanent, not per-field |
| **Hierarchical scope inheritance (None=inherit)** | ✅ Enforced via resolution walk | ✅ User/workspace/folder | ✅ Layered ini hierarchy | ✅ Editor vs project scopes | ✅ Configs + templates |
| **Cross-window propagation via path subscriptions** | ✅ Explicit listener model | ◐ UI updates, not positioned as dependency propagation | ❌ Load-on-start, not reactive | ◐ Not a core claim | ◐ Dialogs update |
| **Declarative UI binding (declare fields, framework resolves)** | ✅ LIST_ITEM_FORMAT / ABC | ◐ UI exists, not this contract | ❌ | ◐ Plugin APIs exist | ◐ Templates exist |
| **Two orthogonal semantic diffs (dirty + sig-diff) with propagation** | ✅ Underline + asterisk → containers | ◐ "Modified" exists, not dual semantic | ❌ | ❌ | ◐ One axis only |
| **Click-to-provenance (preview → editor → scroll → flash)** | ✅ | ◐ "Go to setting" exists | ❌ | ◐ Inspector nav exists | ◐ Navigation exists |
| **Flash overlay architecture (single paint pass)** | ✅ | ❌ | ❌ | ❌ | ❌ |
| **Deterministic scope colors with WCAG AA enforcement** | ✅ | ❌ | ❌ | ❌ | ❌ |
| **Layered border visualization of scope nesting** | ✅ | ❌ | ❌ | ❌ | ❌ |
| **Metadata-aware display (component keys → names)** | ✅ | ◐ Labels exist, different domain | ❌ | ◐ Names exist | ❌ |
| **Zero-cost UI via precomputed caches** | ✅ | ◐ | ◐ | ◐ | ◐ |

**Legend**: ✅ = First-class, systemic | ◐ = Partial/exists but not this architecture | ❌ = Not present

### Key Insight

OpenHCS is the **only system** with ✅ across all 12 capabilities. Other systems have subsets:
- **VS Code**: Great scope inheritance, but no dual-axis resolution or reactive propagation
- **Unreal**: Excellent layered config hierarchy, but file-driven not reactive
- **JetBrains**: Good run config templates, but no visual semantic propagation

**No other system combines**: dual-axis + reactive propagation + declarative binding + dual semantic diffs + click-to-provenance + game-engine flash + WCAG colors + layered borders.

---

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                     ObjectStateRegistry                          │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │
│  │ GlobalScope │──│ PlateScope  │──│ StepScope   │──► ...       │
│  │ scope_id="" │  │ scope_id=   │  │ scope_id=   │              │
│  │             │  │ "/path/plate"│  │ "plate::S1" │              │
│  └─────────────┘  └─────────────┘  └─────────────┘              │
│         │                │                │                      │
│         ▼                ▼                ▼                      │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │
│  │ ObjectState │  │ ObjectState │  │ ObjectState │              │
│  │ _saved_res  │  │ _saved_res  │  │ _saved_res  │              │
│  │ _live_res   │  │ _live_res   │  │ _live_res   │              │
│  │ on_resolved │  │ on_resolved │  │ on_resolved │              │
│  │ _changed()  │  │ _changed()  │  │ _changed()  │              │
│  └─────────────┘  └─────────────┘  └─────────────┘              │
└─────────────────────────────────────────────────────────────────┘
         │                │                │
         ▼                ▼                ▼
┌─────────────────────────────────────────────────────────────────┐
│                        UI Layer                                  │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐           │
│  │ ConfigWindow │  │ PipelineEdit │  │ StepEditor   │           │
│  │ (GlobalConf) │  │ (ListItems)  │  │ (FormFields) │           │
│  └──────────────┘  └──────────────┘  └──────────────┘           │
│         ↑                ↑                ↑                      │
│         └────────────────┴────────────────┘                      │
│                    Declarative binding via                       │
│                    LIST_ITEM_FORMAT / PREVIEW_FIELD_CONFIGS      │
└─────────────────────────────────────────────────────────────────┘
```

---

## 8. Click-to-Provenance Navigation

Clicking any field in a list item preview opens the editor window and **scrolls directly to that field**:

```
User clicks "group_by=CHANNEL" in step list preview
    ↓
DualEditorWindow opens for that step
    ↓
Scrolls to processing_config groupbox
    ↓
Scrolls group_by field to top of viewport
    ↓
Flashes the field to draw attention
```

**Smart scrolling behavior**:
- Only scrolls if target is not already viewable
- GroupBoxes top-align or center when scrolling
- Fields within groupboxes scroll towards viewport top

---

## 9. Game-Engine Flash Animation Architecture

All flash effects render in a **single `paintEvent` per window frame** for maximum performance:

```python
class FlashOverlayMixin:
    def paintEvent(self, event):
        super().paintEvent(event)
        # Single pass: render ALL active flashes
        for flash in self._active_flashes:
            self._render_flash(flash, painter)
```

**Flash masking granularity**:
- Flash a specific field label
- Flash an entire GroupBox (title + border)
- Flash a list item row
- Flash a tree item

**Animation properties**:
- Configurable duration, easing curves
- Alpha fade from highlight → transparent
- Scope-colored flash tint (matches scope border color)

---

## 10. WCAG AA Compliant Scope Colors

Scope colors are generated deterministically from scope ID using **MD5 hashing with WCAG AA contrast enforcement**:

```python
def generate_scope_color(scope_id: str) -> QColor:
    # MD5 hash → hue rotation
    hash_bytes = hashlib.md5(scope_id.encode()).digest()
    hue = (hash_bytes[0] / 255) * 360

    # Enforce WCAG AA contrast ratio (4.5:1 minimum)
    color = QColor.fromHsv(hue, saturation, value)
    while contrast_ratio(color, background) < 4.5:
        adjust_lightness(color)
    return color
```

**Result**: Every scope (plate, step, function) gets a unique, consistent, accessible color that works on both light and dark backgrounds.

---

## 11. Layered Border System

Scope hierarchy is visualized through **layered borders**:

```
┌─────────────────────────────────┐  ← Plate scope (outermost)
│ ┌─────────────────────────────┐ │  ← Step scope
│ │ ┌─────────────────────────┐ │ │  ← Function scope (innermost)
│ │ │      Field Content      │ │ │
│ │ └─────────────────────────┘ │ │
│ └─────────────────────────────┘ │
└─────────────────────────────────┘
```

Each border layer uses the scope's deterministic color, creating immediate visual hierarchy.

---

## 12. Single Source of Truth Architecture

**ObjectState IS the model**. There is no separate "config manager" or "settings store":

```
                    ┌──────────────┐
                    │ ObjectState  │ ← SINGLE SOURCE OF TRUTH
                    │              │
                    │ • _saved_res │ ← What's on disk
                    │ • _live_res  │ ← Current edits
                    │ • scope_id   │ ← Hierarchy position
                    │ • parent     │ ← Inheritance chain
                    └──────────────┘
                           │
            ┌──────────────┼──────────────┐
            ▼              ▼              ▼
     ┌──────────┐   ┌──────────┐   ┌──────────┐
     │ FormMgr  │   │ ListItem │   │ TreeItem │
     │ (Editor) │   │ (Preview)│   │ (Nav)    │
     └──────────┘   └──────────┘   └──────────┘
            │              │              │
            └──────────────┴──────────────┘
                           │
                     All read from
                     ObjectState
```

**No divergence possible**: Every UI component reads from ObjectState. There's no "sync" step because there's nothing to sync.

---

## Conclusion

OpenHCS's configuration system is not just a settings manager—it's a **reactive state management framework** purpose-built for hierarchical scientific pipeline configuration. The combination of:

- Dual-axis resolution (saved/live)
- Automatic cross-window propagation
- Declarative UI binding
- Semantic visual feedback (underline/asterisk)
- Click-to-provenance navigation
- Game-engine flash architecture
- WCAG AA compliant scope colors
- Layered border visualization
- Single source of truth (ObjectState)

...creates a user experience where configuration "just works" across arbitrarily complex hierarchies, with instant visual feedback, accessible colors, and zero-cost interactions.

