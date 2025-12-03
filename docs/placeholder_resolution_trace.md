# Placeholder resolution trace

Walkthrough of how parameter form placeholders are produced, refreshed, and cleared in the PyQt6 form manager stack.

## High-level flow (initial + bulk refresh)

```mermaid
sequenceDiagram
    participant Form as ParameterFormManager
    participant Ops as ParameterOpsService
    participant Live as LiveContextService
    participant Stack as build_context_stack
    participant Lazy as LazyDefaultPlaceholderService
    participant Widget as PyQt6WidgetEnhancer

    Form->>Ops: refresh_with_live_context(use_user_modified_only)
    Ops->>Live: collect(scope_filter, for_type=root_type)
    Live-->>Ops: LiveContextSnapshot(values)
    Ops->>Stack: build_context_stack(context_obj, overlay, live_context, root_form_values)
    Stack-->>Ops: ExitStack with layered config_contexts
    Ops->>Lazy: get_lazy_resolved_placeholder(obj_type, field_name)
    Lazy-->>Ops: placeholder text (e.g., "Default: 2")
    Ops->>Widget: apply_placeholder_text(widget, text)
```

- `use_user_modified_only` is the boolean flag on `refresh_with_live_context`:
  - False (default) → overlay uses `manager.parameters` so placeholders include inherited current values.
  - True → overlay uses only `get_user_modified_values()`, useful when you want to avoid unresolved `None` values in the overlay from masking inherited defaults (e.g., targeted refreshes after selective changes).

## Change event and sibling/cross-window refresh

```mermaid
sequenceDiagram
    participant User
    participant Widget
    participant Manager as ParameterFormManager
    participant Dispatch as FieldChangeDispatcher
    participant Ops as ParameterOpsService
    participant Live as LiveContextService
    participant Others as Other managers

    User->>Widget: edits field
    Widget->>Manager: change signal (via PyQt6WidgetEnhancer.connect_change_signal)
    Manager->>Dispatch: FieldChangeEvent(field, value)
    Dispatch->>Manager: parameters[field] = value
    Dispatch->>Manager: add to _user_set_fields
    Dispatch->>Manager.parent: mark modified (_mark_parents_modified)
    Dispatch->>Ops: refresh_single_placeholder on siblings when value is None
    Dispatch->>Live: increment_token(notify=False)
    Dispatch->>Live: _notify_change()
    Live->>Others: callbacks (_on_live_context_changed)
    Others->>Others: _schedule_cross_window_refresh()
    Others->>Ops: refresh_with_live_context(...)
```

## Detailed trace (call stack + responsibilities)

- Creation (`openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`):
  - Root managers register with `LiveContextService` and connect `_on_live_context_changed` during `__init__`.
  - `InitialRefreshStrategy.execute()` triggers a first `refresh_with_live_context` so every `None` field renders an inherited placeholder.

- Placeholder computation (`openhcs/pyqt_gui/widgets/shared/services/parameter_ops_service.py`):
  - `refresh_with_live_context` recurses through nested managers, calling `refresh_all_placeholders`.
  - For each manager:
    - Collect live values from other open forms via `ParameterFormManager.collect_live_context` → `LiveContextService.collect` (scope-aware, ancestor-filtered).
    - Build a context stack with `config_framework.build_context_stack`:
      - Global layer (thread-local or other window’s global edits; masks with static defaults when editing global config).
      - Parent chain (unified loop over ancestors + immediate parent, live values preferred, stored fallback for immediate parent).
      - Root form layer (root form’s live values for sibling inheritance).
      - Overlay of this form’s own values (via `_compute_overlay`).
    - With the stack active, call `ParameterFormService.get_placeholder_text` → `LazyDefaultPlaceholderService.get_lazy_resolved_placeholder`. This instantiates the lazy config to let its resolver compute the inherited value, then formats `"Default: <value>"` (or `(none)`).
    - `PyQt6WidgetEnhancer.apply_placeholder_text` paints the widget: strategy per widget type, sets `is_placeholder_state` + tooltips, and caches the placeholder text to avoid redundant updates.

- Single-field refresh:
  - `refresh_single_placeholder` (same service) bypasses bulk work for a single `None` field: rebuilds a stack with `overlay_without_field` to avoid self-shadowing, then applies placeholder to that widget only.

- Change dispatch path (`openhcs/pyqt_gui/widgets/shared/services/field_change_dispatcher.py`):
  - Signals from widgets are connected through `PyQt6WidgetEnhancer.connect_change_signal`, which first clears placeholder styling (`_clear_placeholder_state`) before emitting a `FieldChangeEvent`.
  - Dispatcher updates `parameters` and `_user_set_fields`, marks parent chains modified, refreshes sibling placeholders that share the field, invalidates the live-context token (deferred notify), then notifies `LiveContextService` listeners for cross-window refresh.
  - Root manager emits `parameter_changed` and `context_changed` (with `scope_id`), which other forms receive via `_on_live_context_changed` and debounce through `_schedule_cross_window_refresh`.

- Live context production (`openhcs/pyqt_gui/widgets/shared/services/live_context_service.py`):
  - `collect()` walks all active managers (and nested ones), pulling `get_user_modified_values()`. Nested values are reconstructed into the parent’s entry for sibling inheritance.
  - Returns `LiveContextSnapshot` keyed by config type; token-based cache avoids recompute inside a dispatch cycle.

- Widget behavior (`openhcs/pyqt_gui/widgets/shared/widget_strategies.py`):
  - Placeholder strategies per widget (LineEdit, SpinBox, ComboBox, CheckBox, CheckboxGroup, Path).
  - ComboBoxes use `setPlaceholder`/`setCurrentIndex(-1)` to show inherited value while keeping `None` concrete selection.
  - `_clear_placeholder_state` removes styling + cached text so resets back to `None` can reapply placeholders.

## Context stack layers (visual)

```mermaid
graph TD
    A["Global layer - thread-local or live global"] --> B["Parent chain - unified loop: ancestors + immediate parent"]
    B --> C["Root form layer - root manager values for sibling inheritance"]
    C --> D["Overlay - via _compute_overlay"]
```

## Key edge cases

- `refresh_single_placeholder` excludes the target field from the overlay so its `None` doesn’t shadow inherited parent/sibling values.
- Live context collection prefers subclass matches (e.g., `StepWellFilterConfig` values satisfy `WellFilterConfig` placeholders) via `_find_live_values_for_type`.
- `_user_set_fields` drives what flows into live context; `reset` keeps `None` in `_user_set_fields` so placeholders and preview labels stay consistent across windows.

## Deeper resolution flow

### Bulk/initial placeholder resolution (refresh_all_placeholders)

```mermaid
sequenceDiagram
    participant Manager
    participant Ops as ParameterOpsService
    participant Live as LiveContextService
    participant Stack as build_context_stack
    participant Lazy as LazyDefaultPlaceholderService
    participant Widget as PyQt6WidgetEnhancer

    Manager->>Ops: refresh_with_live_context(use_user_modified_only flag)
    Ops->>Live: collect(scope_filter, for_type=root_type)
    Live-->>Ops: LiveContextSnapshot (values, scoped_values)
    Ops->>Stack: build_context_stack(context_obj, overlay, live_context, root_form_values)
    Stack-->>Ops: ExitStack (global → parent chain → root form → overlay)
    Ops->>Lazy: get_lazy_resolved_placeholder(obj_type, field_name)
    Lazy-->>Ops: placeholder text (Default: X or Default: (none))
    Ops->>Widget: apply_placeholder_text(widget, text)
```

- Overlay: computed via `_compute_overlay(manager, use_user_modified_only)`.
- Root form values: pulled from live context when nested, for sibling inheritance.
- Stack layers: global, parent chain (ancestors + immediate parent), root form layer, overlay.
- Lazy resolution happens inside `LazyDefaultPlaceholderService` while the stack is active; it instantiates the lazy dataclass and reads the field to get the inherited value.

### Targeted single-field refresh (refresh_single_placeholder)

```mermaid
sequenceDiagram
    participant Manager
    participant Ops as ParameterOpsService
    participant Live as LiveContextService
    participant Stack as build_context_stack
    participant Lazy as LazyDefaultPlaceholderService
    participant Widget as PyQt6WidgetEnhancer

    Manager->>Ops: refresh_single_placeholder(field_name)
    Ops->>Live: collect(scope_filter, for_type=root_type)
    Live-->>Ops: LiveContextSnapshot
    Ops->>Stack: build_context_stack(..., overlay_without_field)
    Stack-->>Ops: ExitStack
    Ops->>Lazy: get_lazy_resolved_placeholder(obj_type, field_name)
    Lazy-->>Ops: placeholder text
    Ops->>Widget: apply_placeholder_text(widget, text)
```

- Uses `overlay_without_field` so the field’s own `None` doesn’t mask inherited values.
- Same stack layering and lazy resolution path as bulk refresh.

### Change-driven refresh path (user edits)

```mermaid
sequenceDiagram
    participant Widget
    participant Manager
    participant Dispatch as FieldChangeDispatcher
    participant Ops as ParameterOpsService
    participant Live as LiveContextService
    participant Other as Other managers

    Widget->>Manager: change signal (placeholder cleared)
    Manager->>Dispatch: FieldChangeEvent(field, value)
    Dispatch->>Manager: parameters[field] = value
    Dispatch->>Manager: add to _user_set_fields
    Dispatch->>Manager.parent: mark modified (collect_nested_value)
    alt value is None
        Dispatch->>Ops: refresh_single_placeholder on siblings
    end
    Dispatch->>Live: increment_token(notify=False)
    Dispatch->>Live: _notify_change()
    Live->>Other: callbacks fire (debounced in listener)
    Other->>Ops: refresh_with_live_context(...) to recompute placeholders
```

- LiveContextSnapshot contains only user-modified fields (including explicit `None`). Unresolved lazy values are not computed in the snapshot; they resolve during placeholder computation under the context stack.
- `use_user_modified_only=False` is typical for normal refreshes; `True` is used selectively to avoid `None` overlays masking inherited defaults.

### Bulk vs targeted (side-by-side)

```mermaid
flowchart LR
    subgraph Bulk: refresh_with_live_context
        B1[collect live_context] --> B2["_compute_overlay(use_user_modified_only)"]
        B2 --> B3["build_context_stack with overlay"]
        B3 --> B4[resolve placeholders for all None fields]
        B4 --> B5[recurse into nested managers]
    end
    subgraph Targeted: refresh_single_placeholder
        T1[collect live_context] --> T2["_compute_overlay(use_user_modified_only, exclude_field)"]
        T2 --> T3[build_context_stack (overlay_without_field)]
        T3 --> T4[resolve placeholder for one field]
        T4 --> T5[no recursion]
    end
```

Key differences:
- Overlay: bulk uses full overlay; targeted excludes the changing field so its `None` doesn’t shadow inherited values.
- Scope: bulk refreshes all `None` fields and nested managers; targeted refreshes one field only.
- Cost: targeted skips recursion and field iteration, reducing work on sibling updates.

### build_context_stack (layer-by-layer)

```mermaid
flowchart TD
    A["Start build_context_stack"] --> B{Global layer?}
    B -->|is_global_config_editing| B1["global_config_type() masked None"]
    B -->|else if live_context has global| B2["live global from other window"]
    B -->|else| B3["thread-local base global"]
    B1 --> C
    B2 --> C
    B3 --> C
    C{context_obj present?} -->|yes| D["Parent chain loop: for each ancestor + immediate parent"]
    C -->|no| E["skip parent chain"]
    D --> F["_inject_context_layer: live preferred, stored fallback for immediate parent"]
    E --> G
    F --> G{root_form_values present?}
    G -->|yes| H["_inject_context_layer for root form"]
    G -->|no| I["skip root form layer"]
    H --> J{overlay present?}
    I --> J
    J -->|yes| K["_inject_context_layer for overlay"]
    J -->|no| L["skip overlay"]
    K --> M["ExitStack ready"]
    L --> M
```

- Global layer is cached per dispatch cycle for performance.
- Parent chain uses unified `_inject_context_layer` helper for dataclass/SimpleNamespace handling.
- Root form layer supplies sibling inheritance (root form values from live context).
- Overlay via `_compute_overlay(manager, use_user_modified_only, exclude_field)`.

### get_lazy_resolved_placeholder internals

```mermaid
sequenceDiagram
    participant Ops as ParameterOpsService
    participant Lazy as LazyDefaultPlaceholderService
    participant Inst as Lazy dataclass instance

    Ops->>Lazy: get_lazy_resolved_placeholder(dataclass_type, field_name, prefix)
    alt dataclass_type not lazy
        Lazy->>Lazy: try _get_lazy_type_for_base()
        alt lazy type found
            Lazy->>Lazy: switch to lazy type
        else
            Lazy->>Lazy: _get_class_default_placeholder()
            Lazy-->>Ops: formatted text
        end
    end
    Lazy->>Inst: create instance (dataclass_type())
    Inst-->>Lazy: __getattribute__ resolves field using context stack
    Lazy->>Lazy: _format_placeholder_text(resolved_value, prefix)
    Lazy-->>Ops: placeholder text (e.g., "Default: 2" or "Default: (none)")
```

- Resolution happens with `config_context` layers already active from `build_context_stack`.
- If the type is lazy, field access triggers its resolver to apply inheritance.
- Formatting handles enums, lists, nested dataclasses, and `(none)` for None.

### build_context_stack call path (who sets the stack)

```mermaid
sequenceDiagram
    participant Ops as ParameterOpsService
    participant Live as LiveContextService
    participant Stack as build_context_stack
    participant Ctx as config_context (contextvars)

    Ops->>Live: collect(scope_filter, for_type=root_type)
    Live-->>Ops: LiveContextSnapshot (values)
    Ops->>Stack: build_context_stack(context_obj, overlay, live_context, root_form_values, root_form_type)
    Stack-->>Ops: ExitStack
    Ops->>Ctx: enter stacked config_context layers (global → parent chain → root form → overlay)
    Ctx-->>Ops: contextvars current_temp_global set
    Ops->>Lazy: get_lazy_resolved_placeholder(...)
```

The stack is entered before calling `LazyDefaultPlaceholderService`, so the lazy dataclass resolves under those contextvars layers.

### Lazy placeholder resolution with contextvars

```mermaid
sequenceDiagram
    participant Ops as ParameterOpsService
    participant Lazy as LazyDefaultPlaceholderService
    participant Inst as Lazy dataclass instance
    participant Ctx as config_context (contextvars)

    Ctx-->>Lazy: current_temp_global includes overlay + parent layers
    Ops->>Lazy: get_lazy_resolved_placeholder(dataclass_type, field_name, prefix)
    alt dataclass_type is non-lazy
        Lazy->>Lazy: try _get_lazy_type_for_base()
        else Lazy: fallback to _get_class_default_placeholder() for class defaults
    end
    Lazy->>Inst: create dataclass_type() (lazy __getattribute__ uses current_temp_global)
    Inst-->>Lazy: resolved_value for field_name (inheritance applied)
    Lazy->>Lazy: _format_placeholder_text(resolved_value, prefix)
    Lazy-->>Ops: placeholder text
```

### What `_get_class_default_placeholder()` does

- Location: `openhcs/core/lazy_placeholder_simplified.py`.
- Used when the type is not lazy and no lazy equivalent exists.
- Reads the class attribute default (without instantiating) and formats it with the prefix, returning `None` if no default is found.
