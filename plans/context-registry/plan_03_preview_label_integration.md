# plan_03_preview_label_integration.md
## Component: Preview Label Integration with Registry

### Objective

Migrate preview label resolution to use ContextStackRegistry. Preview labels will:
- **Read** from registry for resolved values
- **React** to registry.value_changed signal for updates
- **No longer** resolve through separate LiveContextResolver path

### Plan

1. **Replace `_resolve_preview_field_value()`**
   - Call `registry.resolve(scope_id, field_path)` instead of building context
   - Remove `_resolve_config_attr()` calls
   - Remove `LiveContextResolver` usage in abstract_manager_widget

2. **Replace `_build_preview_labels()`**
   - Iterate enabled preview fields
   - Call `registry.resolve()` for each field
   - Format and return labels

3. **React to registry changes**
   - Connect to `registry.value_changed` signal
   - On ANY value change for a scope, refresh ALL preview fields for that scope
   - Preview labels don't cache - they just call `registry.resolve()` for each field when rendering
   - This handles composite previews correctly (multiple fields contributing to label)
   - Use scope visibility to filter which items need update

4. **Remove deprecated code**
   - Remove `_live_context_resolver` from AbstractManagerWidget
   - Remove `CrossWindowPreviewMixin._on_live_context_changed()` (registry handles it)
   - Simplify `_handle_full_preview_refresh()` to use registry

### Rollout and Testing

- Executed immediately after plan_02; downstream listeners are updated here. End-to-end testing waits until plan_04 completion; no interim compatibility shims.

### Findings

**Current Preview Label Flow**:
- `_build_preview_labels()` iterates enabled fields
- `_resolve_preview_field_value()` navigates dotted paths
- `_resolve_config_attr()` uses LiveContextResolver with context stack
- `CrossWindowPreviewMixin` listens to LiveContextService for changes

**Assumptions/Notes**:
- Preview labels are assumed to depend on the matching `field_path`. If any labels compose multiple fields, add a small dependency map or occasional full refresh to keep those labels in sync.

**Files to Modify**:
- `openhcs/pyqt_gui/widgets/shared/abstract_manager_widget.py`
- `openhcs/pyqt_gui/widgets/mixins/cross_window_preview_mixin.py`
- `openhcs/pyqt_gui/widgets/plate_manager.py`
- `openhcs/pyqt_gui/widgets/pipeline_editor.py`

### Implementation Draft

*To be written after plan_02 is implemented and smell loop approved*
