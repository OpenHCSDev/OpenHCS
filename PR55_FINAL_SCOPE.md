# PR #55 Reimplementation - Final Scope

## What to Build: ONLY Visual Feedback System

PR #55 reimplementation requires implementing **ONE feature**:

### Scope-Based Visual Feedback System
1. **Scope color generation** - MD5-based deterministic colors, WCAG AA compliant
2. **Flash animations** - Triggered when resolved values change (not raw changes)
3. **Layered borders** - Cycling tint factors and patterns for visual differentiation
4. **Integration** - Works with existing `EnabledFieldStylingService`

## What NOT to Build (Already Solved)

### Scope Infrastructure ✅
- `GlobalConfigBase` - Virtual base class for scope checking
- `scope_id` - String property on managers (e.g., `"/data/plates/plate_001::step_0"`)
- `get_root_from_scope_key()` - Scope specificity filtering
- `_is_scope_visible_static()` - Scope visibility checks
- Scope matching for cross-window synchronization
- Context hierarchy: Step → Pipeline → Global → Static defaults

### Caching & Performance ✅
- Already optimized by PR #44
- No new cache control needed
- No performance optimizations needed

### Bug Fixes ✅
- All 10 bugs from PR #55 fixed by PR #44 merge
- No bug fixes needed

## Implementation Plan

### Files to Create
- `openhcs/pyqt_gui/widgets/shared/services/scope_color_service.py` - Color generation
- `openhcs/pyqt_gui/widgets/flash_animation_service.py` - Flash animations
- `openhcs/pyqt_gui/widgets/layered_border_service.py` - Layered borders

### Files to Extend
- `openhcs/pyqt_gui/shared/color_scheme.py` - Add scope colors
- `openhcs/pyqt_gui/widgets/shared/services/enabled_field_styling_service.py` - Integrate visual feedback

## Architecture Principles (from PR #44)

1. **Fail-Loud** - Explicit errors, not silent failures
2. **ABC-Based Contracts** - Type safety over duck typing
3. **Service Layer** - Framework-agnostic business logic
4. **Declarative Configuration** - Reduce boilerplate
5. **Template Methods** - Hooks for customization
6. **Singletons** - Global registries with auto-cleanup

## Next Steps

1. Create detailed plan files following smell-loop process
2. Implement scope color service (MD5-based, WCAG AA)
3. Implement flash animation classes
4. Implement layered border styling
5. Integrate with `EnabledFieldStylingService`
6. Add tests for visual feedback system

