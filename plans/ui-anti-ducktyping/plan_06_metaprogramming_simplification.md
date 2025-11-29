# plan_06_metaprogramming_simplification.md
## Component: ParameterFormManager Metaprogramming Refactor

### Objective
Leverage OpenHCS metaprogramming patterns to reduce ParameterFormManager from 2667 lines to ~800 lines (70% reduction) by eliminating repeating patterns and boilerplate through:
1. Enum-driven widget creation dispatch
2. ABC-based widget creator strategies
3. Auto-generated recursive operations
4. Dataclass-based configuration
5. Registry pattern for widget creators

### Findings: Repeating Patterns Identified

#### 1. Widget Creation Boilerplate (5 similar methods, ~400 lines)

**Current Pattern:**
```python
def _create_regular_parameter_widget(self, param_info) -> QWidget:
    display_info = self.service.get_parameter_display_info(...)
    field_ids = self.service.generate_field_ids_direct(...)
    container = QWidget()
    layout = QHBoxLayout(container)
    label = LabelWithHelp(...)
    widget = self.create_widget(...)
    reset_button = _create_optimized_reset_button(...)
    self.widgets[param_info.name] = widget
    PyQt6WidgetEnhancer.connect_change_signal(...)
    return container

def _create_optional_regular_widget(self, param_info) -> QWidget:
    # 90% identical to above
    display_info = self.service.get_parameter_display_info(...)
    field_ids = self.service.generate_field_ids_direct(...)
    container = QWidget()
    # ... same pattern

def _create_nested_dataclass_widget(self, param_info) -> QWidget:
    # 80% identical to above
    display_info = self.service.get_parameter_display_info(...)
    # ... same pattern

def _create_optional_dataclass_widget(self, param_info) -> QWidget:
    # 85% identical to above
    display_info = self.service.get_parameter_display_info(...)
    # ... same pattern
```

**Metaprogramming Solution (Parametric - Mirrors _FRAMEWORK_CONFIG!):**

```python
from enum import Enum
from dataclasses import dataclass
from typing import Callable, Tuple, Optional

class WidgetCreationType(Enum):
    """Enum for widget creation strategies - mirrors MemoryType pattern."""
    REGULAR = "regular"
    OPTIONAL_REGULAR = "optional_regular"
    NESTED = "nested"
    OPTIONAL_NESTED = "optional_nested"

# ============================================================================
# WIDGET CREATION HANDLERS - Special-case logic (like framework handlers)
# ============================================================================

def _unwrap_optional_type(param_type: Type) -> Type:
    """Unwrap Optional[T] to get T."""
    return (
        ParameterTypeUtils.get_optional_inner_type(param_type)
        if ParameterTypeUtils.is_optional_dataclass(param_type)
        else param_type
    )

def _create_nested_form(manager, param_name: str, param_type: Type, current_value: Any) -> QWidget:
    """Handler for creating nested form."""
    unwrapped_type = _unwrap_optional_type(param_type)
    nested_manager = manager._create_nested_form_inline(param_name, unwrapped_type, current_value)
    return nested_manager.build_form()

# ============================================================================
# UNIFIED WIDGET CREATION CONFIGURATION (like _FRAMEWORK_CONFIG)
# ============================================================================

_WIDGET_CREATION_CONFIG = {
    WidgetCreationType.REGULAR: {
        # Metadata
        'layout_type': 'QHBoxLayout',
        'is_nested': False,

        # Widget creation operations (eval expressions or callables)
        'create_container': 'QWidget()',
        'setup_layout': 'layout.setSpacing(CURRENT_LAYOUT.parameter_row_spacing); layout.setContentsMargins(*CURRENT_LAYOUT.parameter_row_margins)',
        'create_main_widget': 'manager.create_widget(param_info.name, param_info.type, current_value, field_ids["widget_id"])',

        # Feature flags
        'needs_label': True,
        'needs_reset_button': True,
        'needs_checkbox': False,
        'needs_unwrap_type': False,
    },

    WidgetCreationType.NESTED: {
        # Metadata
        'layout_type': 'GroupBoxWithHelp',
        'is_nested': True,

        # Widget creation operations
        'create_container': 'GroupBoxWithHelp(title=display_info["field_label"], help_target=unwrapped_type, color_scheme=manager.config.color_scheme or PyQt6ColorScheme())',
        'setup_layout': None,  # GroupBox handles its own layout
        'create_main_widget': _create_nested_form,  # Callable handler

        # Feature flags
        'needs_label': False,
        'needs_reset_button': False,
        'needs_checkbox': False,
        'needs_unwrap_type': True,
    },

    WidgetCreationType.OPTIONAL_REGULAR: {
        # Metadata
        'layout_type': 'QVBoxLayout',
        'is_nested': False,

        # Widget creation operations
        'create_container': 'QWidget()',
        'setup_layout': None,  # Vertical layout doesn't need spacing
        'create_main_widget': 'manager.create_widget(param_info.name, param_info.type, current_value, field_ids["widget_id"])',

        # Feature flags
        'needs_label': True,
        'needs_reset_button': True,
        'needs_checkbox': True,
        'needs_unwrap_type': False,
    },

    WidgetCreationType.OPTIONAL_NESTED: {
        # Metadata
        'layout_type': 'GroupBoxWithHelp',
        'is_nested': True,

        # Widget creation operations
        'create_container': 'GroupBoxWithHelp(title=display_info["field_label"], help_target=unwrapped_type, color_scheme=manager.config.color_scheme or PyQt6ColorScheme())',
        'setup_layout': None,
        'create_main_widget': _create_nested_form,  # Callable handler

        # Feature flags
        'needs_label': False,
        'needs_reset_button': False,
        'needs_checkbox': True,
        'needs_unwrap_type': True,
    },
}

# Auto-generate widget creation operations from config
def _make_widget_operation(expr_str: str, creation_type: WidgetCreationType):
    """Create operation from expression string (like _make_lambda_with_name)."""
    if expr_str is None:
        return None

    # Create lambda with proper context
    lambda_expr = f'lambda manager, param_info, display_info, field_ids, current_value, unwrapped_type=None: {expr_str}'
    operation = eval(lambda_expr)
    operation.__name__ = f'{creation_type.value}_operation'
    return operation

_WIDGET_OPERATIONS = {
    creation_type: {
        op_name: (
            _make_widget_operation(expr, creation_type)
            if isinstance(expr, str)
            else expr  # Already a callable
        )
        for op_name, expr in config.items()
        if op_name in ['create_container', 'setup_layout', 'create_main_widget']
    }
    for creation_type, config in _WIDGET_CREATION_CONFIG.items()
}

# UNIFIED widget creation method (replaces 5 methods)
def _create_widget_for_param(self, param_info) -> QWidget:
    """UNIFIED: Single widget creation method using parametric dispatch."""
    # Determine creation type from param_info
    if param_info.is_optional and param_info.is_nested:
        creation_type = WidgetCreationType.OPTIONAL_NESTED
    elif param_info.is_nested:
        creation_type = WidgetCreationType.NESTED
    elif param_info.is_optional:
        creation_type = WidgetCreationType.OPTIONAL_REGULAR
    else:
        creation_type = WidgetCreationType.REGULAR

    # Get config and operations for this type
    config = _WIDGET_CREATION_CONFIG[creation_type]
    ops = _WIDGET_OPERATIONS[creation_type]

    # Prepare context
    display_info = self.service.get_parameter_display_info(
        param_info.name, param_info.type, param_info.description
    )
    field_ids = self.service.generate_field_ids_direct(self.config.field_id, param_info.name)
    current_value = self.parameters.get(param_info.name)
    unwrapped_type = _unwrap_optional_type(param_info.type) if config['needs_unwrap_type'] else None

    # Execute operations
    container = ops['create_container'](self, param_info, display_info, field_ids, current_value, unwrapped_type)

    # Setup layout
    layout_type = config['layout_type']
    if layout_type == 'QHBoxLayout':
        layout = QHBoxLayout(container)
    elif layout_type == 'QVBoxLayout':
        layout = QVBoxLayout(container)
    else:  # GroupBoxWithHelp
        layout = container.layout()

    if ops['setup_layout']:
        ops['setup_layout'](self, param_info, display_info, field_ids, current_value, unwrapped_type)

    # Add label if needed
    if config['needs_label']:
        label = LabelWithHelp(
            text=display_info['field_label'],
            param_name=param_info.name,
            param_description=display_info['description'],
            param_type=param_info.type,
            color_scheme=self.config.color_scheme or PyQt6ColorScheme()
        )
        layout.addWidget(label)

    # Add main widget
    main_widget = ops['create_main_widget'](self, param_info, display_info, field_ids, current_value, unwrapped_type)
    layout.addWidget(main_widget, 1)

    # Add reset button if needed
    if config['needs_reset_button'] and not self.read_only:
        reset_button = _create_optimized_reset_button(
            self.config.field_id,
            param_info.name,
            lambda: self.reset_parameter(param_info.name)
        )
        layout.addWidget(reset_button)
        self.reset_buttons[param_info.name] = reset_button

    # Store and connect (common to all)
    self.widgets[param_info.name] = main_widget
    PyQt6WidgetEnhancer.connect_change_signal(main_widget, param_info.name, self._emit_parameter_change)

    if self.read_only:
        self._make_widget_readonly(main_widget)

    return container
```

**Impact:** 5 methods (~400 lines) → 1 method + 1 config dict + 2 handlers (~100 lines) = **75% reduction**

**Key Insight:** PARAMETRIC pattern like `_FRAMEWORK_CONFIG`:
- Single source of truth: `_WIDGET_CREATION_CONFIG` (like `_FRAMEWORK_CONFIG`)
- Eval expressions for simple operations (like `'data.get()'` in memory system)
- Callable handlers for complex operations (like `_pyclesperanto_move_to_device`)
- Auto-generated operations from config (like `_TYPE_OPERATIONS`)
- Feature flags instead of hardcoded logic (like `'supports_dlpack': True`)
- Zero boilerplate - all behavior driven by config

---

#### 2. Recursive Operations Boilerplate (3 similar methods, ~50 lines)

**Current Pattern:**
```python
def _apply_all_styling_callbacks(self) -> None:
    """Recursively apply all styling callbacks."""
    for callback in self._styling_callbacks:
        callback()
    for param_name, nested_manager in self.nested_managers.items():
        nested_manager._apply_all_styling_callbacks()

def _apply_all_post_placeholder_callbacks(self) -> None:
    """Recursively apply all post-placeholder callbacks."""
    for callback in self._post_placeholder_callbacks:
        callback()
    for param_name, nested_manager in self.nested_managers.items():
        nested_manager._apply_all_post_placeholder_callbacks()

def _apply_to_nested_managers(self, operation_func: callable) -> None:
    """Apply operation to all nested managers."""
    for param_name, nested_manager in self.nested_managers.items():
        operation_func(param_name, nested_manager)
```

**Metaprogramming Solution:**

```python
from enum import Enum

class RecursiveOperation(Enum):
    """Enum for recursive operations on nested managers."""
    APPLY_STYLING = ("_styling_callbacks", "_apply_all_styling_callbacks")
    APPLY_POST_PLACEHOLDER = ("_post_placeholder_callbacks", "_apply_all_post_placeholder_callbacks")
    REFRESH_PLACEHOLDERS = (None, "_refresh_all_placeholders")
    REFRESH_ENABLED_STYLING = (None, "_refresh_enabled_styling")
    
    def __init__(self, callback_attr, method_name):
        self.callback_attr = callback_attr
        self.method_name = method_name

# Auto-generate recursive methods using type()
def _create_recursive_method(operation: RecursiveOperation):
    """Factory for creating recursive operation methods."""
    def recursive_method(self, *args, **kwargs):
        # Apply local callbacks if any
        if operation.callback_attr:
            for callback in getattr(self, operation.callback_attr, []):
                callback(*args, **kwargs)
        
        # Recurse to nested managers
        for param_name, nested_manager in self.nested_managers.items():
            getattr(nested_manager, operation.method_name)(*args, **kwargs)
    
    recursive_method.__name__ = operation.method_name
    recursive_method.__doc__ = f"Recursively {operation.method_name.replace('_', ' ')}."
    return recursive_method

# Auto-generate all recursive methods
for operation in RecursiveOperation:
    method = _create_recursive_method(operation)
    setattr(ParameterFormManager, operation.method_name, method)
```

**Impact:** 3 methods (~50 lines) → 1 factory + enum (~30 lines) = **40% reduction**

---

### Implementation Plan

#### Phase 1: Widget Creation Parametric Dispatch (MIRRORS _FRAMEWORK_CONFIG!)
1. Create `WidgetCreationType` enum
2. Create `_WIDGET_CREATION_CONFIG` dict (single source of truth, like `_FRAMEWORK_CONFIG`)
3. Create 2 handler functions for complex operations (like `_pyclesperanto_move_to_device`)
4. Create `_make_widget_operation()` to auto-generate operations from eval expressions
5. Auto-generate `_WIDGET_OPERATIONS` dict (like `_TYPE_OPERATIONS`)
6. Replace 5 widget creation methods with unified `_create_widget_for_param()`

#### Phase 2: Recursive Operations Auto-Generation
1. Create `RecursiveOperation` enum
2. Create `_create_recursive_method()` factory
3. Auto-generate recursive methods using `setattr()`
4. Delete manual recursive methods

#### Phase 3: Context Resolution Consolidation
1. Analyze context-related methods for common patterns
2. Create `ContextResolutionStrategy` ABC if needed
3. Consolidate context building/resolution logic

#### Phase 4: Cross-Window Communication Simplification
1. Extract cross-window logic to separate service class
2. Use signal/slot registry pattern
3. Eliminate manual event handler boilerplate

### Expected Impact

| Component | Before | After | Reduction |
|-----------|--------|-------|-----------|
| Widget Creation | 5 methods, ~400 lines | 1 method + config + 2 handlers, ~100 lines | **75%** |
| Recursive Operations | 3 methods, ~50 lines | 1 factory + enum, ~30 lines | **40%** |
| Context Resolution | ~200 lines | ~120 lines | **40%** |
| Cross-Window | ~150 lines | ~75 lines | **50%** |
| **Total** | **2667 lines** | **~775 lines** | **71%** |

#### 3. Context Building Boilerplate (~200 lines of nested conditionals)

**Current Pattern:**
```python
def _build_context_stack(self, overlay, skip_parent_overlay: bool = False, live_context: dict = None):
    """Build nested config_context() calls - 200+ lines of nested if/else."""
    stack = ExitStack()

    # Pattern 1: Global config handling
    is_root_global_config = (self.config.is_global_config_editing and ...)
    if is_root_global_config:
        static_defaults = self.global_config_type()
        stack.enter_context(config_context(static_defaults, mask_with_none=True))
    else:
        # Pattern 2: Live context handling
        if live_context and self.global_config_type:
            global_live_values = self._find_live_values_for_type(...)
            if global_live_values is not None:
                try:
                    # Reconstruct nested dataclasses
                    global_live_values = self._reconstruct_nested_dataclasses(...)
                    global_live_instance = dataclasses.replace(...)
                    stack.enter_context(config_context(global_live_instance))
                except Exception as e:
                    logger.warning(...)

    # Pattern 3: Parent context handling (repeated 3 times with slight variations)
    if self.context_obj is not None:
        if isinstance(self.context_obj, list):
            for ctx in self.context_obj:
                ctx_type = type(ctx)
                live_values = self._find_live_values_for_type(ctx_type, live_context)
                if live_values is not None:
                    try:
                        live_values = self._reconstruct_nested_dataclasses(live_values, ctx)
                        live_instance = dataclasses.replace(ctx, **live_values)
                        stack.enter_context(config_context(live_instance))
                    except:
                        stack.enter_context(config_context(ctx))
                else:
                    stack.enter_context(config_context(ctx))
        else:
            # SAME PATTERN REPEATED for single context
            ctx_type = type(self.context_obj)
            live_values = self._find_live_values_for_type(ctx_type, live_context)
            if live_values is not None:
                try:
                    live_values = self._reconstruct_nested_dataclasses(live_values, self.context_obj)
                    live_instance = dataclasses.replace(self.context_obj, **live_values)
                    stack.enter_context(config_context(live_instance))
                except Exception as e:
                    logger.warning(...)
                    stack.enter_context(config_context(self.context_obj))
            else:
                stack.enter_context(config_context(self.context_obj))

    # Pattern 4: Parent overlay handling
    if (not skip_parent_overlay and parent_manager and parent_manager._initial_load_complete):
        # ... 40 more lines of similar logic

    # Pattern 5: Overlay conversion (dict -> instance)
    if isinstance(overlay, dict):
        if not overlay and self.object_instance is not None:
            # ... 30 more lines

    return stack
```

**Metaprogramming Solution:**

```python
from enum import Enum
from dataclasses import dataclass
from typing import Optional, Any, List
from contextlib import ExitStack

class ContextLayerType(Enum):
    """Types of context layers in the resolution stack."""
    GLOBAL_STATIC_DEFAULTS = "global_static_defaults"
    GLOBAL_LIVE_VALUES = "global_live_values"
    PARENT_CONTEXT = "parent_context"
    PARENT_OVERLAY = "parent_overlay"
    CURRENT_OVERLAY = "current_overlay"

@dataclass
class ContextLayer:
    """Configuration for a single context layer."""
    layer_type: ContextLayerType
    instance: Any
    mask_with_none: bool = False

    def apply_to_stack(self, stack: ExitStack):
        """Apply this layer to the context stack."""
        from openhcs.config_framework.context_manager import config_context
        stack.enter_context(config_context(self.instance, mask_with_none=self.mask_with_none))

class ContextLayerBuilder(ABC):
    """ABC for building context layers."""

    @abstractmethod
    def can_build(self, manager: 'ParameterFormManager', **kwargs) -> bool:
        """Check if this builder can create a layer."""
        pass

    @abstractmethod
    def build(self, manager: 'ParameterFormManager', **kwargs) -> Optional[ContextLayer]:
        """Build the context layer."""
        pass

class GlobalStaticDefaultsBuilder(ContextLayerBuilder):
    """Builder for global static defaults layer."""
    _layer_type = ContextLayerType.GLOBAL_STATIC_DEFAULTS

    def can_build(self, manager, **kwargs) -> bool:
        return (manager.config.is_global_config_editing and
                manager.global_config_type is not None and
                manager.context_obj is None)

    def build(self, manager, **kwargs) -> Optional[ContextLayer]:
        static_defaults = manager.global_config_type()
        return ContextLayer(
            layer_type=self._layer_type,
            instance=static_defaults,
            mask_with_none=True
        )

class GlobalLiveValuesBuilder(ContextLayerBuilder):
    """Builder for global live values layer."""
    _layer_type = ContextLayerType.GLOBAL_LIVE_VALUES

    def can_build(self, manager, live_context=None, **kwargs) -> bool:
        return (live_context is not None and
                manager.global_config_type is not None and
                not (manager.config.is_global_config_editing and manager.context_obj is None))

    def build(self, manager, live_context=None, **kwargs) -> Optional[ContextLayer]:
        global_live_values = manager._find_live_values_for_type(
            manager.global_config_type, live_context
        )
        if global_live_values is None:
            return None

        try:
            from openhcs.config_framework.context_manager import get_base_global_config
            import dataclasses
            thread_local_global = get_base_global_config()
            if thread_local_global is not None:
                global_live_values = manager._reconstruct_nested_dataclasses(
                    global_live_values, thread_local_global
                )
                global_live_instance = dataclasses.replace(
                    thread_local_global, **global_live_values
                )
                return ContextLayer(
                    layer_type=self._layer_type,
                    instance=global_live_instance
                )
        except Exception as e:
            logger.warning(f"Failed to apply live GlobalPipelineConfig: {e}")
        return None

class ParentContextBuilder(ContextLayerBuilder):
    """Builder for parent context layer(s)."""
    _layer_type = ContextLayerType.PARENT_CONTEXT

    def can_build(self, manager, **kwargs) -> bool:
        return manager.context_obj is not None

    def build(self, manager, live_context=None, **kwargs) -> List[ContextLayer]:
        """Returns list of layers (one per parent context)."""
        contexts = manager.context_obj if isinstance(manager.context_obj, list) else [manager.context_obj]
        layers = []

        for ctx in contexts:
            layer = self._build_single_context(manager, ctx, live_context)
            if layer:
                layers.append(layer)

        return layers

    def _build_single_context(self, manager, ctx, live_context) -> Optional[ContextLayer]:
        """Build layer for a single parent context."""
        ctx_type = type(ctx)
        live_values = manager._find_live_values_for_type(ctx_type, live_context)

        if live_values is not None:
            try:
                live_values = manager._reconstruct_nested_dataclasses(live_values, ctx)
                import dataclasses
                live_instance = dataclasses.replace(ctx, **live_values)
                return ContextLayer(layer_type=self._layer_type, instance=live_instance)
            except Exception as e:
                logger.warning(f"Failed to apply live parent context: {e}")

        return ContextLayer(layer_type=self._layer_type, instance=ctx)

# Auto-register all builders using metaclass
class ContextLayerBuilderMeta(ABCMeta):
    """Metaclass for auto-registering context layer builders."""
    def __new__(cls, name, bases, attrs):
        new_class = super().__new__(cls, name, bases, attrs)
        if not getattr(new_class, '__abstractmethods__', None):
            layer_type = getattr(new_class, '_layer_type', None)
            if layer_type:
                CONTEXT_LAYER_BUILDERS[layer_type] = new_class()
        return new_class

CONTEXT_LAYER_BUILDERS: Dict[ContextLayerType, ContextLayerBuilder] = {}

# UNIFIED context building (replaces 200-line method)
def _build_context_stack(self, overlay, skip_parent_overlay: bool = False, live_context: dict = None):
    """UNIFIED: Build context stack using builder pattern."""
    stack = ExitStack()

    # Build layers in order
    for layer_type in ContextLayerType:
        builder = CONTEXT_LAYER_BUILDERS.get(layer_type)
        if not builder:
            continue

        if not builder.can_build(self, live_context=live_context, skip_parent_overlay=skip_parent_overlay):
            continue

        layers = builder.build(self, live_context=live_context, overlay=overlay)

        # Handle single layer or list of layers
        if isinstance(layers, list):
            for layer in layers:
                if layer:
                    layer.apply_to_stack(stack)
        elif layers:
            layers.apply_to_stack(stack)

    return stack
```

**Impact:** 1 method (~200 lines) → 1 method + 5 builders (~120 lines) = **40% reduction**

---

### Success Criteria

✅ All widget creation uses strategy pattern with enum dispatch
✅ All recursive operations auto-generated from enum
✅ Context building uses builder pattern with auto-registration
✅ Zero duplicate widget creation logic
✅ All strategies auto-register via metaclass
✅ Line count reduced by 65-70%
✅ All existing tests pass
✅ No duck typing introduced

---

## Implementation Summary

### Pattern 1: Widget Creation Parametric Dispatch ✅ COMPLETE

**Files Created:**
- `openhcs/pyqt_gui/widgets/shared/widget_creation_config.py` (298 lines)

**Files Modified:**
- `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py` (2668 → 2519 lines)

**Impact:**
- Deleted 3 widget creation methods (104 lines)
- Deleted 2 dead code functions (62 lines)
- Added parametric config (298 lines in separate file)
- Net reduction: 149 lines (5.6%)

**Commits:**
- `708244d` - Add widget_creation_config.py - parametric widget creation (Plan 06 Phase 1)
- `f0bb71a` - Integrate parametric widget creation into ParameterFormManager (Plan 06 Phase 2)
- `f52246b` - Delete dead code: _create_optional_regular_widget and helper (Plan 06 Phase 3)

### Pattern 3: Context Building Builder Pattern ✅ COMPLETE

**Files Created:**
- `openhcs/pyqt_gui/widgets/shared/context_layer_builders.py` (421 lines)

**Files Modified:**
- `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py` (2519 → 2348 lines)

**Impact:**
- Deleted 177 lines of nested if/else context building logic
- Replaced 205-line method with 7-line builder dispatch
- Added builder pattern (421 lines in separate file)
- Net reduction: 171 lines (6.8%)

**Commits:**
- `31f56b3` - Add context_layer_builders.py - builder pattern for context stack (Plan 06 Pattern 3 Phase 1)
- `48ac854` - Integrate builder pattern into ParameterFormManager._build_context_stack (Plan 06 Pattern 3 Phase 2)

### Cumulative Impact

| Metric | Before | After | Reduction |
|--------|--------|-------|-----------|
| ParameterFormManager Lines | 2668 | 2348 | **320 lines (12.0%)** |
| Widget Creation Methods | 5 | 1 | **80%** |
| Context Building Lines | 205 | 7 | **96.6%** |
| New Files Created | 0 | 2 | widget_creation_config.py, context_layer_builders.py |

**Pattern 2 (Recursive Operations) still pending** - estimated additional 20-30 line reduction.
