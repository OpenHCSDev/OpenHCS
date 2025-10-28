# plan_05_migration_and_validation.md
## Component: Migration Strategy and Validation Framework

### Objective
Define the migration path from duck typing to protocol-based architecture, with validation framework to ensure no duck typing creeps back in.

### Migration Strategy

#### Phase 1: Foundation (Plans 01-02)
**Dependencies:** None
**Deliverables:**
1. Widget protocol ABCs (`widget_protocols.py`)
2. Widget registry metaclass (`widget_registry.py`)
3. Widget adapters for Qt widgets (`widget_adapters.py`)
4. Widget factory with type dispatch (`widget_factory.py`)
5. Widget dispatcher with protocol checks (`widget_dispatcher.py`)

**Validation:**
- All adapters auto-register via metaclass
- All adapters implement required protocols
- Factory creates correct widget for each type
- Dispatcher fails loud on protocol violations

#### Phase 2: Operations Layer (Plans 03-04)
**Dependencies:** Phase 1 complete
**Deliverables:**
1. Widget operations service (`widget_operations.py`)
2. Signal connection protocol implementation
3. ParameterFormManager simplification
4. Delete duck typing dispatch tables

**Validation:**
- All widget operations use protocol dispatch
- No `hasattr()` checks remain
- No attribute-based dispatch tables
- All signal connections use protocol

#### Phase 3: Cleanup and Validation (Plan 05)
**Dependencies:** Phase 2 complete
**Deliverables:**
1. Delete obsolete duck typing code
2. Add architectural validation tests
3. Update documentation
4. Performance benchmarks

**Validation:**
- Codebase grep for duck typing patterns returns zero
- All tests pass
- Performance equal or better than before

### Duck Typing Detection Framework

**File:** `tests/architecture/test_no_duck_typing.py`

Automated tests to prevent duck typing from returning:

```python
import ast
import os
from pathlib import Path
import pytest

class DuckTypingDetector(ast.NodeVisitor):
    """AST visitor that detects duck typing patterns."""
    
    def __init__(self):
        self.violations = []
    
    def visit_Call(self, node):
        """Detect hasattr() and getattr() calls."""
        if isinstance(node.func, ast.Name):
            # Detect hasattr(obj, 'attr')
            if node.func.id == 'hasattr':
                self.violations.append({
                    'type': 'hasattr',
                    'line': node.lineno,
                    'code': ast.unparse(node)
                })
            
            # Detect getattr(obj, 'attr', default)
            elif node.func.id == 'getattr' and len(node.args) == 3:
                self.violations.append({
                    'type': 'getattr_with_default',
                    'line': node.lineno,
                    'code': ast.unparse(node)
                })
        
        self.generic_visit(node)
    
    def visit_Try(self, node):
        """Detect try-except attribute access patterns."""
        # Check if try block accesses attributes
        for stmt in node.body:
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Attribute):
                # Check if except catches AttributeError
                for handler in node.handlers:
                    if handler.type and isinstance(handler.type, ast.Name):
                        if handler.type.id == 'AttributeError':
                            self.violations.append({
                                'type': 'try_except_attribute',
                                'line': node.lineno,
                                'code': ast.unparse(node)
                            })
        
        self.generic_visit(node)


def test_no_duck_typing_in_ui_layer():
    """
    Architectural test: UI layer must not use duck typing.
    
    Scans all UI files for duck typing patterns:
    - hasattr() checks
    - getattr() with defaults
    - try-except AttributeError patterns
    """
    ui_dirs = [
        'openhcs/ui',
        'openhcs/pyqt_gui',
        'openhcs/textual_tui'
    ]
    
    # Allowed exceptions (with justification)
    allowed_exceptions = {
        'openhcs/ui/shared/parameter_type_utils.py': [
            # Legacy compatibility - will be removed in Phase 3
            'has_dataclass_fields',
            'has_resolve_field_value'
        ],
    }
    
    violations = []
    
    for ui_dir in ui_dirs:
        ui_path = Path(ui_dir)
        if not ui_path.exists():
            continue
        
        for py_file in ui_path.rglob('*.py'):
            # Skip test files
            if 'test_' in py_file.name:
                continue
            
            # Parse file
            with open(py_file) as f:
                try:
                    tree = ast.parse(f.read(), filename=str(py_file))
                except SyntaxError:
                    continue
            
            # Detect duck typing
            detector = DuckTypingDetector()
            detector.visit(tree)
            
            # Filter allowed exceptions
            file_violations = detector.violations
            if str(py_file) in allowed_exceptions:
                allowed = allowed_exceptions[str(py_file)]
                file_violations = [
                    v for v in file_violations
                    if not any(a in v['code'] for a in allowed)
                ]
            
            if file_violations:
                violations.append({
                    'file': str(py_file),
                    'violations': file_violations
                })
    
    # Assert no violations
    if violations:
        error_msg = "Duck typing detected in UI layer:\n\n"
        for file_info in violations:
            error_msg += f"{file_info['file']}:\n"
            for v in file_info['violations']:
                error_msg += f"  Line {v['line']}: {v['type']}\n"
                error_msg += f"    {v['code']}\n"
        
        pytest.fail(error_msg)


def test_all_widgets_implement_protocols():
    """
    Architectural test: All widgets must implement required protocols.
    
    Verifies that every widget in WIDGET_IMPLEMENTATIONS:
    1. Implements ValueGettable and ValueSettable
    2. Has a valid _widget_id
    3. Is registered via WidgetMeta
    """
    from openhcs.ui.shared.widget_registry import WIDGET_IMPLEMENTATIONS, WIDGET_CAPABILITIES
    from openhcs.ui.shared.widget_protocols import ValueGettable, ValueSettable
    
    for widget_id, widget_class in WIDGET_IMPLEMENTATIONS.items():
        # Check _widget_id matches registry key
        assert hasattr(widget_class, '_widget_id'), \
            f"{widget_class.__name__} missing _widget_id attribute"
        assert widget_class._widget_id == widget_id, \
            f"{widget_class.__name__}._widget_id mismatch: {widget_class._widget_id} != {widget_id}"
        
        # Check implements core protocols
        assert issubclass(widget_class, ValueGettable), \
            f"{widget_class.__name__} must implement ValueGettable protocol"
        assert issubclass(widget_class, ValueSettable), \
            f"{widget_class.__name__} must implement ValueSettable protocol"
        
        # Check registered in capabilities
        assert widget_class in WIDGET_CAPABILITIES, \
            f"{widget_class.__name__} not registered in WIDGET_CAPABILITIES"


def test_no_dispatch_tables_in_ui():
    """
    Architectural test: No attribute-based dispatch tables allowed.
    
    Searches for patterns like:
    - WIDGET_UPDATE_DISPATCH = [('method_name', handler), ...]
    - WIDGET_GET_DISPATCH = [...]
    """
    ui_files = [
        'openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py',
        'openhcs/pyqt_gui/widgets/shared/widget_strategies.py',
    ]
    
    forbidden_patterns = [
        'WIDGET_UPDATE_DISPATCH',
        'WIDGET_GET_DISPATCH',
        'PLACEHOLDER_STRATEGIES',
        'SIGNAL_CONNECTIONS',
    ]
    
    violations = []
    
    for ui_file in ui_files:
        if not Path(ui_file).exists():
            continue
        
        with open(ui_file) as f:
            content = f.read()
        
        for pattern in forbidden_patterns:
            if pattern in content:
                violations.append(f"{ui_file}: Found forbidden pattern '{pattern}'")
    
    if violations:
        pytest.fail("Attribute-based dispatch tables found:\n" + "\n".join(violations))
```

### Performance Validation

**File:** `tests/performance/test_widget_protocol_performance.py`

Ensure protocol-based dispatch is not slower than duck typing:

```python
import pytest
import time
from openhcs.ui.shared.widget_adapters import LineEditAdapter, SpinBoxAdapter
from openhcs.ui.shared.widget_operations import WidgetOperations

def test_protocol_dispatch_performance():
    """
    Performance test: Protocol dispatch should be as fast as duck typing.
    
    Compares:
    - Protocol-based: isinstance() + method call
    - Duck typing: hasattr() + getattr() + method call
    """
    widget = LineEditAdapter()
    ops = WidgetOperations()
    
    # Warm up
    for _ in range(100):
        ops.set_value(widget, "test")
        ops.get_value(widget)
    
    # Benchmark protocol dispatch
    iterations = 10000
    start = time.perf_counter()
    for i in range(iterations):
        ops.set_value(widget, f"value_{i}")
        value = ops.get_value(widget)
    protocol_time = time.perf_counter() - start
    
    # Benchmark duck typing (for comparison)
    start = time.perf_counter()
    for i in range(iterations):
        if hasattr(widget, 'set_value'):
            widget.set_value(f"value_{i}")
        if hasattr(widget, 'get_value'):
            value = widget.get_value()
    duck_typing_time = time.perf_counter() - start
    
    # Protocol dispatch should be faster (no hasattr overhead)
    assert protocol_time <= duck_typing_time * 1.1, \
        f"Protocol dispatch slower than duck typing: {protocol_time:.4f}s vs {duck_typing_time:.4f}s"
```

### Documentation Updates

**File:** `docs/source/development/ui-architecture.rst`

Document the new architecture:

```rst
UI Architecture: Protocol-Based Widget System
==============================================

OpenHCS UI layer uses explicit protocol-based architecture, eliminating duck typing
in favor of fail-loud contracts.

Widget Protocols
----------------

All widgets implement explicit protocols defined in ``openhcs.ui.shared.widget_protocols``:

- **ValueGettable**: Widget can return a value via ``get_value()``
- **ValueSettable**: Widget can accept a value via ``set_value()``
- **PlaceholderCapable**: Widget can display placeholder text
- **RangeConfigurable**: Widget supports numeric range configuration
- **ChangeSignalEmitter**: Widget emits change signals

Widget Registration
--------------------

Widgets auto-register via ``WidgetMeta`` metaclass::

    class MyCustomWidget(QWidget, ValueGettable, ValueSettable, metaclass=WidgetMeta):
        _widget_id = "my_custom_widget"
        
        def get_value(self) -> Any:
            return self._internal_value
        
        def set_value(self, value: Any) -> None:
            self._internal_value = value

No Duck Typing
--------------

The UI layer **strictly prohibits** duck typing patterns:

❌ **Forbidden**::

    if hasattr(widget, 'set_value'):
        widget.set_value(value)

✅ **Required**::

    if isinstance(widget, ValueSettable):
        widget.set_value(value)
    else:
        raise TypeError(f"{type(widget)} does not implement ValueSettable")

This ensures:
- Compile-time type checking
- Fail-loud on protocol violations
- Discoverable implementations
- Refactoring safety
```

### Findings

**Migration Complexity:**

| Phase | Files Modified | Lines Changed | Risk Level |
|-------|---------------|---------------|------------|
| Phase 1 | 5 new files | +800 lines | Low (new code) |
| Phase 2 | 3 files | -1800, +400 | Medium (refactor) |
| Phase 3 | 10 files | -500 lines | Low (cleanup) |

**Total Impact:**
- **Net reduction:** ~1100 lines
- **Duck typing eliminated:** 100%
- **Protocol coverage:** All UI widgets

**Validation Coverage:**

1. **Static Analysis:**
   - AST parsing detects hasattr/getattr patterns
   - Grep for forbidden dispatch tables
   - Protocol implementation verification

2. **Runtime Validation:**
   - All widgets registered in WIDGET_IMPLEMENTATIONS
   - All widgets implement required protocols
   - Performance benchmarks pass

3. **Architectural Tests:**
   - No duck typing in UI layer
   - All widgets have explicit protocols
   - No attribute-based dispatch tables

### Implementation Draft

(Code will be written after smell loop approval)

