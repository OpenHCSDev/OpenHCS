# plan_01_psygnal_migration.md
## Component: Signal Infrastructure Unification

### Objective

Replace the fragmented signal/callback infrastructure with psygnal — a pure Python Qt-style signal library by Talley Lambert. Eliminate boilerplate, decouple core domain from Qt, and gain type-safe, leak-proof signals.

### Findings

#### Current State: Three Competing Paradigms

**1. Qt pyqtSignal (58 declarations across 25 files)**

```python
# PlateManager alone has 15 signals
plate_selected = pyqtSignal(str)
orchestrator_state_changed = pyqtSignal(str, str)
progress_started = pyqtSignal(int)
_execution_complete_signal = pyqtSignal(dict, str)
# ... 11 more

# Every widget reinvents signal patterns
# No shared infrastructure
# Type safety is theater: pyqtSignal(object) everywhere
```

**2. Manual Callback Lists (ObjectStateRegistry)**

```python
# 4 class-level callback lists
_on_register_callbacks: List[Callable[[str, 'ObjectState'], None]] = []
_on_unregister_callbacks: List[Callable[[str, 'ObjectState'], None]] = []
_on_time_travel_complete_callbacks: List[Callable[[List[Tuple], Optional[str]], None]] = []
_on_history_changed_callbacks: List[Callable[[], None]] = []
_change_callbacks: List[Callable[[], None]] = []

# 3 instance-level callback lists per ObjectState
_on_state_changed_callbacks: List[Callable[[], None]] = []
_on_resolved_changed_callbacks: List[Callable[[Set[str]], None]] = []
_on_time_travel_callbacks: List[Callable[[], None]] = []

# Every list requires 3 methods:
#   add_*_callback(), remove_*_callback(), _fire_*_callbacks()
# Manual dead callback detection: if "deleted" in str(e).lower()
```

**3. Global Singleton Signal Objects**

```python
# custom_function_signals.py
custom_function_signals = CustomFunctionSignals()  # QObject singleton

# GlobalEventBus - another QObject singleton
pipeline_changed = pyqtSignal(list)
config_changed = pyqtSignal(object)
step_changed = pyqtSignal(object)
```

#### The Problems

| Problem | Current | With psygnal |
|---------|---------|--------------|
| Qt coupling in core domain | ObjectStateRegistry imports no Qt, but has hand-rolled signal system | Pure Python signals - same pattern |
| Boilerplate explosion | 3 methods per callback list × 8 lists = 24 methods | 0 methods - Signal handles it |
| Memory leaks | Manual `if "deleted" in str(e).lower()` | Weak references by default |
| Type safety | `pyqtSignal(object)`, `List[Callable]` | `Signal(str, int)` - validated |
| Fragmentation | 3 paradigms, no unification | One paradigm everywhere |

#### What psygnal Provides

```python
from psygnal import Signal

class ObjectStateRegistry:
    # Class-level signals (replace 5 callback lists)
    register = Signal(str, object)          # scope_id, ObjectState
    unregister = Signal(str, object)        # scope_id, ObjectState
    history_changed = Signal()              # no args
    time_travel_complete = Signal(list, str)  # dirty_states, triggering_scope
    change = Signal()                       # token incremented

class ObjectState:
    # Instance-level signals (replace 3 callback lists)
    resolved_changed = Signal(set)          # Set[str] changed paths
    state_changed = Signal()                # dirty/sig-diff changed
    time_travel = Signal()                  # restored via time-travel
```

**Eliminated:**
- `add_register_callback()`, `remove_register_callback()`, `_fire_register_callbacks()`
- `add_unregister_callback()`, `remove_unregister_callback()`, `_fire_unregister_callbacks()`
- ... 18 more methods

**Gained:**
- Type-checked signal arguments
- Automatic weak reference cleanup
- Thread safety built-in
- Qt-compatible API (`.connect()`, `.emit()`, `.disconnect()`)

### Plan

**Phase 1: Add psygnal dependency**
- Add `psygnal` to pyproject.toml
- No code changes yet

**Phase 2: Migrate ObjectStateRegistry (core domain)**
- Replace 5 class-level `List[Callable]` with `Signal` attributes
- Replace `add_*_callback()` → `.connect()`
- Replace `remove_*_callback()` → `.disconnect()`
- Replace `_fire_*_callbacks()` → `.emit()`
- Update all callers (ParameterFormManager, TimeTravelWidget, etc.)

**Phase 3: Migrate ObjectState instance signals**
- Replace 3 instance-level callback lists with `Signal` attributes
- Same pattern: connect/disconnect/emit

**Phase 4: Assess Qt signal consolidation**
- GlobalEventBus could remain pyqtSignal (it's already Qt-coupled)
- OR migrate to psygnal for uniformity
- Decision: Keep pyqtSignal in GUI layer, psygnal in core domain

### Cleanup — DELETE ALL OF THIS

**Methods to DELETE from `ObjectStateRegistry`:**
```python
def add_register_callback(...)        # DELETE
def remove_register_callback(...)     # DELETE
def _fire_register_callbacks(...)     # DELETE
def add_unregister_callback(...)      # DELETE
def remove_unregister_callback(...)   # DELETE
def _fire_unregister_callbacks(...)   # DELETE
# ... and all other add_*/remove_*/_fire_* methods
```

**Methods to DELETE from `ObjectState`:**
```python
def add_state_changed_callback(...)   # DELETE
def remove_state_changed_callback(...) # DELETE
def _fire_state_changed_callbacks(...) # DELETE
# ... and all other callback list methods
```

**No wrappers. No backwards compatibility.**
- All `add_*_callback()` calls → `.connect()`
- All `remove_*_callback()` calls → `.disconnect()`
- All `_fire_*_callbacks()` calls → `.emit()`
- If a caller uses the old API, it fails loud — update the caller

### Implementation Draft

*(Only after smell loop passes)*

