# plan_01_psygnal_migration.md
## Component: Signal Infrastructure Unification

### Objective

Replace hand-rolled callback lists in ObjectStateRegistry with psygnal Signals. This is a surgical migration — not a rewrite of all Qt signals. The rot is specifically in `object_state.py` where we maintain 8 callback lists with 24 boilerplate methods.

### The Rot

```python
# openhcs/config_framework/object_state.py — 8 callback lists, 24 methods

# CLASS-LEVEL (ObjectStateRegistry) — 5 lists
_on_register_callbacks: List[Callable[[str, 'ObjectState'], None]] = []
_on_unregister_callbacks: List[Callable[[str, 'ObjectState'], None]] = []
_on_time_travel_complete_callbacks: List[Callable[[List[Tuple], Optional[str]], None]] = []
_on_history_changed_callbacks: List[Callable[[], None]] = []
_change_callbacks: List[Callable[[], None]] = []

# INSTANCE-LEVEL (ObjectState) — 3 lists per instance
_on_state_changed_callbacks: List[Callable[[], None]] = []
_on_resolved_changed_callbacks: List[Callable[[Set[str]], None]] = []
_on_time_travel_callbacks: List[Callable[[], None]] = []

# Each list requires 3 methods:
#   add_*_callback(), remove_*_callback(), _fire_*_callbacks()
# Plus manual dead callback detection: if "deleted" in str(e).lower()
```

### The Solution: psygnal

```python
from psygnal import Signal

class ObjectStateRegistry:
    # Class-level signals (replace 5 callback lists)
    registered = Signal(str, object)           # (scope_id, ObjectState)
    unregistered = Signal(str, object)         # (scope_id, ObjectState)
    history_changed = Signal()                 # no args
    time_travel_complete = Signal(list, str)   # (dirty_states, triggering_scope)
    changed = Signal()                         # token incremented

class ObjectState:
    # Instance-level signals (replace 3 callback lists)
    resolved_changed = Signal(set)             # Set[str] changed paths
    state_changed = Signal()                   # dirty/sig-diff changed
    time_traveled = Signal()                   # restored via time-travel
```

**What psygnal provides:**
- `.connect(callback)` — subscribe
- `.disconnect(callback)` — unsubscribe
- `.emit(*args)` — fire
- Automatic weak reference cleanup (no more `if "deleted" in str(e).lower()`)
- Type-checked arguments
- Thread safety

### Caller Enumeration (Complete)

**ObjectStateRegistry class-level signals:**

| Signal | Caller | File | Line |
|--------|--------|------|------|
| `registered` | `AbstractManagerWidget._on_registry_register` | `abstract_manager_widget.py` | 452 |
| `unregistered` | `AbstractManagerWidget._on_registry_unregister` | `abstract_manager_widget.py` | 451 |
| `unregistered` | `MainWindow._on_object_state_unregistered` | `main.py` | 591 |
| `time_travel_complete` | `MainWindow._on_time_travel_complete` | `main.py` | 587 |
| `history_changed` | `TimeTravelWidget._update_ui` | `time_travel_widget.py` | 49 |
| `history_changed` | `SnapshotBrowserWindow._on_refresh` | `snapshot_browser_window.py` | 128 |
| `changed` | `ParameterFormManager._on_live_context_changed` | `parameter_form_manager.py` | 267 |

**ObjectState instance-level signals:**

| Signal | Caller | File | Line |
|--------|--------|------|------|
| `resolved_changed` | `ParameterFormManager._on_resolved_values_changed` | `parameter_form_manager.py` | 328 |
| `resolved_changed` | `FunctionListEditor.on_resolved_changed` | `function_list_editor.py` | 749 |
| `state_changed` | `ParameterFormManager._on_state_changed` | `parameter_form_manager.py` | 335 |
| `state_changed` | `ConfigHierarchyTree.on_state_changed` | `config_hierarchy_tree.py` | 206 |

### Plan

**Step 1: Add psygnal dependency**
```bash
uv add psygnal
```

**Step 2: Replace ObjectStateRegistry class-level signals**

Before:
```python
_on_register_callbacks: List[Callable[[str, 'ObjectState'], None]] = []

@classmethod
def add_register_callback(cls, callback):
    if callback not in cls._on_register_callbacks:
        cls._on_register_callbacks.append(callback)

@classmethod
def _fire_register_callbacks(cls, scope_key, state):
    for callback in cls._on_register_callbacks:
        try:
            callback(scope_key, state)
        except Exception as e:
            logger.warning(f"Error in register callback: {e}")
```

After:
```python
registered = Signal(str, object)  # (scope_id, ObjectState)

# In register():
cls.registered.emit(key, state)
```

**Step 3: Update callers**

Before:
```python
ObjectStateRegistry.add_unregister_callback(self._on_registry_unregister)
```

After:
```python
ObjectStateRegistry.unregistered.connect(self._on_registry_unregister)
```

**Step 4: Replace ObjectState instance-level signals**

Before:
```python
self._on_resolved_changed_callbacks: List[Callable[[Set[str]], None]] = []

def on_resolved_changed(self, callback):
    if callback not in self._on_resolved_changed_callbacks:
        self._on_resolved_changed_callbacks.append(callback)
```

After:
```python
self.resolved_changed = Signal(set)

# Callers:
state.resolved_changed.connect(self._on_resolved_values_changed)
```

### Cleanup — DELETE ALL OF THIS

**From `ObjectStateRegistry` (class-level):**
```python
# DELETE these 5 lists:
_on_register_callbacks: List[...]
_on_unregister_callbacks: List[...]
_on_time_travel_complete_callbacks: List[...]
_on_history_changed_callbacks: List[...]
_change_callbacks: List[...]

# DELETE these 15 methods:
add_register_callback(), remove_register_callback(), _fire_register_callbacks()
add_unregister_callback(), remove_unregister_callback(), _fire_unregister_callbacks()
add_time_travel_complete_callback(), remove_time_travel_complete_callback()
add_history_changed_callback(), remove_history_changed_callback(), _fire_history_changed_callbacks()
connect_listener(), disconnect_listener(), _fire_change_callbacks()
```

**From `ObjectState` (instance-level):**
```python
# DELETE these 3 lists:
_on_state_changed_callbacks: List[...]
_on_resolved_changed_callbacks: List[...]
_on_time_travel_callbacks: List[...]

# DELETE these 9 methods:
on_state_changed(), off_state_changed(), _notify_state_changed()
on_resolved_changed(), off_resolved_changed()
on_time_travel(), off_time_travel()
```

**Estimated deletion:** ~120 lines of boilerplate

**No wrappers. No backwards compatibility.**
- All `add_*_callback()` → `.connect()`
- All `remove_*_callback()` → `.disconnect()`
- All `_fire_*_callbacks()` → `.emit()`
- If a caller uses old API, it fails loud — update the caller

### ❌ ANTIPATTERNS TO AVOID

**DO NOT create wrapper methods:**
```python
# ❌ WRONG: Wrapper that calls the signal
def add_register_callback(cls, callback):
    cls.registered.connect(callback)  # DON'T DO THIS
```
Callers must use `.connect()` directly. Delete the wrapper entirely.

**DO NOT keep old lists "for compatibility":**
```python
# ❌ WRONG: Keeping both systems
registered = Signal(str, object)
_on_register_callbacks: List[...] = []  # DON'T KEEP THIS
```
Delete the lists. There is no transition period.

**DO NOT create adapter classes:**
```python
# ❌ WRONG: Adapter pattern
class SignalAdapter:
    def __init__(self, signal):
        self.signal = signal
    def add_callback(self, cb):
        self.signal.connect(cb)
```
This is the same boilerplate with extra steps. Delete it.

**DO NOT add try/except for "gradual migration":**
```python
# ❌ WRONG: Fallback to old system
try:
    ObjectStateRegistry.registered.connect(callback)
except AttributeError:
    ObjectStateRegistry.add_register_callback(callback)  # DON'T
```
There is no gradual migration. Old API fails loud. Fix the caller.

### Out of Scope

- Qt `pyqtSignal` in GUI widgets — stays as-is (already Qt-coupled)
- `GlobalEventBus` — stays as-is (already Qt-coupled)
- `CustomFunctionSignals` — stays as-is (already Qt-coupled)

This plan is surgical: only `object_state.py` and its 11 callers.

### Implementation Draft

*(Only after smell loop passes)*
