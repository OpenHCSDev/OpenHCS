# plan_06_collection_aware_object_state.md (UPDATED FOR PYQT6)
## Component: Seal ObjectState Abstraction - Complete Hierarchy

### Objective

Make ObjectState the **git of runtime state**. Fix time travel bugs by ensuring ALL parent-child relationships are tracked as ObjectState parameters. No external dicts. Single source of truth. Correctness by construction.

### Problem Analysis

**The Bug**: Time travel causes step lists to merge/disappear across timelines.

**Root Cause**: Multiple sources of truth. ObjectStateRegistry is managed by time travel, but external dicts are not:

| Parent → Child | Currently Tracked By | ObjectState? |
|----------------|---------------------|--------------|
| Root → Plates | `plates: List[Dict]` in PlateManager | ❌ |
| Plate → PipelineConfig | `plate_configs[plate_path]` dict | ⚠️ (ObjectState exists but dict still used) |
| Plate → Pipeline | implicit (plate_path used as key) | ❌ |
| Pipeline → Steps | `plate_pipelines[plate_path]` dict | ❌ |
| Step → (config) | ObjectState per FunctionStep | ✅ |

Time travel restores ObjectState parameters correctly, but these dicts accumulate state from all timelines.

**Current ObjectState usage** (PyQt6):
- ✅ PipelineConfig: ObjectState registered per plate (scope_id = plate_path)
- ✅ FunctionStep: ObjectState registered per step (scope_id = `{plate}::step_N`)
- ❌ Hierarchy relationships: NOT in ObjectState - stored in dicts

**Files involved**:
- [openhcs/pyqt_gui/widgets/plate_manager.py](openhcs/pyqt_gui/widgets/plate_manager.py) - Lines 127-137 define dicts
- [openhcs/pyqt_gui/widgets/pipeline_editor.py](openhcs/pyqt_gui/widgets/pipeline_editor.py) - Lines 204-207 define dicts

### The Abstraction: ObjectState IS the Hierarchy

**Principle**: If something needs tracked state, it's an ObjectState. Parent-child relationships are parameters.

**Current Hierarchy** (PyQt6):
```
PlateManager
  └── plates: List[Dict] = [{'name': str, 'path': str}, ...]
      ├── orchestrators[plate_path] = PipelineOrchestrator(...)
      ├── plate_configs[plate_path] = PipelineConfig(...)  ← ObjectState exists, dict is cache
      └── plate_pipelines[plate_path] = List[FunctionStep]  ← LEAK (in PipelineEditor)

PipelineEditor
  ├── pipeline_steps: List[FunctionStep]  ← Current plate (derived from plate_pipelines)
  └── plate_pipelines[plate_path] = [step1, step2, ...]  ← LEAK
```

**Target Hierarchy** (ObjectState sealed):
```
RootState ObjectState (scope: "")
  └── plate_scope_ids: List[str] = ["plate_A", "plate_B"]

PlateState ObjectState (scope: "plate_A" = plate_path)
  └── plate_path: str = "/path/to/plate"
  └── name: str = "plate1"
  └── pipeline_scope_id: str = "plate_A::pipeline"
  # PipelineConfig already ObjectState - no changes needed
  # Orchestrator NOT stored - recreated on-demand from PlateState

Pipeline ObjectState (scope: "plate_A::pipeline")
  └── name: str = "pipeline_for_plate_A"  (existing field)
  └── description: str (existing field)
  └── metadata: dict (existing field)
  └── step_scope_ids: List[str] = ["plate_A::step_0", "plate_A::step_1"]  (NEW - added field)
  # Pipeline inherits from list, but we track scope_ids not actual steps

FunctionStep ObjectState (scope: "plate_A::step_0")
  └── (already tracked - FunctionStep.func, configs, etc.)
```

**Operations become parameter mutations**:
- Add plate → update root's `plate_scope_ids` + register PlateState
- Add step → update pipeline's `step_scope_ids` + register FunctionStep
- Reorder → update list order in parameters
- Delete → remove from parent's list + cascade unregister

**All captured in snapshots. Time travel restores everything.**

### Why Explicit Schemas? (Rationale)

**Question**: Why create new classes instead of tracking dicts/lists directly in ObjectState?

**Answer**: ObjectState tracks **configuration objects with schemas**, not arbitrary data structures.

**What breaks if we track dicts/lists?**
1. **No type schema**: `dict` tells you nothing about what keys exist or what they mean
2. **No MRO**: Dicts don't have inheritance chains for resolution
3. **Ambiguous nesting**: `{'a': {'b': 1}}` - is that `a.b` or a dict-valued parameter?
4. **No declaration**: From the Manifesto - "Declarative Supremacy" - configuration IS documentation

**The principle**: If something is important enough to track with ObjectState, it's important enough to **declare what it is**.

```python
# NOT declarative - ad-hoc data, must guess what keys exist
{'name': 'plate1', 'path': '/path'}

# Declarative - schema is explicit, inspectable, type-checkable
@dataclass
class PlateState:
    name: str
    path: str
```

ObjectState is built around **object-oriented semantics**: attributes, MRO, classes, instances. It walks MRO chains and context stacks. This only makes sense for objects with schemas, not data structures.

**The "indirection" of creating PlateState isn't indirection - it's making implicit structure explicit.**

### Data Model

Define the container objects that ObjectState will wrap:

```python
# File: openhcs/config_framework/collection_containers.py (NEW)

from dataclasses import dataclass, field
from typing import List

@dataclass
class RootState:
    """Root container tracking all plates in the application.

    ObjectState wraps this to make plate_scope_ids a tracked parameter.
    No methods - pure data container.

    WHY THIS EXISTS: No Root class exists. We need something to track the plate list.
    """
    plate_scope_ids: List[str] = field(default_factory=list)


@dataclass
class PlateState:
    """Per-plate container tracking plate identity and pipeline reference.

    ObjectState wraps this to track plate metadata and pipeline relationship.
    Orchestrator is NOT stored here - recreated on-demand from plate_path.

    This REPLACES the Dict entries in PlateManager.plates:
        OLD: {'name': 'plate1', 'path': '/path/to/plate1'}
        NEW: PlateState(name='plate1', plate_path='/path/to/plate1', ...)

    WHY THIS EXISTS: Plates are currently dicts. No Plate class exists.
    Dicts can't be tracked by ObjectState (no schema, no MRO, no declaration).
    """
    name: str  # Display name (e.g., "plate1")
    plate_path: str  # Absolute path to plate directory (immutable identity, used as scope_id)
    pipeline_scope_id: str  # e.g., "/path/to/plate::pipeline"
```

**Why NOT PipelineState?** Pipeline class already exists ([openhcs/core/pipeline/\_\_init\_\_.py:31](openhcs/core/pipeline/__init__.py#L31)):

```python
class Pipeline(list):
    """Behaves like List[AbstractStep] but carries metadata."""
    def __init__(self, steps=None, *, name=None, metadata=None, description=None):
        super().__init__(steps or [])
        self.name = name or f"Pipeline_{id(self)}"
        self.description = description
        self.metadata = metadata or {}
```

We'll **use Pipeline directly** and add a `step_scope_ids` attribute. No new class needed.

**Why NOT store orchestrator?** PipelineOrchestrator has:
- Runtime state (OrchestratorState enum, caches, visualizers)
- Heavyweight objects (StorageRegistry, FileManager, MetadataCache)
- Created on Init Plate, destroyed on close
- Not configuration - it's a runtime execution engine

**Strategy**: Orchestrator is ephemeral. Recreate on-demand from PlateState.plate_path when needed. Time travel doesn't need to restore orchestrator internals - just the plate path and pipeline steps.

### Plan

**Phase ordering**: Build container dataclasses (Phase 1), migrate to ObjectState incrementally (Phases 2-4), handle orchestrators (Phase 5).

**CRITICAL**: Children[T] descriptor is OPTIONAL refinement (Phase 6). Phases 2-4 use manual parameter management (`get_parameter`, `update_parameter`). Works with existing ObjectState, no new abstractions required.

#### Phase 1: Create Container Dataclasses

**File**: `openhcs/config_framework/collection_containers.py` (NEW)

Create RootState and PlateState as shown in Data Model section above.

**No dependencies**. These are pure data containers. Can implement and test in isolation.

**Note**: We do NOT create PipelineState - Pipeline class already exists at [openhcs/core/pipeline/\_\_init\_\_.py:31](openhcs/core/pipeline/__init__.py#L31). We'll use it directly.

#### Phase 2: Root ObjectState for Plates

**File**: [openhcs/pyqt_gui/widgets/plate_manager.py](openhcs/pyqt_gui/widgets/plate_manager.py)

**Current code (lines 127-128)**:
```python
self.plates: List[Dict] = []  # LEAK: not tracked by time travel
self.selected_plate_path: str = ""
```

**Changes**:

```python
from openhcs.config_framework.collection_containers import RootState, PlateState

ROOT_SCOPE_ID = ""

def __init__(self):
    # ... existing init ...

    # DELETE: self.plates = []
    # Root state tracks all plates via ObjectState
    self._ensure_root_state()

    # Keep: self.selected_plate_path (selection is ephemeral, not configuration)
    # Keep: self.orchestrators (Phase 5 will handle)
    # Keep: self.plate_configs (already has ObjectState, dict is cache - Phase 5)

def _ensure_root_state(self) -> ObjectState:
    """Get or create root ObjectState tracking all plates."""
    state = ObjectStateRegistry.get_by_scope(ROOT_SCOPE_ID)
    if not state:
        root = RootState()  # Empty plate list initially
        state = ObjectState(object_instance=root, scope_id=ROOT_SCOPE_ID)
        ObjectStateRegistry.register(state)
    return state

def _add_plate(self, name: str, plate_path: str) -> None:
    """Add plate - register PlateState ObjectState."""
    # Generate scope and pipeline scope
    plate_scope = plate_path  # Use path as scope (already unique)
    pipeline_scope = f"{plate_scope}::pipeline"

    # Create PlateState
    plate_state_obj = PlateState(
        name=name,
        plate_path=plate_path,
        pipeline_scope_id=pipeline_scope
    )

    # Register PlateState ObjectState
    plate_state = ObjectState(object_instance=plate_state_obj, scope_id=plate_scope)
    ObjectStateRegistry.register(plate_state)

    # Update root's child references
    root_state = self._ensure_root_state()
    current = root_state.get_parameter("plate_scope_ids") or []
    root_state.update_parameter("plate_scope_ids", current + [plate_scope])

    # Update UI list (already have in AbstractManagerWidget.update_item_list)
    self.update_item_list()

def get_plates(self) -> List[PlateState]:
    """Derive plate list from root ObjectState. REPLACES self.plates."""
    root_state = ObjectStateRegistry.get_by_scope(ROOT_SCOPE_ID)
    if not root_state:
        return []

    plate_scope_ids = root_state.get_parameter("plate_scope_ids") or []
    plates = []
    for scope_id in plate_scope_ids:
        state = ObjectStateRegistry.get_by_scope(scope_id)
        if not state:
            raise KeyError(f"Plate ObjectState missing: {scope_id}")  # FAIL LOUD
        plates.append(state.object_instance)
    return plates

def _get_backing_items(self) -> List:
    """Override from AbstractManagerWidget - derive from ObjectState instead of self.plates."""
    return self.get_plates()
```

**Update ITEM_HOOKS** (lines 84-92):
```python
ITEM_HOOKS = {
    'id_accessor': ('attr', 'plate_path'),  # PlateState.plate_path instead of dict['path']
    'backing_attr': None,  # No backing attr - derived via _get_backing_items()
    'selection_attr': 'selected_plate_path',  # Keep selection ephemeral
    # ... rest unchanged ...
}
```

**Update _format_item_content()** (currently uses `item['name']`):
```python
def _format_item_content(self, item: PlateState) -> str:
    return item.name  # PlateState.name instead of dict['name']
```

**Delete**:
- `self.plates: List[Dict]` declaration (line 127)
- Any code that appends to `self.plates`

**Keep** (for now, Phase 5 will handle):
- `self.orchestrators` dict
- `self.plate_configs` dict (ObjectState already exists, dict is cache for faster lookup)

#### Phase 3: Pipeline ObjectState for Steps

**File**: [openhcs/pyqt_gui/widgets/pipeline_editor.py](openhcs/pyqt_gui/widgets/pipeline_editor.py)

**Current code (lines 204-207)**:
```python
self.pipeline_steps: List[FunctionStep] = []  # Current plate's steps
self.current_plate: str = ""
self.plate_pipelines: Dict[str, List[FunctionStep]] = {}  # LEAK
```

**Changes**:

```python
from openhcs.core.pipeline import Pipeline

def __init__(self):
    # ... existing init ...

    # DELETE: self.pipeline_steps = []
    # DELETE: self.plate_pipelines = {}

    # Keep: self.current_plate (ephemeral view state)

def _ensure_pipeline_state(self, plate_scope: str) -> ObjectState:
    """Get or create Pipeline ObjectState for plate."""
    pipeline_scope = f"{plate_scope}::pipeline"
    state = ObjectStateRegistry.get_by_scope(pipeline_scope)
    if not state:
        # Use existing Pipeline class, add step_scope_ids attribute
        pipeline = Pipeline(name=f"pipeline_for_{plate_scope}")
        pipeline.step_scope_ids = []  # NEW attribute for tracking scope IDs
        state = ObjectState(object_instance=pipeline, scope_id=pipeline_scope)
        ObjectStateRegistry.register(state)
    return state

def _add_step(self, step: FunctionStep) -> None:
    """Add step - register FunctionStep ObjectState and update pipeline."""
    step_scope = self._build_step_scope_id(step)  # Uses ScopeTokenService (line 658)

    # Register step ObjectState (already happens, just ensure scope is correct)
    # See _register_step_state() lines 682-702 - ALREADY EXISTS
    step_state = ObjectState(
        object_instance=step,
        scope_id=step_scope,
        parent_state=ObjectStateRegistry.get_by_scope(self.current_plate),
        exclude_params=['func']  # Exclude func from parameter extraction
    )
    ObjectStateRegistry.register(step_state)

    # NEW: Update pipeline's child references
    pipeline_state = self._ensure_pipeline_state(self.current_plate)
    current = pipeline_state.get_parameter("step_scope_ids") or []
    pipeline_state.update_parameter("step_scope_ids", current + [step_scope])

    # Update UI list (already exists in AbstractManagerWidget.update_item_list)
    self.update_item_list()

def get_steps(self, plate_scope: str) -> List[FunctionStep]:
    """Derive step list from Pipeline ObjectState. REPLACES plate_pipelines[plate_scope]."""
    pipeline_scope = f"{plate_scope}::pipeline"
    pipeline_state = ObjectStateRegistry.get_by_scope(pipeline_scope)
    if not pipeline_state:
        return []

    step_scope_ids = pipeline_state.get_parameter("step_scope_ids") or []
    return [ObjectStateRegistry.get_by_scope(sid).object_instance
            for sid in step_scope_ids]

def _get_backing_items(self) -> List:
    """Override from AbstractManagerWidget - derive from ObjectState instead of self.pipeline_steps."""
    if not self.current_plate:
        return []
    return self.get_steps(self.current_plate)

def set_current_plate(self, plate_path: str) -> None:
    """Switch to different plate - load its pipeline from ObjectState."""
    # ... existing cleanup code (lines 604-620) ...

    self.current_plate = plate_path

    # OLD (DELETE):
    # self.pipeline_steps = self.plate_pipelines.get(plate_path, [])

    # NEW: Derive from ObjectState (implicitly via _get_backing_items)
    # Just trigger UI refresh
    self.update_item_list()

    # ... existing flash invalidation (lines 621-629) ...
```

**Update ITEM_HOOKS** (lines 76-88):
```python
ITEM_HOOKS = {
    # ... most unchanged ...
    'backing_attr': None,  # No backing attr - derived via _get_backing_items()
    # ... rest unchanged ...
}
```

**Delete**:
- `self.pipeline_steps: List[FunctionStep]` declaration (line 204)
- `self.plate_pipelines: Dict[str, List[FunctionStep]]` declaration (line 207)
- Any code that mutates `self.plate_pipelines` or `self.pipeline_steps` directly

**Keep**:
- `self.current_plate` (ephemeral view state, not configuration)
- `self.selected_step` (ephemeral selection, not configuration)

#### Phase 4: Cascade Operations

**Delete with cascade** (PlateManager):
```python
def _perform_delete(self, items: List[PlateState]) -> None:
    """Delete plates - cascade unregister ObjectStates."""
    for plate in items:
        plate_scope = plate.plate_path

        # Remove from root's child references
        root_state = self._ensure_root_state()
        current = root_state.get_parameter("plate_scope_ids") or []
        root_state.update_parameter("plate_scope_ids",
            [s for s in current if s != plate_scope])

        # Cascade unregister (already exists in ObjectStateRegistry)
        # This automatically removes PlateState, Pipeline, all FunctionSteps
        ObjectStateRegistry.unregister_scope_and_descendants(plate_scope)

        # Clean up orchestrator cache (ephemeral)
        self.orchestrators.pop(plate_scope, None)

    # Update UI
    self.update_item_list()
```

**Reorder** (PipelineEditor):
```python
def _reorder_steps(self, new_order: List[FunctionStep]) -> None:
    """Reorder steps - update Pipeline.step_scope_ids."""
    if not self.current_plate:
        return

    # Build new scope_id list from new order
    # Use existing _build_step_scope_id() - scope_id is derived, not stored on step
    new_scope_ids = [self._build_step_scope_id(step) for step in new_order]

    # Update pipeline state
    pipeline_state = self._ensure_pipeline_state(self.current_plate)
    pipeline_state.update_parameter("step_scope_ids", new_scope_ids)

    # Update UI
    self.update_item_list()
```

#### Phase 5: Orchestrator Lifecycle

**Problem**: Orchestrators are runtime execution engines, not configuration. They shouldn't be in ObjectState.

**Current behavior**:
- Created on "Init Plate" action (lines 383-450 in plate_manager.py)
- Stored in `self.orchestrators[plate_path]`
- Has runtime state: OrchestratorState enum (CREATED → READY → COMPILED → EXECUTING)
- Has caches: MetadataCache, component keys, visualizers

**Solution**: Keep orchestrators dict as ephemeral cache. Clear on time travel.

**File**: [openhcs/pyqt_gui/widgets/plate_manager.py](openhcs/pyqt_gui/widgets/plate_manager.py)

```python
# Keep orchestrators dict (already declared line 129)
self.orchestrators: Dict[str, PipelineOrchestrator] = {}  # CACHE, not source of truth

def get_orchestrator(self, plate_scope: str) -> Optional[PipelineOrchestrator]:
    """Get orchestrator for plate, returning cached instance if exists."""
    # Check cache (already exists - this is current behavior)
    if plate_scope in self.orchestrators:
        return self.orchestrators[plate_scope]

    # Not cached - return None
    # Caller must Init Plate to create orchestrator
    return None

def _on_time_travel_complete(self, dirty_states, triggering_scope):
    """Clear orchestrator cache after time travel - force recreation.

    Hook into AbstractManagerWidget's time travel callback.
    """
    # Clear all orchestrators - they're tied to old timeline
    self.orchestrators.clear()

    # Note: PlateState.plate_path is restored by time travel
    # User must re-Init Plate to recreate orchestrator
    # This is CORRECT - orchestrator state (READY, COMPILED, etc) is ephemeral

    # Update button states (Init Plate button should be enabled)
    self.update_button_states()
```

**Similarly for plate_configs** (lines 131):
```python
# plate_configs is a CACHE for faster lookup
# Source of truth is ObjectState registered per plate
# Clear on time travel to force reload from ObjectState

def _on_time_travel_complete(self, dirty_states, triggering_scope):
    self.orchestrators.clear()
    self.plate_configs.clear()  # Force reload from ObjectState
    self.update_button_states()
```

**Rationale**:
- Orchestrators are recreated when needed (user clicks Init Plate)
- Time travel doesn't try to serialize/restore them
- They're derived from ObjectState (PlateState.plate_path + PipelineState.step_scope_ids)
- OrchestratorState enum is runtime execution state, not configuration

#### Phase 6: Children[T] Descriptor (OPTIONAL REFINEMENT)

**Status**: DEFERRED

The Children[T] descriptor (original plan lines 216-316) is an elegant abstraction:
```python
@dataclass
class RootState:
    plates: Children[PlateState]  # Declarative child management

root.plates.append(new_plate)  # Auto-registers, auto-updates scope_ids
```

**Challenges**:
1. Requires descriptor integration with dataclass fields
2. Needs `__set_name__` to capture field name
3. Must work with ObjectState parameter system
4. Additional complexity for marginal benefit over manual `get_parameter`/`update_parameter`

**Recommendation**: Implement Phases 1-5 first with manual parameter management. If the verbosity becomes painful, add Children[T] as a refinement. Manual approach works and is explicit.

**If implemented later**:
- Move scope_id generation logic into Children[T].append()
- Replace manual `get_parameter`/`update_parameter` calls with descriptor access
- Add type safety: `Children[PlateState]` enforces type at runtime

### Invariants

1. **ObjectState IS the abstraction**: Everything stateful is an ObjectState
2. **Hierarchy IS parameters**: Parent stores `child_scope_ids` as parameter
3. **Single source of truth**: ObjectStateRegistry only. No external dicts except caches.
4. **Derive, don't store**: UI reads from ObjectState via `_get_backing_items()`, never from local dicts
5. **Time travel = parameter restore**: All structure is parameters, all restored
6. **Fail loud**: `raise KeyError` if ObjectState missing, not silent `None` returns
7. **Ephemeral runtime**: Orchestrators are runtime engines, not configuration - clear on time travel

### What This Seals

| Leak | Sealed By | Lines Changed |
|------|-----------|---------------|
| `plates: List[Dict]` | Root ObjectState with `plate_scope_ids` | plate_manager.py:127-128 |
| `plate_configs` dict | Keep as cache, clear on time travel | plate_manager.py:131 |
| `plate_pipelines` dict | Pipeline ObjectState with `step_scope_ids` | pipeline_editor.py:207 |
| `pipeline_steps` list | Derive from Pipeline via `get_steps()` | pipeline_editor.py:204 |
| `orchestrators` dict | Keep as cache, clear on time travel | plate_manager.py:129 |

### Files to Create

1. [openhcs/config_framework/collection_containers.py](openhcs/config_framework/collection_containers.py) - RootState, PlateState dataclasses (NOT PipelineState - using existing Pipeline class)

### Files to Modify

1. [openhcs/pyqt_gui/widgets/plate_manager.py](openhcs/pyqt_gui/widgets/plate_manager.py) - Root + PlateState integration
2. [openhcs/pyqt_gui/widgets/pipeline_editor.py](openhcs/pyqt_gui/widgets/pipeline_editor.py) - Pipeline integration (add step_scope_ids attribute)
3. [openhcs/core/pipeline/\_\_init\_\_.py](openhcs/core/pipeline/__init__.py) - Pipeline class (add step_scope_ids attribute tracking - optional, could just set dynamically)

### Testing Strategy

**Invariant to verify**: After time travel, plate/pipeline/step hierarchy is restored from ObjectState, not accumulated from dicts.

**Test cases**:
1. Add plate → time travel back → plate disappears (ObjectState unregistered)
2. Add step → time travel back → step disappears from pipeline (step_scope_ids restored)
3. Add plate on branch A, time travel to common ancestor, add different plate on branch B → both branches preserve their own plates (no cross-contamination)
4. Time travel → orchestrators cleared → must re-Init Plate (ephemeral state not restored)
5. Delete step → cascade unregister → all child ObjectStates removed

**Smell loop targets**:
- Search for `self.plates` in plate_manager.py - ensure all replaced with `get_plates()`
- Search for `self.plate_pipelines` in pipeline_editor.py - ensure all replaced with `get_steps()`
- Search for `self.pipeline_steps` in pipeline_editor.py - ensure all replaced with derived access

### Open Questions

1. ~~**Scope ID sanitization**: plate_path has slashes and potentially colons. Use directly or escape?~~
   - **CLOSED**: `::` is not a valid file path character on any OS. Non-issue. Use path directly.

2. **PlateState additional fields**: Does PlateState need fields beyond name/plate_path/pipeline_scope_id?
   - Check if plate_configs dict stores additional metadata
   - If yes, migrate those fields into PlateState dataclass

3. **plate_configs dict**: Currently stores PipelineConfig per plate AND has ObjectState registered.
   - Is dict redundant? Can we always use ObjectStateRegistry.get_by_scope(plate_path)?
   - Recommendation: Keep dict as cache for now (Phase 5), validate no semantic difference

4. **Orchestrator state tracking**: Should OrchestratorState enum be in PlateState?
   - Current: Ephemeral, not persisted
   - Recommendation: Correct - execution state is runtime, not configuration
   - User can see state in UI, doesn't need time travel

### Next Steps

1. **Smell loop**: Read plate_manager.py and pipeline_editor.py in full to verify no additional state leaks
2. **Implement Phase 1**: Create collection_containers.py with dataclasses
3. **Implement Phase 2**: Root ObjectState + PlateState in plate_manager
4. **Implement Phase 3**: PipelineState in pipeline_editor
5. **Implement Phase 4**: Cascade delete + reorder operations
6. **Implement Phase 5**: Orchestrator lifecycle + time travel cleanup
7. **Test time travel**: Verify step lists no longer merge across timelines
