# ObjectState Extraction Refactor

**Branch:** `object-state-extraction`  
**Commits:** 20 commits, +1539 net lines  
**Core Change:** Extract MODEL from ParameterFormManager into ObjectState for proper MVC separation

## Summary

This refactor separates MODEL (data/state) from VIEW (widgets/UI) in the OpenHCS GUI layer. Before this change, `ParameterFormManager` (PFM) was a 1209-line monolith that owned both data and widgets. After, PFM is 616 lines of pure VIEW logic, with all MODEL responsibilities moved to the new `ObjectState` class (753 lines).

---

## Architecture Comparison

### Before (main): Monolithic PFM

```mermaid
flowchart TB
    subgraph "main branch"
        direction TB
        
        PFM["ParameterFormManager<br/>(1209 lines)"]
        
        subgraph MODEL_IN_PFM["MODEL (embedded in PFM)"]
            params["self.parameters: Dict"]
            types["self.parameter_types: Dict"]
            defaults["self.param_defaults: Dict"]
            user_set["self._user_set_fields: Set"]
            reset["self.reset_fields: Set"]
        end
        
        subgraph VIEW_IN_PFM["VIEW (embedded in PFM)"]
            widgets["self.widgets: Dict"]
            nested["self.nested_managers: Dict"]
            signals["Qt Signals"]
        end
        
        PFM --> MODEL_IN_PFM
        PFM --> VIEW_IN_PFM
        
        style PFM stroke:#ff6b6b,stroke-width:3px
        style MODEL_IN_PFM stroke:#ffa94d,stroke-width:2px
        style VIEW_IN_PFM stroke:#69db7c,stroke-width:2px
    end
```

### After (object-state-extraction): Clean MVC

```mermaid
flowchart TB
    subgraph "object-state-extraction branch"
        direction TB
        
        OS["ObjectState<br/>(753 lines, NEW)"]
        PFM2["ParameterFormManager<br/>(616 lines, -49%)"]
        
        subgraph MODEL["MODEL (ObjectState)"]
            params2["parameters: Dict"]
            types2["parameter_types: Dict"]
            defaults2["param_defaults: Dict"]
            user_set2["_user_set_fields: Set"]
            reset2["reset_fields: Set"]
            nested_states["nested_states: Dict[str, ObjectState]"]
        end
        
        subgraph VIEW["VIEW (PFM)"]
            widgets2["widgets: Dict"]
            nested2["nested_managers: Dict"]
            signals2["Qt Signals"]
        end
        
        OS --> MODEL
        PFM2 --> VIEW
        PFM2 -.->|"self.state"| OS
        
        style OS stroke:#4dabf7,stroke-width:3px
        style PFM2 stroke:#69db7c,stroke-width:3px
        style MODEL stroke:#4dabf7,stroke-width:2px
        style VIEW stroke:#69db7c,stroke-width:2px
    end
```

---

## Lifecycle Comparison

### Before: PFM Lifecycle = Data Lifecycle

```mermaid
sequenceDiagram
    participant User
    participant StepEditor
    participant PFM as ParameterFormManager
    participant Step
    
    User->>StepEditor: Open step editor
    StepEditor->>PFM: Create(step)
    Note over PFM: Extract parameters<br/>Create widgets<br/>DATA LIVES HERE
    
    User->>PFM: Edit value
    PFM->>PFM: self.parameters[name] = value
    
    User->>StepEditor: Close editor
    StepEditor->>PFM: Destroy
    Note over PFM: ❌ DATA LOST<br/>unless manually synced
    
    User->>StepEditor: Reopen editor
    StepEditor->>PFM: Create(step) again
    Note over PFM: ❌ Re-extract from step<br/>May lose unsaved edits
```

### After: ObjectState Lifecycle Independent of UI

```mermaid
sequenceDiagram
    participant Pipeline as PipelineEditor
    participant Registry as ObjectStateRegistry
    participant OS as ObjectState
    participant PFM as ParameterFormManager
    participant User
    
    Pipeline->>OS: Create when step added
    Pipeline->>Registry: register(state)
    Note over OS: DATA CREATED<br/>Persists until step removed
    
    User->>Pipeline: Open step editor
    Pipeline->>Registry: get_by_scope(scope_id)
    Registry-->>Pipeline: ObjectState
    Pipeline->>PFM: Create(state=ObjectState)
    Note over PFM: VIEW attaches to MODEL
    
    User->>PFM: Edit value
    PFM->>OS: state.update_parameter(name, value)
    Note over OS: ✅ Single source of truth
    
    User->>Pipeline: Close editor
    Note over PFM: VIEW destroyed
    Note over OS: ✅ DATA PERSISTS
    
    User->>Pipeline: Reopen editor
    Pipeline->>Registry: get_by_scope(scope_id)
    Registry-->>Pipeline: SAME ObjectState
    Pipeline->>PFM: Create(state=ObjectState)
    Note over PFM: ✅ Attaches to existing state
```

---

## Data Flow Comparison

### Before: Direct Mutation

```mermaid
flowchart LR
    subgraph "main: Direct Dict Mutation"
        Widget1["Widget"]
        PFM1["PFM.parameters"]
        Service1["ParameterOpsService"]
        
        Widget1 -->|"on_change"| Service1
        Service1 -->|"manager.parameters[x] = y"| PFM1
        
        style PFM1 stroke:#ff6b6b,stroke-width:2px
    end
```

### After: ObjectState Methods

```mermaid
flowchart LR
    subgraph "object-state-extraction: Method Calls"
        Widget2["Widget"]
        PFM2["PFM (VIEW)"]
        OS2["ObjectState (MODEL)"]
        Service2["ParameterOpsService"]
        
        Widget2 -->|"on_change"| Service2
        Service2 -->|"manager.state.update_parameter()"| OS2
        PFM2 -.->|"@property delegation"| OS2
        
        style OS2 stroke:#4dabf7,stroke-width:2px
        style PFM2 stroke:#69db7c,stroke-width:2px
    end
```

---

## Class Responsibility Shift

```mermaid
flowchart TB
    subgraph Before["main: PFM Responsibilities"]
        direction LR
        B1["Extract params"]
        B2["Store state"]
        B3["Track modifications"]
        B4["Create widgets"]
        B5["Handle signals"]
        B6["Resolve placeholders"]
        B7["Live context"]
    end
    
    subgraph After["object-state-extraction: Split"]
        direction TB
        subgraph OS_Resp["ObjectState (MODEL)"]
            A1["Extract params"]
            A2["Store state"]
            A3["Track modifications"]
            A6["Resolve placeholders"]
        end
        subgraph PFM_Resp["PFM (VIEW)"]
            A4["Create widgets"]
            A5["Handle signals"]
        end
        subgraph LCS_Resp["LiveContextService"]
            A7["Live context collection"]
        end
    end
    
    style Before stroke:#ff6b6b,stroke-width:2px
    style OS_Resp stroke:#4dabf7,stroke-width:2px
    style PFM_Resp stroke:#69db7c,stroke-width:2px
    style LCS_Resp stroke:#be4bdb,stroke-width:2px
```

---

## Registry Architecture

```mermaid
flowchart TB
    subgraph Registry["ObjectStateRegistry (Singleton)"]
        direction LR
        states["_states: Dict[scope_id, ObjectState]"]
    end

    subgraph Scopes["Scope Hierarchy"]
        global["scope_id=None<br/>GlobalPipelineConfig"]
        plate["/path/to/plate<br/>PipelineConfig"]
        step0["/path/to/plate::step_0<br/>FunctionStep"]
        step1["/path/to/plate::step_1<br/>FunctionStep"]
    end

    Registry --> global
    Registry --> plate
    Registry --> step0
    Registry --> step1

    style Registry stroke:#4dabf7,stroke-width:3px
    style global stroke:#ffa94d,stroke-width:2px
    style plate stroke:#69db7c,stroke-width:2px
    style step0 stroke:#be4bdb,stroke-width:2px
    style step1 stroke:#be4bdb,stroke-width:2px
```

---

## Property Delegation Pattern

PFM delegates state access to ObjectState via `@property` decorators:

```mermaid
flowchart LR
    subgraph PFM_Props["PFM Properties (VIEW)"]
        p1["@property parameters"]
        p2["@property reset_fields"]
        p3["@property _user_set_fields"]
    end

    subgraph OS_Data["ObjectState Data (MODEL)"]
        d1["self.parameters"]
        d2["self.reset_fields"]
        d3["self._user_set_fields"]
    end

    p1 -->|"return self.state.parameters"| d1
    p2 -->|"return self.state.reset_fields"| d2
    p3 -->|"return self.state._user_set_fields"| d3

    style PFM_Props stroke:#69db7c,stroke-width:2px
    style OS_Data stroke:#4dabf7,stroke-width:2px
```

---

## Files Changed Summary

| File | Before | After | Change |
|------|--------|-------|--------|
| `object_state.py` | 0 | 753 | **NEW** |
| `parameter_form_manager.py` | 1209 | 616 | **-49%** |
| `parameter_ops_service.py` | 292 | 256 | -36 |
| `scope_token_service.py` | 0 | 178 | **NEW** |

### Key Deletions from PFM
- `from_dataclass_instance()` factory method
- `NoneAwareLineEdit`, `NoneAwareIntEdit` (→ widget_strategies.py)
- `create_widget()`, `_make_widget_readonly()` (→ WidgetService)
- `collect_live_context()`, `trigger_global_cross_window_refresh()` (→ LiveContextService)
- Direct state manipulation (`self.parameters[x] = y`)

### Key Additions to ObjectState
- `update_parameter(name, value)` - single mutation entry point
- `reset_parameter(name)` - handles tracking internally
- `get_current_values()` - collect all parameter values
- `get_user_modified_values()` - only user-set fields
- `update_thread_local_global_config()` - live updates for GlobalConfig
- `nested_states: Dict[str, ObjectState]` - recursive MODEL structure

---

## Conceptual Model

```mermaid
flowchart TB
    subgraph Ownership["Lifecycle Ownership"]
        direction TB

        PipelineEditor["PipelineEditor"]
        ConfigWindow["ConfigWindow"]
        ImageBrowser["ImageBrowser"]

        PipelineEditor -->|"owns steps"| StepStates["ObjectState per step"]
        ConfigWindow -->|"owns config"| ConfigState["ObjectState for config"]
        ImageBrowser -->|"owns viewer configs"| ViewerStates["ObjectState per viewer"]
    end

    subgraph Attachment["VIEW Attachment"]
        StepEditor["StepParameterEditor"]
        ConfigForm["ConfigWindow Form"]
        ViewerForm["ImageBrowser Forms"]

        StepEditor -.->|"attaches to"| StepStates
        ConfigForm -.->|"attaches to"| ConfigState
        ViewerForm -.->|"attaches to"| ViewerStates
    end

    style Ownership stroke:#4dabf7,stroke-width:2px
    style Attachment stroke:#69db7c,stroke-width:2px
```

---

## Benefits

1. **Data Persistence**: State survives UI close/reopen cycles
2. **Testability**: ObjectState is pure Python, no Qt dependencies
3. **Single Source of Truth**: All mutations through ObjectState methods
4. **Cleaner Code**: PFM reduced 49%, clear responsibility boundaries
5. **Registry Lookup**: `ObjectStateRegistry.get_by_scope(scope_id)` finds state anywhere
6. **Nested State**: `ObjectState.nested_states` mirrors dataclass structure

