# Dirty Tracking: Two Sources of Truth Analysis

## Summary

**PFM Labels are MORE accurate** - they use `is_field_dirty()` directly on every parameter change.  
**List Items can DESYNC** - they rely on threshold-crossing callbacks that can miss the initial dirty state.

---

## The Two Mechanisms

### 1. PFM Label Dirty Indicator (Accurate ✅)

```mermaid
flowchart TD
    A[User edits field] --> B[update_parameter]
    B --> C[on_parameters_changed callback fires]
    C --> D[_on_parameter_changed_for_label_styling]
    D --> E[_update_label_styling]
    E --> F["is_field_dirty(dotted_path)"]
    F --> G[Compare _live_resolved vs _saved_resolved]
    G --> H[set_dirty_indicator on label]
    
    style F fill:#90EE90
    style G fill:#90EE90
```

**Key Property**: Calls `is_field_dirty()` **synchronously on EVERY parameter change**.

### 2. List Item Dirty Marker (Can Desync ❌)

```mermaid
flowchart TD
    A[User edits field] --> B[update_parameter]
    B --> C[invalidate_by_type_and_scope]
    C --> D[_ensure_live_resolved]
    D --> E{was_dirty != is_dirty_now?}
    E -->|YES| F[on_dirty_changed callback fires]
    E -->|NO| G[NO callback - already dirty]
    F --> H[queue_visual_update]
    H --> I[update_item_list]
    I --> J[_format_list_item]
    J --> K[_get_dirty_marker]
    K --> L["is_dirty()"]
    
    G --> M[List item text NOT refreshed]
    
    style E fill:#FFB6C1
    style G fill:#FFB6C1
    style M fill:#FFB6C1
```

**Key Property**: Only triggers on **threshold crossings** (clean→dirty or dirty→clean).

---

## The Desync Scenario

```mermaid
sequenceDiagram
    participant OS as ObjectState
    participant PFM as PFM Labels
    participant LI as List Item
    
    Note over OS: ObjectState created<br/>_live_resolved computed<br/>_saved_resolved computed
    
    rect rgb(255, 200, 200)
        Note over OS,LI: DESYNC WINDOW
        OS->>OS: Field becomes dirty<br/>(live context differs from saved)
        OS->>PFM: on_parameters_changed
        PFM->>PFM: is_field_dirty() → TRUE
        PFM->>PFM: Shows asterisk ✅
        Note over LI: List item subscription<br/>NOT YET REGISTERED
    end
    
    Note over LI: Pipeline editor calls update_item_list()
    LI->>OS: Subscribe on_dirty_changed
    Note over LI: Subscription registered<br/>BUT threshold already crossed!
    
    rect rgb(200, 255, 200)
        Note over LI: Workaround: _format_list_item calls is_dirty()
        LI->>OS: is_dirty()
        OS->>LI: TRUE
        LI->>LI: Shows asterisk ✅ (polling wins)
    end
```

---

## When Does List Item Actually Update?

The list item dirty marker is updated via TWO mechanisms:

### Mechanism A: Callback (Reactive)
- `on_dirty_changed` fires → `queue_visual_update()` → `update_item_list()`
- **Problem**: Only fires on threshold crossings

### Mechanism B: Polling (During Redraw)
- `_format_list_item()` calls `_get_dirty_marker()` which calls `is_dirty()`
- **This is the safety net** - but only works when list is redrawn

---

## Root Cause of Desync

```mermaid
flowchart LR
    subgraph "When ObjectState becomes dirty"
        A[ObjectState created] --> B[_compute_resolved_snapshot]
        B --> C[_live_resolved differs from _saved_resolved]
        C --> D[ObjectState.is_dirty = TRUE]
    end
    
    subgraph "List Item Subscription"
        E[Pipeline editor opens/updates] --> F[update_item_list]
        F --> G[_subscribe_flash_for_item]
        G --> H[on_dirty_changed registered]
    end
    
    D -.->|"Threshold crossing<br/>ALREADY HAPPENED"| H
    
    style D fill:#FFB6C1
    style H fill:#FFB6C1
```

**The Problem**: If ObjectState becomes dirty BEFORE the list item subscribes, 
the `on_dirty_changed` callback was never invoked for that transition.

---

## Why PFM Labels Work

1. **Immediate subscription**: PFM subscribes to `on_parameters_changed` in `__init__`
2. **Per-field granularity**: Every parameter change triggers label update
3. **Direct query**: Always calls `is_field_dirty()` - never relies on cached state

## Why List Items Can Fail

1. **Delayed subscription**: List items subscribe when `update_item_list()` runs
2. **Threshold-based**: `on_dirty_changed` only fires on transitions
3. **Initial state missed**: If already dirty when subscribed, no callback fires

---

## The Fix Options

### Option 1: Immediate Dirty Check on Subscription
When subscribing to `on_dirty_changed`, immediately check current dirty state:

```python
def _subscribe_flash_for_item(self, item, list_item, scope_id):
    # ... existing subscription code ...
    
    # NEW: Check current dirty state and update immediately
    if state.is_dirty():
        self.queue_visual_update()  # Force redraw with dirty marker
```

### Option 2: Use on_parameters_changed Instead
Subscribe to `on_parameters_changed` which fires on EVERY change, not just transitions.

### Option 3: Rely on Polling Only
Remove `on_dirty_changed` subscription and rely on `_get_dirty_marker()` polling.
But this requires ensuring `update_item_list()` is called when needed.

