# Input Conversion Backend Update Solutions

## Problem Statement

When input conversion happens (disk → zarr) during step 1 execution, subsequent steps that read from `PIPELINE_START` should use the zarr backend instead of the original disk backend.

## ✅ IMPLEMENTED SOLUTION

**Location:** `openhcs/core/pipeline/materialization_flag_planner.py` (lines 70-82)

**Approach:** Check during backend determination if input conversion will happen, and set zarr backend for PIPELINE_START steps (steps 1+).

### Implementation

```python
# In MaterializationFlagPlanner.assign_materialization_flags():
else:  # Other steps - read from memory (unless already set by chainbreaker logic)
    if READ_BACKEND not in step_plan:
        from openhcs.core.steps.abstract import InputSource
        if step.processing_config.input_source == InputSource.PIPELINE_START:
            # Check if input conversion will happen - if so, use zarr backend
            if "input_conversion_dir" in step_plans[0]:
                step_plan[READ_BACKEND] = Backend.ZARR.value
                # Also update input_dir to point to conversion target
                step_plan['input_dir'] = step_plans[0]["input_conversion_dir"]
                logger.debug(f"Step {i}: PIPELINE_START with conversion → zarr backend")
            else:
                # No conversion - use the same backend as the first step
                step_plan[READ_BACKEND] = step_plans[0][READ_BACKEND]
        else:
            step_plan[READ_BACKEND] = Backend.MEMORY.value
```

### Why This Works

1. ✅ **Compilation-time decision** - No runtime mutation of frozen contexts
2. ✅ **Proper architecture** - Backend determination happens in MaterializationFlagPlanner, which is designed for this
3. ✅ **Forward-looking** - Sets up steps to use zarr BEFORE it exists, knowing step 0 will create it
4. ✅ **Step 0 reads from disk** - Still uses original backend for conversion
5. ✅ **Steps 1+ read from zarr** - Automatically benefit from conversion
6. ✅ **Immutable contexts** - No mutations after compilation

### Execution Flow

```
COMPILE TIME (MaterializationFlagPlanner):
├── Step 0: read_backend="disk", input_dir="/plate/images" (will convert)
├── Step 1: Detects conversion flag → read_backend="zarr", input_dir="/plate/zarr"
└── Step 2: Detects conversion flag → read_backend="zarr", input_dir="/plate/zarr"

RUNTIME (Step 0):
├── Load from disk (/plate/images)
├── Convert to zarr
├── Save to /plate/zarr
└── Update metadata

RUNTIME (Step 1):
└── Load from zarr (/plate/zarr) ✅ Fast, efficient!

RUNTIME (Step 2):
└── Load from zarr (/plate/zarr) ✅ Fast, efficient!
```

### Alternative: Bulk Preload Still Loads from Disk

**Note:** Bulk preload (lines 1076+ in function_step.py) uses `read_backend`, so it will:
- Step 0: Load from disk (before conversion)
- Step 1+: Load from zarr (after conversion) ✅

---

## Other Solutions Explored (Not Implemented)

All other solutions are documented below for reference but were rejected in favor of the implemented solution above.

**Approach:** Check at runtime if zarr is available before each step executes.

### Implementation

```python
# In function_step.py, at start of process():
def process(self, context: 'ProcessingContext', step_index: int) -> None:
    step_plan = context.step_plans[step_index]
    
    # DYNAMIC BACKEND RESOLUTION for PIPELINE_START steps
    if step_index > 0:  # Skip first step (no conversion yet)
        from openhcs.core.steps.abstract import InputSource
        if hasattr(self, 'processing_config') and \
           self.processing_config.input_source == InputSource.PIPELINE_START:
            # Re-check available backends at runtime
            available_backends = context.microscope_handler.get_available_backends(context.plate_path)
            if Backend.ZARR in available_backends:
                logger.info(f"🔄 Step {step_index}: Detected zarr backend now available, updating from {step_plan['read_backend']}")
                step_plan['read_backend'] = Backend.ZARR.value
    
    # Continue with normal processing...
    read_backend = step_plan['read_backend']
```

### Pros
- ✅ Minimal changes to existing code
- ✅ Works even if conversion happens in parallel/distributed scenarios
- ✅ Self-correcting - adapts to actual plate state
- ✅ No changes to compilation phase

### Cons
- ❌ Modifies "frozen" step plans at runtime (violates immutability)
- ❌ Metadata file I/O on every step execution
- ❌ Won't work if steps run in parallel (race condition)
- ❌ Doesn't handle distributed execution (separate processes)

### Verdict
⚠️ **Pragmatic but hacky.** Works for single-process sequential execution but breaks architectural principles.

---

## Solution 2: Pre-Execution Conversion Phase

**Approach:** Move input conversion BEFORE any step execution, as a separate orchestrator phase.

### Implementation

```python
# In orchestrator.py execute_compiled_plate():
def execute_compiled_plate(self, pipeline_definition, compiled_contexts, ...):
    # NEW PHASE: Pre-execution input conversion
    if self._needs_input_conversion(compiled_contexts):
        logger.info("🔄 PRE-EXECUTION: Starting input conversion phase...")
        self._execute_input_conversion_phase(compiled_contexts)
        logger.info("🔄 PRE-EXECUTION: Input conversion complete, recompiling contexts...")
        
        # Recompile contexts to pick up zarr backend
        compiled_contexts = self._recompile_contexts_after_conversion(compiled_contexts)
    
    # EXISTING: Execute steps with updated contexts
    for axis_id, frozen_context in compiled_contexts.items():
        ...

def _execute_input_conversion_phase(self, compiled_contexts):
    """Execute input conversion for all wells before any step processing."""
    for axis_id, context in compiled_contexts.items():
        if "input_conversion_dir" in context.step_plans[0]:
            self._convert_input_for_well(context, axis_id)
```

### Pros
- ✅ Clean separation of concerns
- ✅ All steps see zarr from the start
- ✅ No runtime modifications to step plans
- ✅ Works with parallel step execution
- ✅ Conversion happens once per plate, not per well

### Cons
- ❌ Significant refactoring required
- ❌ Breaks current architecture (conversion was meant to be per-step)
- ❌ Recompilation overhead
- ❌ Complex error handling (what if conversion fails?)
- ❌ Doesn't work well with per-well parallel execution

### Verdict
✅ **Architecturally sound but expensive.** Best long-term solution but requires major changes.

---

## Solution 3: Update All Step Plans After First Step Completion

**Approach:** After step 1 completes conversion, update backend for all remaining steps.

### Implementation

```python
# In function_step.py, at end of process() after conversion:
if "input_conversion_dir" in step_plan:
    # ... existing conversion code ...
    
    # UPDATE REMAINING STEPS
    logger.info(f"🔄 INPUT CONVERSION: Updating read_backend for subsequent PIPELINE_START steps")
    from openhcs.core.steps.abstract import InputSource
    
    for i in range(step_index + 1, len(context.step_plans)):
        next_step_plan = context.step_plans[i]
        # Check if step reads from PIPELINE_START (would need step definition access)
        # For now, assume all subsequent steps that have same read_backend should update
        if next_step_plan.get('read_backend') == read_backend:
            next_step_plan['read_backend'] = Backend.ZARR.value
            logger.info(f"🔄 Updated step {i} read_backend: {read_backend} → zarr")
```

### Pros
- ✅ Localized change (only in function_step.py)
- ✅ Updates happen automatically after conversion
- ✅ Minimal overhead
- ✅ Works with sequential execution

### Cons
- ❌ Can't distinguish which steps read from PIPELINE_START vs previous step output
- ❌ Doesn't work with parallel well execution (each well has separate context)
- ❌ Modifies step plans after compilation
- ❌ Brittle (assumes backend equality means PIPELINE_START)

### Verdict
⚠️ **Quick fix but fragile.** Works for common cases but makes assumptions.

---

## Solution 4: Smart Backend Detection in Path Getter

**Approach:** Make `get_paths_for_axis` smart enough to check for zarr at runtime.

### Implementation

```python
# In function_step.py get_all_image_paths():
def get_all_image_paths(input_dir, backend, axis_id, filemanager, microscope_handler):
    """Get image paths, with automatic zarr fallback."""
    
    # Try requested backend first
    try:
        all_image_files = filemanager.list_image_files(str(input_dir), backend)
    except FileNotFoundError:
        # If disk fails and we're reading from PIPELINE_START, try zarr
        logger.debug(f"Backend {backend} not found, checking for zarr alternative...")
        
        # Check if zarr subdirectory exists
        zarr_dir = Path(input_dir).parent / "zarr"
        if backend == Backend.DISK.value and zarr_dir.exists():
            logger.info(f"🔄 AUTO-FALLBACK: Using zarr backend instead of disk for {input_dir}")
            all_image_files = filemanager.list_image_files(str(zarr_dir), Backend.ZARR.value)
        else:
            raise
    
    # ... rest of function
```

### Pros
- ✅ Transparent to rest of system
- ✅ Works automatically without manual intervention
- ✅ No changes to step plans
- ✅ Handles both converted and non-converted plates

### Cons
- ❌ Hidden behavior (magic fallback)
- ❌ Error messages become confusing
- ❌ Doesn't actually use zarr's benefits (just finds files)
- ❌ Path structure assumptions (zarr subdir)

### Verdict
❌ **Too magical.** Hides problems rather than solving them.

---

## Solution 5: Lazy Backend Resolution with Context Flag

**Approach:** Add a flag to context indicating conversion happened, check it at step start.

### Implementation

```python
# In function_step.py after conversion:
if "input_conversion_dir" in step_plan:
    # ... existing conversion code ...
    
    # Set flag in context
    context._input_converted_to_zarr = True
    context._zarr_input_dir = str(conversion_dir)

# At start of each step's process():
def process(self, context, step_index):
    step_plan = context.step_plans[step_index]
    
    # Check if conversion happened and adjust
    if step_index > 0 and getattr(context, '_input_converted_to_zarr', False):
        from openhcs.core.steps.abstract import InputSource
        if self.processing_config.input_source == InputSource.PIPELINE_START:
            # Use zarr backend and directory
            step_plan['read_backend'] = Backend.ZARR.value
            step_plan['input_dir'] = context._zarr_input_dir
            logger.info(f"🔄 Step {step_index}: Using converted zarr input")
```

### Pros
- ✅ Explicit flag makes behavior clear
- ✅ Works for sequential and parallel wells (context per well)
- ✅ Minimal changes
- ✅ Easy to debug

### Cons
- ❌ Adds mutable state to "frozen" context
- ❌ Doesn't persist across process boundaries
- ❌ Still modifies step plans at runtime

### Verdict
✅ **Balanced approach.** Good compromise between cleanliness and practicality.

---

## Solution 6: Conversion-Aware Path Planner

**Approach:** Make path planner check for post-conversion zarr during path resolution.

### Implementation

```python
# In path_planner.py:
def _resolve_step_input_dir(self, step_index, step):
    """Resolve input directory, checking for converted zarr."""
    
    if step_index == 0:
        return self.base_input_dir
    
    from openhcs.core.steps.abstract import InputSource
    if step.processing_config.input_source == InputSource.PIPELINE_START:
        # Check if zarr conversion happened or will happen
        if "input_conversion_dir" in self.plans[0]:
            conversion_dir = Path(self.plans[0]["input_conversion_dir"])
            # Use conversion target as input
            return str(conversion_dir)
        return self.base_input_dir
    
    # Previous step output
    return self.plans[step_index - 1]["output_dir"]
```

### Pros
- ✅ Paths are correct from the start
- ✅ No runtime modifications
- ✅ Clean separation - path planner handles paths
- ✅ Backend follows directory automatically

### Cons
- ❌ Assumes conversion will happen (might not if step 1 fails)
- ❌ Circular dependency (path planner needs conversion info)
- ❌ Doesn't update backend, only path

### Verdict
⚠️ **Half solution.** Fixes paths but not backends.

---

## Recommended Solution: Hybrid Approach (5 + 3)

Combine Solution 5's flag with Solution 3's batch update:

```python
# After conversion in step 1:
if "input_conversion_dir" in step_plan:
    # ... conversion code ...
    
    # 1. Set context flag
    context._input_converted_to_zarr = True
    context._zarr_conversion_dir = str(conversion_dir)
    
    # 2. Update all subsequent PIPELINE_START steps
    from openhcs.core.steps.abstract import InputSource
    for i in range(step_index + 1, len(context.step_plans)):
        next_plan = context.step_plans[i]
        # Only update if this step was supposed to read from PIPELINE_START
        # (identified by having same input_dir as step 0)
        if next_plan.get('input_dir') == context.step_plans[0]['input_dir']:
            next_plan['read_backend'] = Backend.ZARR.value
            next_plan['input_dir'] = str(conversion_dir)
            logger.info(f"🔄 Updated step {i} to use zarr: {conversion_dir}")
```

### Why This Works
- ✅ Explicit and debuggable (flag)
- ✅ Batch update is efficient
- ✅ Input_dir comparison is reliable way to identify PIPELINE_START steps
- ✅ Works within single-well context (parallel-safe per well)
- ✅ Minimal changes to existing architecture

### Limitations
- ⚠️ Still modifies "frozen" plans (but explicitly and safely)
- ⚠️ Each well converts independently (some duplication)

---

## Alternative: Recompilation-Based Solution (Most Correct)

For truly clean architecture, conversion should trigger recompilation:

```python
# In orchestrator execute_compiled_plate():
def execute_compiled_plate(self, pipeline_definition, compiled_contexts, ...):
    conversion_happened = False
    
    for axis_id, context in compiled_contexts.items():
        # Execute step 0
        pipeline_definition[0].process(context, 0)
        
        # Check if conversion happened
        if hasattr(context, '_input_converted_to_zarr'):
            conversion_happened = True
            break  # Only need one well to convert
    
    # Recompile if conversion happened
    if conversion_happened:
        logger.info("🔄 Input conversion detected, recompiling contexts...")
        # Re-run compilation to pick up zarr backend
        compiled_contexts = self.compile_plate_for_processing(
            pipeline_definition, 
            plate_path=self.plate_path,
            ...
        )
    
    # Execute remaining steps with updated contexts
    for axis_id, context in compiled_contexts.items():
        for step_index in range(1, len(pipeline_definition)):
            pipeline_definition[step_index].process(context, step_index)
```

This is **architecturally perfect** but complex to implement.
