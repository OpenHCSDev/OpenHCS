# OMERO ZMQ Backend Selection Bug

## Summary
OMERO tests fail in ZMQ execution mode because checkpoint materialization attempts to create real directories using the disk backend instead of the OMERO backend, causing permission errors when trying to create directories under `/omero` (a virtual path).

## Error Message
```
RuntimeError: ZMQ execution failed: Error creating directory /omero/plate_403_outputs/checkpoints_step0: [Errno 13] Permission denied: '/omero'
```

## Root Cause
The `materialized_backend` in step plans is being set to `'disk'` instead of `'omero_local'` for OMERO plates when executing via ZMQ.

## Architecture Context

### OMERO Virtual Backend
- OMERO uses **virtual paths** like `/omero/plate_123/` that don't exist on the filesystem
- OMERO is a **virtual backend** - all paths are virtual, generated from OMERO plate structure
- **No real filesystem operations** - `ensure_directory()` is a no-op for OMERO backend
- OMERO output must be saved as **FileAnnotations** attached to OMERO objects, not as files
- OMERO plates MUST use `omero_local` backend for both input and output

### Backend Selection Flow
1. **Test Configuration** (`tests/integration/test_main.py:343-344`):
   ```python
   if test_config.is_omero:
       materialization_backend = MaterializationBackend('omero_local')
   ```
   Creates `GlobalPipelineConfig` with `VFSConfig(materialization_backend=MaterializationBackend.OMERO_LOCAL)`

2. **Path Planning Phase** (`openhcs/core/pipeline/path_planner.py:185`):
   ```python
   'materialized_backend': self.vfs.materialization_backend.value,
   ```
   Sets initial `materialized_backend` to `self.vfs.materialization_backend.value`

3. **Materialization Flag Planning Phase** (`openhcs/core/pipeline/materialization_flag_planner.py:83-85`):
   ```python
   if "materialized_output_dir" in step_plan:
       materialization_backend = MaterializationFlagPlanner._resolve_materialization_backend(context, vfs_config)
       step_plan["materialized_backend"] = materialization_backend
   ```
   Should overwrite `materialized_backend` with correct value from `vfs_config`

4. **Execution** (`openhcs/core/steps/function_step.py:997`):
   ```python
   filemanager.ensure_directory(materialized_output_dir, materialized_backend)
   ```
   Uses `materialized_backend` from step plan to create checkpoint directories

## ZMQ Configuration Transmission

### Client Side (`openhcs/runtime/zmq_execution_client.py:82`):
```python
request['config_code'] = generate_config_code(global_config, GlobalPipelineConfig, clean_mode=True)
```

### Server Side (`openhcs/runtime/zmq_execution_server.py:196-198`):
```python
is_empty = 'GlobalPipelineConfig(\n\n)' in config_code or 'GlobalPipelineConfig()' in config_code
global_config = GlobalPipelineConfig() if is_empty else (exec(config_code, ns := {}) or ns.get('config'))
```

### Config Serialization (`openhcs/debug/pickle_to_python.py:996-1028`):
```python
def generate_config_code(config, config_class, clean_mode=True):
    """
    Generate Python code representation of a config object.
    
    Args:
        config: Config instance (PipelineConfig, GlobalPipelineConfig, etc.)
        config_class: The class of the config
        clean_mode: If True, only show non-default values
    """
    config_repr = generate_clean_dataclass_repr(
        config,
        indent_level=0,
        clean_mode=clean_mode,
        required_imports=required_imports
    )
```

## Investigation Results

### Test 1: Config Serialization Works Correctly
```python
from openhcs.core.config import GlobalPipelineConfig, VFSConfig, MaterializationBackend
from openhcs.debug.pickle_to_python import generate_config_code

config = GlobalPipelineConfig(
    vfs_config=VFSConfig(materialization_backend=MaterializationBackend.OMERO_LOCAL)
)

code = generate_config_code(config, GlobalPipelineConfig, clean_mode=True)
print(code)
```

**Result**: Correctly generates:
```python
config = GlobalPipelineConfig(
    vfs_config=VFSConfig(
        materialization_backend=MaterializationBackend.OMERO_LOCAL
    )
)
```

### Test 2: Local OMERO Test Still Fails
```bash
pytest tests/integration/test_main.py --it-microscopes OMERO --it-zmq-mode zmq --it-visualizers none -v -s
```

**Result**: Both tests fail with same error:
- `test_main[disk-OMERO-3d-multiprocessing-zmq-none]` - FAILED
- `test_main[zarr-OMERO-3d-multiprocessing-zmq-none]` - FAILED

Error: `Error creating directory /omero/plate_403_outputs/checkpoints_step0: [Errno 13] Permission denied: '/omero'`

## Attempted Fix (Did Not Work)

### Change Made
Added `vfs_config=None` to `PipelineConfig` in ZMQ mode to inherit from global config:

```python
# tests/integration/test_main.py:591-597
pipeline_config = PipelineConfig(
    path_planning_config=LazyPathPlanningConfig(
        output_dir_suffix=CONSTANTS.OUTPUT_SUFFIX
    ),
    step_well_filter_config=LazyStepWellFilterConfig(well_filter=CONSTANTS.PIPELINE_STEP_WELL_FILTER_TEST),
    vfs_config=None,  # Inherit from global config
)
```

**Commit**: `8f01ee5` - "fix: Set vfs_config=None in ZMQ pipeline config to inherit OMERO backend from global config"

**Result**: Tests still fail with same error. This suggests the issue is NOT in the test configuration.

## Hypotheses to Investigate

### Hypothesis 1: Config Inheritance Not Working in ZMQ Server
The ZMQ server might be creating a new orchestrator that doesn't properly inherit the global config's `vfs_config`. Check:
- How does the server create the orchestrator from the deserialized config?
- Is the `vfs_config` from `GlobalPipelineConfig` being passed to the orchestrator's `pipeline_config`?
- Does the config context manager properly propagate `vfs_config` from global to pipeline config?

### Hypothesis 2: Clean Mode Dropping None Values
When `pipeline_config` has `vfs_config=None` and is serialized with `clean_mode=True`, the `None` value might be dropped, causing the server to use the default `VFSConfig()` with `materialization_backend=DISK`. Check:
- Does `generate_clean_dataclass_repr()` preserve `None` values in clean mode?
- What does the actual serialized `pipeline_config_code` look like?
- Add debug logging to print the generated config code before sending to server

### Hypothesis 3: Lazy Config Resolution Issue
The lazy config system might not be properly resolving `vfs_config=None` to inherit from the global config. Check:
- Does `LazyVFSConfig` exist and is it being used?
- How does the config context manager handle `None` values in lazy configs?
- Is there a difference between `vfs_config=None` and `vfs_config=LazyVFSConfig()`?

### Hypothesis 4: Server-Side Config Merging
The server might be merging the global config and pipeline config incorrectly. Check:
- How does `_execute_with_orchestrator()` merge the configs?
- Is the `vfs_config` from `pipeline_config` overriding the one from `global_config`?
- Does the orchestrator use the correct config hierarchy?

## Debugging Steps

1. **Add debug logging to print generated config code**:
   ```python
   # In zmq_execution_client.py:82
   config_code = generate_config_code(global_config, GlobalPipelineConfig, clean_mode=True)
   logger.info(f"Generated global config code:\n{config_code}")
   
   pipeline_config_code = generate_config_code(pipeline_config, PipelineConfig, clean_mode=True)
   logger.info(f"Generated pipeline config code:\n{pipeline_config_code}")
   ```

2. **Add debug logging on server side to print received config**:
   ```python
   # In zmq_execution_server.py:196
   logger.info(f"Received config code:\n{config_code}")
   logger.info(f"Received pipeline config code:\n{pipeline_config_code}")
   ```

3. **Add debug logging in MaterializationFlagPlanner**:
   ```python
   # In materialization_flag_planner.py:84
   logger.info(f"Step {i}: vfs_config.materialization_backend = {vfs_config.materialization_backend}")
   logger.info(f"Step {i}: resolved materialization_backend = {materialization_backend}")
   ```

4. **Check what vfs_config the orchestrator is using**:
   ```python
   # In orchestrator initialization
   logger.info(f"Orchestrator vfs_config: {self.pipeline_config.vfs_config}")
   logger.info(f"Orchestrator materialization_backend: {self.pipeline_config.vfs_config.materialization_backend}")
   ```

## Files Involved

- `tests/integration/test_main.py` - Test configuration
- `openhcs/core/config.py` - Config dataclasses and defaults
- `openhcs/core/pipeline/path_planner.py` - Sets initial `materialized_backend`
- `openhcs/core/pipeline/materialization_flag_planner.py` - Resolves final `materialized_backend`
- `openhcs/core/steps/function_step.py` - Uses `materialized_backend` for checkpoint creation
- `openhcs/runtime/zmq_execution_client.py` - Serializes and sends config
- `openhcs/runtime/zmq_execution_server.py` - Deserializes and uses config
- `openhcs/debug/pickle_to_python.py` - Config serialization logic
- `openhcs/io/disk.py` - Disk backend `ensure_directory()` (raises the error)
- `openhcs/io/omero_local.py` - OMERO backend `ensure_directory()` (no-op)

## Expected Behavior
For OMERO tests in ZMQ mode:
1. Test creates `GlobalPipelineConfig` with `VFSConfig(materialization_backend=MaterializationBackend.OMERO_LOCAL)`
2. Config is serialized and sent to ZMQ server
3. Server deserializes config and creates orchestrator
4. Orchestrator compiles pipeline with correct `materialized_backend='omero_local'` in step plans
5. Checkpoint materialization calls `filemanager.ensure_directory(dir, 'omero_local')`
6. OMERO backend's no-op `ensure_directory()` is called (no error)

## Actual Behavior
Steps 1-3 appear to work correctly, but step 4 sets `materialized_backend='disk'` instead of `'omero_local'`, causing step 5 to call the disk backend's `ensure_directory()` which tries to create a real directory at `/omero/...` and fails with permission denied.

