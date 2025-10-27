# Plan: Fix Zarr Input Conversion to Use Proper Subdirectory Structure

## Problem Statement

Currently, when `materialization_backend=ZARR` is set, the system converts input plates to zarr format but saves them to a **separate plate folder** with `_zarr` suffix (e.g., `zstack_plate_zarr/`). This defeats the purpose because:

1. The zarr version is never automatically used on subsequent runs
2. The orchestrator is initialized with the original plate, not the zarr plate
3. Creates duplicate plate structures instead of subdirectories within the same plate

## Architectural Requirements

### Two Different Scenarios

**Scenario A: OpenHCS Output Plates (No Virtual Workspace)**
- Subdirectories like `images/`, `checkpoints_step0/` contain real files matching their paths
- Zarr can **share the same subdirectory** with disk files
- Both backends coexist: `"available_backends": {"disk": true, "zarr": true}`

**Scenario B: Non-OpenHCS Input Plates (With Virtual Workspace)**
- Subdirectories like `TimePoint_1/` use virtual workspace mapping
- Virtual paths don't match filesystem layout
- Zarr must use a **separate subdirectory** (e.g., `zarr/`)
- Cannot mix virtual workspace paths with zarr OME-ZARR hierarchy

### Detection Logic

Determine which scenario by checking if the input subdirectory has `virtual_workspace` in `available_backends`:
- If `virtual_workspace` present → Scenario B (separate zarr subdirectory)
- If `virtual_workspace` absent → Scenario A (shared subdirectory)

## Solution Design

### Metadata Structure After Conversion

**Scenario A (Shared Subdirectory):**
```json
{
  "subdirectories": {
    "images": {
      "microscope_handler_name": "imagexpress",
      "source_filename_parser_name": "ImageXpressFilenameParser",
      "grid_dimensions": [3, 3],
      "pixel_size": 1.0,
      "image_files": [
        "images/A01_s001_w1.tif",
        "images/A01_s001_w2.tif",
        ...
      ],
      "channels": {...},
      "wells": {...},
      "sites": {...},
      "z_indexes": {...},
      "timepoints": {...},
      "available_backends": {
        "disk": true,
        "zarr": true  // Both coexist
      },
      "main": true
    }
  }
}
```

**Scenario B (Separate Subdirectory):**
```json
{
  "subdirectories": {
    "TimePoint_1": {
      "microscope_handler_name": "imagexpress",
      "source_filename_parser_name": "ImageXpressFilenameParser",
      "grid_dimensions": [3, 3],
      "pixel_size": 1.0,
      "image_files": [
        "TimePoint_1/A01_s001_w1_z001_t001.tif",
        ...
      ],
      "channels": {...},
      "wells": {...},
      "available_backends": {
        "disk": true,
        "virtual_workspace": true
      },
      "workspace_mapping": {...},
      "main": false  // No longer main after conversion
    },
    "zarr": {
      "microscope_handler_name": "imagexpress",
      "source_filename_parser_name": "ImageXpressFilenameParser",
      "grid_dimensions": [3, 3],
      "pixel_size": 1.0,
      "image_files": [
        "zarr/A01_s001_w1_z001_t001.tif",  // Virtual filenames
        "zarr/A01_s001_w2_z001_t001.tif",
        ...
      ],
      "channels": {...},  // Same as TimePoint_1
      "wells": {...},     // Same as TimePoint_1
      "available_backends": {
        "zarr": true
      },
      "main": true  // Use this on subsequent runs
    }
  }
}
```

### How Zarr Backend Handles Virtual Filenames

The zarr backend already stores virtual filenames in `openhcs_output_paths` attributes and uses them for `list_files()`:

1. **Saving**: Stores virtual filenames in `field_array.attrs["openhcs_output_paths"]`
2. **Listing**: Returns these virtual filenames from `list_files()`
3. **Loading**: Uses `openhcs_filename_map` to map virtual filenames → 5D coordinates → zarr arrays

This means the `image_files` list for zarr subdirectory should contain the same virtual filenames that are stored in the zarr attributes.

## Implementation Plan

### 1. Fix Compiler Input Conversion Config (openhcs/core/pipeline/compiler.py)

**File**: `openhcs/core/pipeline/compiler.py`
**Lines**: 244-265

**Current code:**
```python
conversion_config = PathPlanningConfig(
    output_dir_suffix="_zarr",  # Creates separate plate
    global_output_folder=plate_path.parent,
    sub_dir=path_config.sub_dir
)
```

**New logic:**
```python
# Determine if input uses virtual workspace
metadata = context.microscope_handler.metadata_handler._load_metadata_dict(plate_path)
subdirs = metadata["subdirectories"]
original_subdir = path_config.sub_dir
uses_virtual_workspace = Backend.VIRTUAL_WORKSPACE.value in subdirs[original_subdir]["available_backends"]

zarr_subdir = "zarr" if uses_virtual_workspace else original_subdir

conversion_config = PathPlanningConfig(
    output_dir_suffix="",
    global_output_folder=plate_path,
    sub_dir=zarr_subdir
)

context.step_plans[0]["input_conversion_config"] = conversion_config
context.step_plans[0]["input_conversion_uses_virtual_workspace"] = uses_virtual_workspace
context.step_plans[0]["input_conversion_original_subdir"] = original_subdir
```

### 2. Update Metadata After Conversion (openhcs/core/steps/function_step.py)

**File**: `openhcs/core/steps/function_step.py`
**Lines**: After line 905 (after input conversion completes)

**Add metadata update logic:**
```python
# Update metadata after conversion
if "input_conversion_dir" in step_plan:
    conversion_dir = Path(step_plan["input_conversion_dir"])
    plate_root = conversion_dir.parent

    if step_plan["input_conversion_uses_virtual_workspace"]:
        _update_metadata_for_separate_zarr_conversion(
            context, plate_root,
            step_plan["input_conversion_original_subdir"],
            conversion_dir.name
        )
    else:
        _update_metadata_for_shared_zarr_conversion(
            context, plate_root,
            step_plan["input_conversion_original_subdir"]
        )
```

### 3. Add Metadata Update Helper Functions (openhcs/core/steps/function_step.py)

**File**: `openhcs/core/steps/function_step.py`
**Location**: After existing helper functions (around line 1300)

**Function 1: Separate zarr subdirectory (Scenario B)**
```python
def _update_metadata_for_separate_zarr_conversion(
    context: 'ProcessingContext',
    plate_root: Path,
    original_subdir: str,
    zarr_subdir: str
) -> None:
    """Update metadata: original main=false, zarr main=true."""
    from openhcs.io.metadata_writer import get_metadata_path
    import json

    metadata_path = get_metadata_path(plate_root)
    with open(metadata_path) as f:
        metadata = json.load(f)

    subdirs = metadata["subdirectories"]
    original_metadata = subdirs[original_subdir]

    # Create zarr subdirectory metadata
    zarr_metadata = original_metadata.copy()
    zarr_metadata["available_backends"] = {"zarr": True}
    zarr_metadata["main"] = True
    zarr_metadata.pop("workspace_mapping", None)

    # Update image_files to use zarr/ prefix
    zarr_metadata["image_files"] = [
        f"{zarr_subdir}/{Path(f).name}" for f in original_metadata["image_files"]
    ]

    # Update original subdirectory to main=false
    subdirs[original_subdir]["main"] = False
    subdirs[zarr_subdir] = zarr_metadata

    with open(metadata_path, 'w') as f:
        json.dump(metadata, f, indent=2)

    logger.info(f"Updated metadata: {original_subdir} main=false, {zarr_subdir} main=true")
```

**Function 2: Shared subdirectory (Scenario A)**
```python
def _update_metadata_for_shared_zarr_conversion(
    context: 'ProcessingContext',
    plate_root: Path,
    subdir: str
) -> None:
    """Add zarr to available_backends."""
    from openhcs.io.metadata_writer import get_metadata_path
    import json

    metadata_path = get_metadata_path(plate_root)
    with open(metadata_path) as f:
        metadata = json.load(f)

    metadata["subdirectories"][subdir]["available_backends"]["zarr"] = True

    with open(metadata_path, 'w') as f:
        json.dump(metadata, f, indent=2)

    logger.info(f"Updated metadata: {subdir} now has zarr backend")
```

### 4. Update Detection Logic on Subsequent Runs (openhcs/core/pipeline/compiler.py)

**File**: `openhcs/core/pipeline/compiler.py`
**Lines**: 249-252

**Current code:**
```python
# Check if input plate is already zarr format
available_backends = context.microscope_handler.get_available_backends(plate_path)
already_zarr = Backend.ZARR in available_backends
```

**Fix**: Check main subdirectory's backends (which will be zarr/ if conversion happened):
```python
# Check if main subdirectory has zarr backend
available_backends = context.microscope_handler.get_available_backends(plate_path)
already_zarr = Backend.ZARR in available_backends
```

**Note**: No change needed - existing code already works because `get_available_backends()` returns the main subdirectory's backends, and after conversion the main subdirectory will be `zarr/` (Scenario B) or will have zarr in its backends (Scenario A).

## Testing Plan

### Test Case 1: ImageXpress Input Plate (Virtual Workspace)
1. Run pipeline with `materialization_backend=ZARR` on ImageXpress plate
2. Verify zarr conversion creates `zarr/` subdirectory (not `zstack_plate_zarr/`)
3. Verify metadata has both `TimePoint_1/` (main=false) and `zarr/` (main=true)
4. Run pipeline again
5. Verify it uses `zarr/` subdirectory (no re-conversion)

### Test Case 2: OpenHCS Output Plate (No Virtual Workspace)
1. Run pipeline that outputs to disk
2. Run another pipeline with `materialization_backend=ZARR` on that output
3. Verify zarr files are added to `images/` subdirectory (not separate)
4. Verify metadata shows `"available_backends": {"disk": true, "zarr": true}`
5. Run pipeline again
6. Verify it uses zarr backend from `images/` subdirectory

## Files to Modify

1. **openhcs/core/pipeline/compiler.py** (lines 244-265)
   - Update input conversion config logic
   - Add virtual workspace detection
   - Pass metadata to step_plan

2. **openhcs/core/steps/function_step.py** (after line 905)
   - Add metadata update after conversion
   - Add two helper functions for metadata updates

## Edge Cases

1. **Multiple subdirectories**: Currently only handles single main subdirectory
2. **Partial conversion**: If conversion fails midway, metadata might be inconsistent
3. **Manual zarr deletion**: If user deletes zarr/ directory, metadata still shows it as main
4. **Mixed backends**: What if user manually adds zarr files to a virtual workspace subdirectory?

## Future Enhancements

1. Add validation to ensure metadata consistency
2. Add cleanup logic to remove zarr cache
3. Add progress tracking for conversion
4. Support converting multiple subdirectories at once

