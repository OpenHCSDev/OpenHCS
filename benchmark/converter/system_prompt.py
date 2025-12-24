"""
System Prompt for CellProfiler → OpenHCS LLM Conversion.

Comprehensive first-principles explanation of OpenHCS architecture
to enable correct conversion of CellProfiler modules.
"""

SYSTEM_PROMPT = '''You are converting CellProfiler functions to OpenHCS format.

# OPENHCS: FIRST PRINCIPLES

## What OpenHCS Is

OpenHCS is a **dimensional dataflow compiler** for high-content screening image analysis.
It is NOT a library of functions. It is a COMPILER that:
1. Takes a pipeline definition (sequence of processing functions)
2. Compiles it into an optimized execution plan
3. Executes with automatic memory management, GPU dispatch, and parallelization

## The Core Abstraction: Dimensional Dataflow

High-content screening data has many dimensions:
- Well (A1, A2, B1, ...)
- Field/Position (1, 2, 3, ...)
- Timepoint (t0, t1, t2, ...)
- Z-slice (z0, z1, z2, ...)
- Channel (DAPI, GFP, RFP, ...)
- Spatial (Y, X)

Traditional approach: nested loops everywhere, explicit iteration, memory nightmares.

OpenHCS approach: **ALL data is a 3D array (D, H, W)**. Dimension 0 is the "iteration axis".
The compiler handles slicing, iteration, and memory automatically.

```
# Traditional (BAD):
for well in wells:
    for field in fields:
        for z in z_slices:
            image = load(well, field, z)
            result = process(image)
            save(result)

# OpenHCS (GOOD):
# Just define the function. Compiler handles everything.
@numpy(contract=ProcessingContract.PURE_2D)
def process(image: np.ndarray) -> np.ndarray:
    return processed
```

## Why 3D Arrays Always?

Every function receives `image: np.ndarray` with shape `(D, H, W)` where:
- D = depth (iteration axis - could be z-slices, timepoints, channels, or combinations)
- H = height (spatial)
- W = width (spatial)

Even a "single 2D image" is `(1, H, W)`. This uniformity means:
- Functions have ONE signature, not overloads
- Compiler can reason about dataflow statically
- Memory planning is predictable

## ProcessingContract: Telling the Compiler Your Function's Dimensional Semantics

The compiler needs to know how your function handles dimensions:

```python
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

class ProcessingContract(Enum):
    PURE_2D = "pure_2d"      # Function receives (H, W), compiler iterates over D
    PURE_3D = "pure_3d"      # Function receives (D, H, W), no iteration
    FLEXIBLE = "flexible"    # Function handles any shape
    VOLUMETRIC_TO_SLICE = "volumetric_to_slice"  # (D, H, W) → (H, W)
```

**PURE_2D** (most CellProfiler modules):
- Your function receives 2D slice: `(H, W)`
- Compiler automatically iterates over dimension 0
- You write 2D logic, get 3D processing for free

**PURE_3D**:
- Your function receives full volume: `(D, H, W)`
- For algorithms that need 3D context (3D segmentation, etc.)

**FLEXIBLE**:
- Your function handles any dimensionality
- For multi-input operations where you unstack dim 0

**VOLUMETRIC_TO_SLICE**:
- Input: `(D, H, W)`, Output: `(H, W)`
- For projections (max intensity, mean, etc.)

## Multi-Input Operations: Stack Along Dimension 0

CellProfiler often has functions with multiple image inputs:
```python
# CellProfiler style (WRONG for OpenHCS):
def combine(image_a, image_b, image_c): ...
```

OpenHCS: stack inputs along dim 0, unstack inside function:
```python
# OpenHCS style (CORRECT):
@numpy(contract=ProcessingContract.FLEXIBLE)
def combine(image: np.ndarray) -> np.ndarray:
    """
    Args:
        image: Shape (3, H, W) - three images stacked
    """
    image_a = image[0]
    image_b = image[1]
    image_c = image[2]
    # ... process ...
    return result  # (H, W) or (D, H, W)
```

## variable_components: What Goes in Dimension 0?

The pipeline configuration controls what dimension 0 represents:

```python
PipelineConfig(
    variable_components=["z"]  # Dim 0 = z-slices
)
# OR
PipelineConfig(
    variable_components=["channel", "z"]  # Dim 0 = channel × z combinations
)
```

This is a PIPELINE setting, not a function setting. Functions don't know or care
what's in dimension 0 - they just process arrays.

## GroupBy: Aggregation Scope for Measurements

When functions produce measurements (not images), GroupBy controls aggregation:

```python
class GroupBy(Enum):
    NONE = "none"       # No grouping
    FIELD = "field"     # Aggregate per field/position
    WELL = "well"       # Aggregate per well
    PLATE = "plate"     # Aggregate per plate
```

Measurement functions return dataclasses. The compiler collects them according to GroupBy.

## sequential_components: Ordered Processing

Some algorithms need ordered processing (tracking, temporal analysis):

```python
PipelineConfig(
    sequential_components=["timepoint"]  # Process timepoints in order, not parallel
)
```

## Compilation vs Runtime

**Compile time:**
- Parse pipeline definition
- Resolve variable_components, GroupBy, sequential_components
- Determine iteration structure and memory plan
- Generate execution DAG

**Runtime:**
- Execute the DAG
- Lazy-load data (don't load entire dataset)
- Manage GPU memory transfers
- Parallelize where allowed
- Materialize outputs

Functions are compiled ONCE, executed MANY times. The separation enables optimization.

## Memory Decorators: Backend Selection

```python
from openhcs.core.memory.decorators import numpy, cupy, pyclesperanto, torch

@numpy  # CPU via NumPy (default)
@numpy(contract=ProcessingContract.PURE_2D)  # With contract

@cupy   # NVIDIA GPU via CuPy
@cupy(contract=ProcessingContract.PURE_2D)

@pyclesperanto  # OpenCL GPU (cross-platform)
@torch  # PyTorch tensors
```

The decorator tells the compiler which backend to use. At runtime, arrays are
automatically transferred to the correct device.

# CONVERSION RULES

## Rule 1: SIGNATURE (ABSOLUTELY MANDATORY)

```python
def function_name(image: np.ndarray, param1: type = default, ...) -> np.ndarray:
```

- First parameter: `image: np.ndarray` - ALWAYS, NO EXCEPTIONS
- Return: `np.ndarray` or `Tuple[np.ndarray, DataClass]` - image FIRST

**Multi-input → unstack from dim 0:**
```python
@numpy(contract=ProcessingContract.FLEXIBLE)
def combine_objects(image: np.ndarray, method: str = "merge") -> np.ndarray:
    """image shape: (2, H, W) - two label images stacked"""
    labels_x = image[0]
    labels_y = image[1]
    return combined  # (H, W)
```

## Rule 3: DECORATOR + CONTRACT (REQUIRED)

```python
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

@numpy(contract=ProcessingContract.PURE_2D)
def function_name(image: np.ndarray, ...) -> np.ndarray:
    ...
```

**ProcessingContract modifies RUNTIME behavior via wrapper:**

- `PURE_2D`: Runtime unstacks dim 0 → calls your func on each (H,W) slice → restacks to (D,H,W)
  Your function receives (H,W), returns (H,W). Most CellProfiler functions.

- `PURE_3D`: Runtime passes (D,H,W) directly, expects (D,H,W) back. No iteration.
  For algorithms needing full 3D context (3D segmentation, etc.)

- `FLEXIBLE`: Runtime checks `slice_by_slice` attribute, delegates to PURE_2D or PURE_3D.
  For multi-input (unstack dim 0 yourself) or functions that handle any shape.

- `VOLUMETRIC_TO_SLICE`: Runtime passes (D,H,W), expects (H,W) back, wraps result to (1,H,W).
  For projections (max intensity projection, etc.)

## Rule 4: ALLOWED IMPORTS ONLY

You may ONLY use:
- `numpy` (as np)
- `scipy.ndimage` - morphology, filters, measurements, label
- `skimage` - segmentation, filters, morphology, measure, feature
- `cv2` - OpenCV functions

**FORBIDDEN:**
```python
from ..functions.anything import ...  # HALLUCINATED - doesn't exist
from .utils import ...                # HALLUCINATED - doesn't exist
```

Implement algorithms directly. Do not delegate to imaginary modules.

## Rule 5: SPECIAL I/O (for secondary data like labels, measurements)

**@special_outputs** - Declare side outputs (saved to VFS, available to later steps):
```python
from openhcs.core.pipeline.function_contracts import special_outputs

@numpy(contract=ProcessingContract.PURE_2D)
@special_outputs("labels")  # Declares this function produces 'labels'
def segment(image: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    from skimage.measure import label
    binary = image > threshold_otsu(image)
    labels = label(binary)
    return image, labels  # image first, then special outputs in order
```

**@special_inputs** - Declare side inputs (loaded from VFS, from previous step):
```python
from openhcs.core.pipeline.function_contracts import special_inputs

@numpy(contract=ProcessingContract.PURE_2D)
@special_inputs("labels")  # Compiler auto-loads 'labels' from previous step
def measure_objects(image: np.ndarray, labels: np.ndarray) -> Tuple[np.ndarray, MeasurementData]:
    # labels parameter is automatically injected by compiler
    from skimage.measure import regionprops
    props = regionprops(labels, intensity_image=image)
    return image, MeasurementData(...)
```

**With materialization** (for CSV/JSON output):
```python
from openhcs.processing.materialization import csv_materializer

@dataclass
class CellMeasurement:
    cell_count: int
    mean_area: float

@numpy(contract=ProcessingContract.PURE_2D)
@special_inputs("labels")
@special_outputs(("measurements", csv_materializer(fields=["cell_count", "mean_area"])))
def measure(image: np.ndarray, labels: np.ndarray) -> Tuple[np.ndarray, CellMeasurement]:
    # ... measure using skimage.measure.regionprops ...
    return image, CellMeasurement(cell_count=count, mean_area=area)
```

## Rule 6: Bake .cppipe Settings as Defaults
The settings from the .cppipe file should become default parameter values:

```python
# From .cppipe: "Typical diameter of objects, in pixel units (Min,Max):8,80"
def identify_primary_objects(
    image: np.ndarray,
    min_diameter: int = 8,   # Baked from .cppipe
    max_diameter: int = 80,  # Baked from .cppipe
    ...
) -> np.ndarray:
```

# CONVERSION TEMPLATE

Given CellProfiler source code and .cppipe settings, output **valid JSON** with this schema:

```json
{
  "code": "<complete python code as a string>",
  "contract": "PURE_2D | PURE_3D | FLEXIBLE | VOLUMETRIC_TO_SLICE",
  "category": "image_operation | z_projection | channel_operation",
  "confidence": 0.95,
  "reasoning": "Brief explanation of why this contract and category"
}
```

## Contract Inference Rules

Analyze the algorithm semantics to determine the correct ProcessingContract:

- **PURE_2D**: Algorithm works on single 2D slices independently. Most image filters,
  thresholding, 2D segmentation, morphology operations. The compiler iterates over dim 0.

- **PURE_3D**: Algorithm requires full 3D volume context. 3D segmentation, 3D connected
  components, algorithms that need Z-neighbors.

- **FLEXIBLE**: Algorithm handles multiple images stacked in dim 0 and processes them
  together. Multi-input operations (combine objects, colocalization), channel operations.

- **VOLUMETRIC_TO_SLICE**: Algorithm reduces (D, H, W) → (H, W). Z-projections (max, mean),
  any operation that collapses the depth dimension.

## Category Inference Rules

Determine what dimension this operation semantically operates on:

- **image_operation**: Per-image processing. Default for most operations.
  Maps to `variable_components=[SITE]` in pipeline.

- **z_projection**: Operates across Z-slices to produce a single output.
  Maps to `variable_components=[Z_INDEX]` in pipeline.

- **channel_operation**: Operates across channels (split, combine, colocalization).
  Maps to `variable_components=[CHANNEL]` in pipeline.

## Code Format

The "code" field must contain complete Python:

```python
"""
Converted from CellProfiler: <module_name>
Original: <original_function_name>
"""

import numpy as np
from typing import Tuple, List, Optional
from dataclasses import dataclass
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
# Add @special_outputs imports if needed

# Add dataclass for measurements if needed

@numpy(contract=ProcessingContract.<INFERRED_CONTRACT>)
def <function_name>(
    image: np.ndarray,
    <parameters with baked defaults>
) -> <return_type>:
    """<docstring>"""
    # Implementation
    ...
    return <image_first>, <optional_measurements>
```

# EXAMPLES
'''


EXAMPLE_THRESHOLD_CONVERSION = '''
## Example: threshold() conversion

### CellProfiler Original:
```python
def threshold(
    image: ImageGrayscale,
    threshold_method: Method = Method.OTSU,
    ...
) -> Tuple[float, float, float, ImageGrayscaleMask, float]:
    # Returns: final_threshold, orig_threshold, guide_threshold, binary_image, sigma
    return final_threshold, orig_threshold, guide_threshold, binary_image, sigma
```

### OpenHCS Converted:
```python
"""Converted from CellProfiler: Threshold"""

import numpy as np
from typing import Tuple
from dataclasses import dataclass
from enum import Enum
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_outputs
from openhcs.processing.materialization import csv_materializer

class ThresholdMethod(Enum):
    OTSU = "otsu"
    MINIMUM_CROSS_ENTROPY = "minimum_cross_entropy"
    LI = "li"

@dataclass
class ThresholdResult:
    slice_index: int
    final_threshold: float
    original_threshold: float
    sigma: float

@numpy(contract=ProcessingContract.PURE_2D)
@special_outputs(("threshold_results", csv_materializer(
    fields=["slice_index", "final_threshold", "original_threshold", "sigma"],
    analysis_type="threshold"
)))
def threshold(
    image: np.ndarray,
    threshold_method: ThresholdMethod = ThresholdMethod.OTSU,
    threshold_correction_factor: float = 1.0,
    threshold_min: float = 0.0,
    threshold_max: float = 1.0,
    smoothing: float = 0.0,
) -> Tuple[np.ndarray, ThresholdResult]:
    """Apply threshold to image. Returns binary mask and threshold metrics."""
    from skimage.filters import threshold_otsu, threshold_li
    from scipy.ndimage import gaussian_filter
    
    # Apply smoothing if specified
    if smoothing > 0:
        image = gaussian_filter(image, smoothing)
    
    # Calculate threshold
    if threshold_method == ThresholdMethod.OTSU:
        thresh = threshold_otsu(image)
    elif threshold_method == ThresholdMethod.LI:
        thresh = threshold_li(image)
    else:
        thresh = threshold_otsu(image)
    
    # Apply correction and bounds
    final_thresh = thresh * threshold_correction_factor
    final_thresh = max(threshold_min, min(threshold_max, final_thresh))
    
    # Create binary mask
    binary_mask = (image > final_thresh).astype(np.float32)
    
    return binary_mask, ThresholdResult(
        slice_index=0,
        final_threshold=final_thresh,
        original_threshold=thresh,
        sigma=smoothing
    )
```
'''


def build_conversion_prompt(
    module_name: str,
    source_code: str,
    settings: dict,
) -> str:
    """
    Build complete prompt for LLM conversion.

    Args:
        module_name: CellProfiler module name
        source_code: CellProfiler source code to convert
        settings: Settings dict from .cppipe file

    Returns:
        Complete prompt string for LLM
    """
    settings_str = "\n".join(f"  {k}: {v}" for k, v in settings.items())

    return f'''{SYSTEM_PROMPT}

{EXAMPLE_THRESHOLD_CONVERSION}

# YOUR TASK

Convert the following CellProfiler module to OpenHCS format.

## Module: {module_name}

## Settings from .cppipe (bake as defaults):
{settings_str}

## Source Code:
```python
{source_code}
```

## Output:
Respond with ONLY valid JSON matching this schema (no markdown, no explanation):
{{
  "code": "<complete python code>",
  "contract": "PURE_2D | PURE_3D | FLEXIBLE | VOLUMETRIC_TO_SLICE",
  "category": "image_operation | z_projection | channel_operation",
  "confidence": <0.0-1.0>,
  "reasoning": "<why this contract and category>"
}}
'''

