====================
DtypeConfig System
====================

*Module: openhcs.core.config*  
*Status: STABLE*

---

Overview
========

Traditional image processing pipelines hardcode dtype conversion assumptions for each backend. The DtypeConfig system eliminates these assumptions by providing a unified configuration that controls dtype conversion behavior across all memory backends (NumPy, CuPy, PyTorch, TensorFlow).

Quick Reference
===============

.. code-block:: python

    from openhcs.core.config import GlobalPipelineConfig, DtypeConfig, DtypeConversion
    
    # Set global default: preserve input dtype with scaling
    config = GlobalPipelineConfig(
        dtype_config=DtypeConfig(
            default_dtype_conversion=DtypeConversion.PRESERVE_INPUT
        )
    )
    
    # Override per-step: use native output dtype (no scaling)
    step = FunctionStep(
        function='my_gpu_function',
        dtype_config=DtypeConfig(
            default_dtype_conversion=DtypeConversion.NATIVE_OUTPUT
        )
    )

Configuration Hierarchy
=======================

DtypeConfig follows the standard OpenHCS configuration hierarchy:

**Priority Order** (highest to lowest):

1. **Step-level override**: ``FunctionStep(dtype_config=...)``
2. **Pipeline-level default**: ``PipelineConfig(dtype_config=...)``
3. **Global default**: ``GlobalPipelineConfig(dtype_config=...)``

This enables setting a global policy while allowing per-step exceptions for specific processing requirements.

Conversion Modes
================

NATIVE_OUTPUT (Default)
-----------------------

Backend functions return their natural output dtype without scaling.

.. code-block:: python

    # GPU function returns float32 [0.0, 1.0]
    # Output: float32 [0.0, 1.0] (no conversion)
    
    dtype_config = DtypeConfig(
        default_dtype_conversion=DtypeConversion.NATIVE_OUTPUT
    )

**When to use**: GPU processing pipelines where float32 is preferred, or when downstream steps expect normalized float values.

PRESERVE_INPUT
--------------

Backend functions scale output to match input dtype range.

.. code-block:: python

    # Input: uint16 [0, 65535]
    # GPU function returns: float32 [0.0, 1.0]
    # Output: uint16 [0, 65535] (scaled back)
    
    dtype_config = DtypeConfig(
        default_dtype_conversion=DtypeConversion.PRESERVE_INPUT
    )

**When to use**: Mixed CPU/GPU pipelines where dtype consistency is critical, or when saving results that must match input format.

Backend Integration
===================

DtypeConfig is automatically injected into every memory backend decorator:

.. code-block:: python

    from openhcs.core.memory.decorators import numpy_memory, cupy_memory
    
    @numpy_memory
    def process_numpy(image: np.ndarray, dtype_config: DtypeConfig = None) -> np.ndarray:
        # dtype_config automatically injected by decorator
        # Conversion applied based on dtype_config.default_dtype_conversion
        return processed_image
    
    @cupy_memory
    def process_cupy(image: cp.ndarray, dtype_config: DtypeConfig = None) -> cp.ndarray:
        # Same injection pattern for all backends
        return processed_image

The decorator system handles:

- **Automatic injection**: ``dtype_config`` parameter added to function signature
- **Context resolution**: Resolves from step → pipeline → global hierarchy
- **Conversion application**: Applies scaling based on configuration mode
- **Type preservation**: Maintains dtype semantics across backend boundaries

Scaling Semantics
=================

Range-Based Transformation
--------------------------

Scaling uses dtype-specific ranges to preserve data fidelity:

.. code-block:: python

    # uint8 → float32 conversion
    # Input range: [0, 255]
    # Output range: [0.0, 1.0]
    # Formula: float_value = uint8_value / 255.0
    
    # float32 → uint16 conversion
    # Input range: [0.0, 1.0]
    # Output range: [0, 65535]
    # Formula: uint16_value = float_value * 65535.0

**Supported dtypes**: uint8, uint16, uint32, int8, int16, int32, float16, float32, float64

Dtype-Preserving Percentile Normalization
------------------------------------------

Percentile normalization maintains dtype while rescaling intensity range:

.. code-block:: python

    from openhcs.processing.backends.processors.percentile_utils import (
        percentile_normalize_preserve_dtype
    )
    
    # Input: uint16 [100, 50000] (raw microscopy data)
    # Normalize to [2%, 98%] percentiles
    # Output: uint16 [0, 65535] (full dynamic range)
    
    normalized = percentile_normalize_preserve_dtype(
        image,
        lower_percentile=2.0,
        upper_percentile=98.0
    )

This enables contrast enhancement without dtype conversion overhead.

Common Patterns
===============

Global GPU Pipeline
-------------------

.. code-block:: python

    # All GPU steps use native float32 output
    config = GlobalPipelineConfig(
        dtype_config=DtypeConfig(
            default_dtype_conversion=DtypeConversion.NATIVE_OUTPUT
        )
    )

Mixed CPU/GPU Pipeline
----------------------

.. code-block:: python

    # Global: preserve dtype for consistency
    global_config = GlobalPipelineConfig(
        dtype_config=DtypeConfig(
            default_dtype_conversion=DtypeConversion.PRESERVE_INPUT
        )
    )
    
    # GPU step: override to use native float32
    gpu_step = FunctionStep(
        function='gpu_denoising',
        dtype_config=DtypeConfig(
            default_dtype_conversion=DtypeConversion.NATIVE_OUTPUT
        )
    )

Per-Step Override
-----------------

.. code-block:: python

    # Most steps preserve dtype
    pipeline_config = PipelineConfig(
        dtype_config=DtypeConfig(
            default_dtype_conversion=DtypeConversion.PRESERVE_INPUT
        )
    )
    
    # Final visualization step uses native float32
    viz_step = FunctionStep(
        function='create_overlay',
        dtype_config=DtypeConfig(
            default_dtype_conversion=DtypeConversion.NATIVE_OUTPUT
        )
    )

Implementation Notes
====================

**🔬 Source Code**: 

- Configuration: ``openhcs/core/config.py`` (line 289)
- Decorator injection: ``openhcs/core/memory/decorators.py`` (line 18)
- Scaling logic: ``openhcs/core/memory/dtype_scaling.py`` (line 15)
- Percentile utils: ``openhcs/processing/backends/processors/percentile_utils.py`` (line 121)

**🏗️ Architecture**: 

- :doc:`../architecture/memory-type-system` - Memory backend architecture
- :doc:`../architecture/configuration-management-system` - Configuration hierarchy

**📊 Performance**: 

- Zero-copy when input/output dtypes match
- Single scaling operation when conversion needed
- Framework-specific optimizations (CuPy uses GPU kernels)

Key Design Decisions
====================

**Why inject into every backend?**

Ensures consistent dtype behavior across all memory types without requiring backend-specific configuration.

**Why default to NATIVE_OUTPUT?**

GPU backends naturally produce float32, and forcing conversion adds overhead. Users opt-in to dtype preservation when needed.

**Why separate from ProcessingConfig?**

Dtype conversion is orthogonal to processing logic (grouping, variable components). Separate config enables independent evolution.

Common Gotchas
==============

- **Don't assume dtype preservation**: Default mode is NATIVE_OUTPUT, which may change dtype
- **Percentile normalization preserves dtype**: Use ``percentile_normalize_preserve_dtype`` when dtype consistency is critical
- **Step overrides are absolute**: Step-level ``dtype_config`` completely replaces pipeline/global config (no merging)
- **Scaling is range-based**: Float values outside [0.0, 1.0] will be clipped when converting to integer dtypes

