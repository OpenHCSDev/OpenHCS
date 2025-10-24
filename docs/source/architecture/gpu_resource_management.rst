GPU Resource Management System
==============================

Overview
--------

OpenHCS implements a GPU resource management system that coordinates GPU
device allocation during pipeline compilation. The system provides GPU
detection, registry initialization, and compilation-time GPU assignment
to ensure consistent GPU usage across pipeline steps.

**Note**: This document describes the actual GPU management
implementation. Runtime load balancing and slot acquisition features are
planned for future development.

Architecture Components
-----------------------

GPU Registry Singleton
~~~~~~~~~~~~~~~~~~~~~~

The core of the system is a thread-safe global GPU registry:

.. code:: python

   # Global GPU registry structure (simplified - no runtime coordination)
   GPU_REGISTRY: Dict[int, Dict[str, int]] = {
       0: {"max_pipelines": 2},  # GPU 0 can handle 2 concurrent pipelines
       1: {"max_pipelines": 2},  # GPU 1 can handle 2 concurrent pipelines
       # ... more GPUs
   }

   # Thread safety
   _registry_lock = threading.Lock()
   _registry_initialized = False

   # Note: "active" count was removed - GPU assignment happens at compilation time,
   # not at runtime. No runtime coordination exists.

Registry Initialization
~~~~~~~~~~~~~~~~~~~~~~~

The registry is initialized once during application startup:

.. code:: python

   def setup_global_gpu_registry(global_config: Optional[GlobalPipelineConfig] = None) -> None:
       """Initialize GPU registry using global configuration."""

       config_to_use = global_config or get_default_global_config()
       initialize_gpu_registry(configured_num_workers=config_to_use.num_workers)

   def initialize_gpu_registry(configured_num_workers: int) -> None:
       """Initialize GPU registry based on available hardware."""

       global GPU_REGISTRY, _registry_initialized

       with _registry_lock:
           if _registry_initialized:
               raise RuntimeError("GPU registry already initialized")

           # 1. Detect available GPUs
           available_gpus = _detect_available_gpus()
           logger.info(f"Detected GPUs: {available_gpus}")

           if not available_gpus:
               logger.warning("No GPUs detected. GPU memory types will not be available.")
               _registry_initialized = True
               GPU_REGISTRY.clear()
               return

           # 2. Calculate max concurrent pipelines per GPU
           max_cpu_threads = os.cpu_count() or configured_num_workers
           pipelines_per_gpu = max(1, math.ceil(max_cpu_threads / len(available_gpus)))

           # 3. Initialize registry (simplified structure)
           GPU_REGISTRY.clear()
           for gpu_id in available_gpus:
               GPU_REGISTRY[gpu_id] = {"max_pipelines": pipelines_per_gpu}

           _registry_initialized = True
           logger.info(f"GPU registry initialized: {GPU_REGISTRY}")

GPU Detection
~~~~~~~~~~~~~

Multi-library GPU detection across supported frameworks:

.. code:: python

   def _detect_available_gpus() -> List[int]:
       """Detect available GPUs across all supported frameworks."""

       available_gpus = set()

       # Check CuPy GPUs
       try:
           cupy_gpu = check_cupy_gpu_available()
           if cupy_gpu is not None:
               available_gpus.add(cupy_gpu)
       except Exception as e:
           logger.debug("Cupy GPU detection failed: %s", e)

       # Check PyTorch GPUs
       try:
           torch_gpu = check_torch_gpu_available()
           if torch_gpu is not None:
               available_gpus.add(torch_gpu)
       except Exception as e:
           logger.debug("Torch GPU detection failed: %s", e)

       # Check TensorFlow GPUs
       try:
           tf_gpu = check_tf_gpu_available()
           if tf_gpu is not None:
               available_gpus.add(tf_gpu)
       except Exception as e:
           logger.debug("TensorFlow GPU detection failed: %s", e)

       # Check JAX GPUs using lazy detection
       # JAX is checked via lazy import to defer jax.devices() call until needed
       # This avoids thread explosion (54+ threads) during startup
       try:
           jax_gpu = check_jax_gpu_available()
           if jax_gpu is not None:
               available_gpus.add(jax_gpu)
       except Exception as e:
           logger.debug("JAX GPU detection failed: %s", e)

       return sorted(list(available_gpus))

   def check_torch_gpu_available() -> Optional[int]:
       """Check PyTorch GPU availability."""
       try:
           import torch
           if torch.cuda.is_available():
               return torch.cuda.current_device()
       except Exception:
           pass
       return None

   def check_cupy_gpu_available() -> Optional[int]:
       """Check CuPy GPU availability."""
       try:
           import cupy
           if cupy.cuda.is_available():
               return cupy.cuda.get_device_id()
       except Exception:
           pass
       return None

GPU Allocation Strategy
-----------------------

Compilation-Time Assignment
~~~~~~~~~~~~~~~~~~~~~~~~~~~

GPU devices are assigned during pipeline compilation, not execution:

.. code:: python

   class GPUMemoryTypeValidator:
       """Validates GPU memory types and assigns GPU devices."""

       @staticmethod
       def validate_step_plans(step_plans: Dict[int, Dict[str, Any]]) -> Dict[int, Dict[str, Any]]:
           """Validate GPU memory types in step plans and assign GPU IDs."""

           # 1. Check if any step requires GPU
           requires_gpu = False
           required_libraries = set()

           for step_index, step_plan in step_plans.items():
               input_memory_type = step_plan.get('input_memory_type')
               output_memory_type = step_plan.get('output_memory_type')

               if input_memory_type in VALID_GPU_MEMORY_TYPES:
                   requires_gpu = True
                   required_libraries.add(input_memory_type)

               if output_memory_type in VALID_GPU_MEMORY_TYPES:
                   requires_gpu = True
                   required_libraries.add(output_memory_type)

           # If no step requires GPU, return empty assignments
           if not requires_gpu:
               return {}

           # 2. Validate that required libraries are installed
           _validate_required_libraries(required_libraries)

           # 3. Get GPU registry status
           gpu_registry = get_gpu_registry_status()
           if not gpu_registry:
               raise ValueError(
                   "🔥 COMPILATION FAILED: No GPUs available in registry but pipeline contains GPU-decorated functions!"
               )

           # 4. Assign first available GPU (simplified assignment)
           # All steps in pipeline use same GPU for affinity
           gpu_id = list(gpu_registry.keys())[0]

           # 5. Assign GPU to all GPU-requiring steps
           gpu_assignments = {}
           for step_index, step_plan in step_plans.items():
               input_type = step_plan.get('input_memory_type')
               output_type = step_plan.get('output_memory_type')

               if (input_type in VALID_GPU_MEMORY_TYPES or
                   output_type in VALID_GPU_MEMORY_TYPES):

                   gpu_assignments[step_index] = {'gpu_id': gpu_id}
                   logger.debug(
                       "Step %s assigned gpu_id %s for memory types: %s/%s",
                       step_index, gpu_id, input_type, output_type
                   )

           return gpu_assignments

GPU Affinity Strategy
~~~~~~~~~~~~~~~~~~~~~

All steps in a pipeline use the same GPU for optimal performance:

.. code:: python

   # GPU affinity is automatically enforced during compilation
   # All GPU-requiring steps in a pipeline receive the same gpu_id
   # This ensures optimal memory locality and reduces GPU context switching

Registry Status Access
----------------------

GPU Registry Status
~~~~~~~~~~~~~~~~~~~

.. code:: python

   def get_gpu_registry_status() -> Dict[int, Dict[str, int]]:
       """Get the current status of the GPU registry.

       Thread-safe: Uses a lock to ensure consistent access to the global registry.

       Returns:
           Copy of the GPU registry

       Raises:
           RuntimeError: If the GPU registry is not initialized
       """
       with _registry_lock:
           if not _registry_initialized:
               raise RuntimeError(
                   "Clause 295 Violation: GPU registry not initialized. "
                   "Must call initialize_gpu_registry() first."
               )

           # Return a copy of the registry to prevent external modification
           return {gpu_id: info.copy() for gpu_id, info in GPU_REGISTRY.items()}

Memory Type Integration
-----------------------

GPU Memory Type Validation
~~~~~~~~~~~~~~~~~~~~~~~~~~

The system validates GPU memory types against available hardware:

.. code:: python

   # GPU memory types that require GPU devices
   VALID_GPU_MEMORY_TYPES = {"cupy", "torch", "tensorflow", "jax", "pyclesperanto"}

   # Validation is performed during compilation by GPUMemoryTypeValidator
   # Library-specific validation ensures GPU compatibility before execution

Current Implementation Status
-----------------------------

Implemented Features
~~~~~~~~~~~~~~~~~~~~

-  ✅ GPU registry initialization and detection
-  ✅ Compilation-time GPU assignment
-  ✅ GPU affinity enforcement (same GPU per pipeline)
-  ✅ Multi-library GPU detection (PyTorch, CuPy, TensorFlow, JAX)
-  ✅ Thread-safe registry access
-  ✅ Lazy JAX GPU detection (defers jax.devices() call to avoid thread explosion)

Future Enhancements
~~~~~~~~~~~~~~~~~~~

1. **Runtime GPU Slot Management**: Dynamic GPU slot acquisition/release
   during execution
2. **Load Balancing**: Intelligent GPU assignment based on current
   utilization
3. **GPU Memory Monitoring**: Real-time memory usage tracking and
   optimization
4. **Error Handling**: GPU failure detection and recovery mechanisms
5. **Multi-Node GPU Management**: Coordinate GPUs across multiple
   machines
6. **Performance Profiling**: Detailed GPU performance metrics and
   recommendations

See Also
--------

**Core Integration**:

- :doc:`memory_type_system` - GPU memory type decorators and validation
- :doc:`pipeline_compilation_system` - GPU assignment during compilation
- :doc:`concurrency_model` - Multi-processing with GPU coordination

**Practical Usage**:

- :doc:`../guides/memory_type_integration` - GPU memory type integration guide
- :doc:`../api/processing_backends` - GPU-accelerated processing functions
- :doc:`../api/orchestrator` - PipelineOrchestrator GPU configuration

**Advanced Topics**:

- :doc:`compilation_system_detailed` - GPU resource assignment details
- :doc:`function_pattern_system` - GPU function patterns and optimization
- :doc:`system_integration` - GPU integration with other OpenHCS systems
