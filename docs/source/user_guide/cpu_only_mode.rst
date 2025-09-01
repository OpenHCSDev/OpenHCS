CPU-Only Mode
=============

OpenHCS supports a CPU-only mode that filters function registration to only include NumPy-based functions, enabling CI testing and deployment in environments without GPU support.

## Overview

CPU-only mode is designed for:

- **Continuous Integration (CI)**: Running tests without GPU dependencies
- **Development environments**: Working on systems without CUDA/OpenCL support
- **Deployment flexibility**: Running OpenHCS on CPU-only servers
- **Testing and validation**: Ensuring pipeline logic works independent of GPU acceleration

## Enabling CPU-Only Mode

Set the ``OPENHCS_CPU_ONLY`` environment variable to enable CPU-only mode:

.. code-block:: bash

   # Enable CPU-only mode
   export OPENHCS_CPU_ONLY=1
   
   # Run OpenHCS (only NumPy functions will be registered)
   python your_script.py

.. code-block:: bash

   # Disable CPU-only mode (default)
   unset OPENHCS_CPU_ONLY
   # or
   export OPENHCS_CPU_ONLY=0

## How It Works

When ``OPENHCS_CPU_ONLY`` is enabled, the function registry filters available functions to only include those with NumPy memory types:

.. code-block:: python

   # In func_registry.py
   def _filter_functions_by_memory_type(memory_type: str) -> List[Callable]:
       """Filter functions by memory type, respecting CPU-only mode."""
       
       # CPU-only mode: only allow numpy functions
       if os.getenv('OPENHCS_CPU_ONLY', '0') == '1':
           if memory_type not in CPU_ONLY_MEMORY_TYPES:
               return []
       
       # Normal mode: all memory types allowed
       if memory_type not in VALID_MEMORY_TYPES:
           return []

**Memory Type Filtering**:

- **CPU_ONLY_MEMORY_TYPES**: ``{"numpy"}``
- **VALID_MEMORY_TYPES**: ``{"numpy", "cupy", "torch", "tensorflow", "jax", "pyclesperanto"}``

## Available Functions in CPU-Only Mode

In CPU-only mode, OpenHCS provides access to:

### **NumPy-based Functions**
- **Scikit-image functions**: All CPU implementations
- **SciPy ndimage functions**: Standard image processing operations
- **OpenHCS native functions**: Custom implementations with NumPy backend
- **Basic operations**: Filtering, morphology, measurements, transformations

### **Excluded in CPU-Only Mode**
- **Pyclesperanto functions**: GPU-accelerated OpenCL implementations
- **CuPy functions**: GPU-accelerated NumPy equivalents
- **PyTorch functions**: GPU tensor operations
- **TensorFlow/JAX functions**: ML framework GPU operations

## CI Integration

CPU-only mode is particularly useful for continuous integration workflows:

.. code-block:: yaml

   # .github/workflows/tests.yml
   name: Tests
   on: [push, pull_request]
   
   jobs:
     test:
       runs-on: ubuntu-latest
       steps:
         - uses: actions/checkout@v3
         - name: Set up Python
           uses: actions/setup-python@v3
           with:
             python-version: '3.9'
         - name: Install dependencies
           run: |
             pip install -e .
             pip install pytest
         - name: Run tests in CPU-only mode
           env:
             OPENHCS_CPU_ONLY: 1
           run: pytest tests/

## Performance Considerations

### **CPU vs GPU Performance**
- **CPU functions**: Slower but universally compatible
- **Algorithm equivalence**: Same results as GPU versions for most operations
- **Memory usage**: Lower GPU memory requirements
- **Scalability**: Limited by CPU cores vs GPU parallelism

### **Development Workflow**
1. **Develop with CPU-only**: Test pipeline logic without GPU dependencies
2. **Validate with GPU**: Ensure performance and memory efficiency
3. **Deploy flexibly**: Choose CPU or GPU based on target environment

## Environment Variable Reference

.. list-table:: CPU-Only Mode Environment Variables
   :header-rows: 1
   :widths: 30 20 50

   * - Variable
     - Default
     - Description
   * - ``OPENHCS_CPU_ONLY``
     - ``0``
     - Enable CPU-only mode (``1``) or full GPU mode (``0``)

## Troubleshooting

### **Common Issues**

**Missing Functions**:
If functions are missing in CPU-only mode, they may be GPU-only implementations. Check the function's memory type:

.. code-block:: python

   # Check function memory type
   print(f"Memory type: {func.input_memory_type}")
   
   # Find CPU alternatives
   from openhcs.processing.func_registry import get_functions_by_memory_type
   cpu_functions = get_functions_by_memory_type("numpy")

**Performance Differences**:
CPU implementations may be significantly slower than GPU versions. Consider:

- Using smaller test datasets in CPU-only mode
- Implementing CPU-specific optimizations for critical paths
- Profiling to identify bottlenecks

### **Validation**

Verify CPU-only mode is working:

.. code-block:: python

   import os
   from openhcs.processing.func_registry import FUNC_REGISTRY
   
   # Check if CPU-only mode is enabled
   cpu_only = os.getenv('OPENHCS_CPU_ONLY', '0') == '1'
   print(f"CPU-only mode: {cpu_only}")
   
   # Check available registries
   print(f"Available registries: {list(FUNC_REGISTRY.keys())}")
   
   # In CPU-only mode, should only see numpy-based registries
   if cpu_only:
       assert 'pyclesperanto' not in FUNC_REGISTRY
       assert 'cupy' not in FUNC_REGISTRY

## Best Practices

### **Development**
- **Test both modes**: Ensure pipelines work in both CPU-only and GPU modes
- **Use environment files**: Manage environment variables consistently
- **Document requirements**: Specify when GPU acceleration is required

### **Deployment**
- **Environment detection**: Automatically enable CPU-only mode when GPUs unavailable
- **Graceful degradation**: Provide CPU fallbacks for GPU-intensive operations
- **Performance monitoring**: Track execution times in different modes

CPU-only mode provides essential flexibility for OpenHCS deployment across diverse environments while maintaining full pipeline compatibility and functionality.
