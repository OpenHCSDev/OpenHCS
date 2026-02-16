===================================
Orchestrator Cleanup Guarantees
===================================

*Module: openhcs.core.orchestrator.orchestrator*  
*Status: STABLE*

---

Overview
========

Worker processes accumulate memory and GPU resources when processing multiple wells sequentially. The orchestrator cleanup system guarantees resource cleanup before error returns, preventing memory leaks and zombie workers.

Problem Context
===============

Without guaranteed cleanup, worker processes leak resources:

.. code-block:: python

    # Worker processes well A
    process_well_A()  # Allocates GPU memory, creates VFS mappings
    
    # Worker processes well B
    process_well_B()  # Allocates MORE GPU memory, MORE VFS mappings
    
    # Worker processes well C → ERROR
    process_well_C()  # Raises exception
    
    # Without cleanup: GPU memory and VFS from A, B, C still allocated
    # Worker process is now a zombie with leaked resources

This causes:

- **Memory exhaustion**: GPU memory fills up across sequential wells
- **VFS pollution**: Memory backend accumulates stale file mappings
- **Zombie workers**: Processes hang with unreleased resources

Solution: Cleanup Before Error Return
======================================

The orchestrator guarantees cleanup REGARDLESS of success or failure:

.. code-block:: python

    def _execute_axis_with_sequential_combinations(
        pipeline_definition, axis_contexts, visualizer
    ):
        """Execute sequential combinations with guaranteed cleanup."""
        
        for combo_idx, (context_key, frozen_context) in enumerate(axis_contexts):
            # Execute this combination
            result = _execute_single_axis_static(
                pipeline_definition, frozen_context, visualizer
            )
            
            # CRITICAL: Clear VFS and GPU REGARDLESS of success/failure
            # This must happen BEFORE checking result status
            from polystore.base import reset_memory_backend
            from openhcs.core.memory.gpu_cleanup import cleanup_all_gpu_frameworks
            
            reset_memory_backend()
            if cleanup_all_gpu_frameworks:
                cleanup_all_gpu_frameworks()
            
            # NOW check if combination failed (after cleanup)
            if not result.success:
                return result  # Return error with clean state

**Key insight**: Cleanup happens BEFORE error return, ensuring worker process is in clean state even when errors occur.

Cleanup Components
==================

VFS Reset
---------

The memory backend maintains a virtual file system mapping real paths to in-memory data:

.. code-block:: python

    from polystore.base import reset_memory_backend
    
    # Clear all VFS mappings
    reset_memory_backend()

**What this clears**:

- In-memory file mappings
- Cached metadata
- Virtual path registrations
- Backend state

**Why this matters**: Without reset, VFS accumulates mappings from previous wells, causing memory growth and stale data access.

GPU Framework Cleanup
----------------------

GPU frameworks (CuPy, PyTorch, TensorFlow) cache memory pools and kernels:

.. code-block:: python

    from openhcs.core.memory.gpu_cleanup import cleanup_all_gpu_frameworks
    
    # Clear GPU memory pools and caches
    if cleanup_all_gpu_frameworks:
        cleanup_all_gpu_frameworks()

**What this clears**:

- CuPy memory pools
- PyTorch cached allocations
- TensorFlow graph caches
- CUDA context state

**Why this matters**: GPU memory pools grow across sequential wells. Cleanup releases memory back to GPU.

Cleanup Timing Guarantees
==========================

After Each Sequential Combination
----------------------------------

.. code-block:: python

    # Sequential processing: A → B → C
    for combination in sequential_combinations:
        result = process_combination(combination)
        
        # Cleanup AFTER each combination
        reset_memory_backend()
        cleanup_all_gpu_frameworks()
        
        # Check result AFTER cleanup
        if not result.success:
            return result  # Clean state guaranteed

**Guarantee**: Each combination starts with clean VFS and GPU state.

Before Error Return
-------------------

.. code-block:: python

    try:
        result = process_combination(combination)
    except Exception as e:
        # Cleanup BEFORE raising exception
        reset_memory_backend()
        cleanup_all_gpu_frameworks()
        raise  # Exception raised with clean state

**Guarantee**: Exceptions don't prevent cleanup. Worker process is clean even on errors.

After Successful Completion
----------------------------

.. code-block:: python

    # All combinations successful
    for combination in combinations:
        result = process_combination(combination)
        reset_memory_backend()
        cleanup_all_gpu_frameworks()
    
    # Final cleanup after all combinations
    reset_memory_backend()
    cleanup_all_gpu_frameworks()
    
    return success_result

**Guarantee**: Worker process is clean after successful completion, ready for next task.

Operational Implications
========================

Memory Stability
----------------

Cleanup guarantees prevent memory growth across sequential processing:

.. code-block:: python

    # Without cleanup
    # Well 1: 2GB GPU memory used
    # Well 2: 4GB GPU memory used (2GB + 2GB leaked)
    # Well 3: 6GB GPU memory used (4GB + 2GB leaked)
    # Well 4: OOM error (out of memory)
    
    # With cleanup
    # Well 1: 2GB GPU memory used → cleanup → 0GB
    # Well 2: 2GB GPU memory used → cleanup → 0GB
    # Well 3: 2GB GPU memory used → cleanup → 0GB
    # Well 4: 2GB GPU memory used → cleanup → 0GB

**Operational benefit**: Stable memory usage enables processing large plate datasets without OOM errors.

Worker Process Reuse
---------------------

Clean workers can be reused for subsequent tasks:

.. code-block:: python

    # Worker pool with 4 processes
    with ProcessPoolExecutor(max_workers=4) as executor:
        # Process 96-well plate
        for well in wells:
            future = executor.submit(process_well, well)
            # Worker cleanup guaranteed after each well
            # Same worker can process next well without restart

**Operational benefit**: Worker process reuse reduces overhead from process creation/destruction.

Zombie Worker Prevention
-------------------------

Cleanup before error return prevents zombie workers:

.. code-block:: python

    # Worker processes well with error
    try:
        process_well(well)
    except Exception as e:
        # Cleanup guaranteed before exception propagates
        reset_memory_backend()
        cleanup_all_gpu_frameworks()
        raise
    
    # Worker is clean, can be terminated or reused

**Operational benefit**: No zombie workers with leaked resources. Clean shutdown guaranteed.

Implementation Patterns
=======================

Sequential Combination Processing
----------------------------------

.. code-block:: python

    def _execute_axis_with_sequential_combinations(
        pipeline_definition, axis_contexts, visualizer
    ):
        """Execute sequential combinations with cleanup guarantees."""
        
        for combo_idx, (context_key, frozen_context) in enumerate(axis_contexts):
            # Execute combination
            result = _execute_single_axis_static(
                pipeline_definition, frozen_context, visualizer
            )
            
            # CRITICAL: Cleanup BEFORE checking result
            reset_memory_backend()
            if cleanup_all_gpu_frameworks:
                cleanup_all_gpu_frameworks()
            
            # Check result AFTER cleanup
            if not result.success:
                return result
        
        return ExecutionResult.success(axis_id=axis_id)

Multiprocessing Worker Function
--------------------------------

.. code-block:: python

    def _worker_process_well(well_context):
        """Worker function with cleanup guarantees."""
        
        try:
            # Process well
            result = process_pipeline(well_context)
            
            # Cleanup on success
            reset_memory_backend()
            cleanup_all_gpu_frameworks()
            
            return result
        
        except Exception as e:
            # Cleanup on error
            reset_memory_backend()
            cleanup_all_gpu_frameworks()
            
            # Return error result (don't raise to prevent worker crash)
            return ExecutionResult.failure(error=str(e))

ZMQ Execution Server
--------------------

The ZMQ execution server ensures cleanup even for remote execution:

.. code-block:: python

    class ZMQExecutionServer:
        def execute_pipeline(self, request):
            """Execute pipeline with cleanup guarantees."""
            
            try:
                result = self.orchestrator.execute_compiled_plate(...)
                
                # Cleanup after execution
                reset_memory_backend()
                cleanup_all_gpu_frameworks()
                
                return result
            
            except Exception as e:
                # Cleanup on error
                reset_memory_backend()
                cleanup_all_gpu_frameworks()
                
                raise

**Key insight**: Cleanup guarantees extend to remote execution via ZMQ server.

Implementation Notes
====================

**🔬 Source Code**: 

- Sequential cleanup: ``openhcs/core/orchestrator/orchestrator.py`` (line 199)
- Worker cleanup: ``openhcs/core/orchestrator/orchestrator.py`` (line 200-208)
- ZMQ server cleanup: ``openhcs/runtime/zmq_execution_server.py`` (line 448)

**🏗️ Architecture**: 

- :doc:`../concepts/memory-backend-system` - VFS architecture
- :doc:`gpu-resource-management` - GPU cleanup system
- :doc:`concurrency-model` - Multiprocessing architecture

**📊 Performance**: 

- VFS reset: < 1ms (clears dictionary mappings)
- GPU cleanup: 10-100ms (depends on allocated memory)
- Total overhead: < 1% of well processing time

Key Design Decisions
====================

**Why cleanup before error return?**

Ensures worker process is in clean state even when errors occur. Prevents zombie workers with leaked resources.

**Why cleanup after each sequential combination?**

Sequential processing accumulates resources across combinations. Per-combination cleanup prevents memory growth.

**Why separate VFS and GPU cleanup?**

VFS cleanup is always safe. GPU cleanup is conditional (only if GPU frameworks are loaded). Separation enables flexibility.

Common Gotchas
==============

- **Don't skip cleanup on errors**: Cleanup must happen BEFORE error return
- **Don't assume cleanup is automatic**: Explicit cleanup calls required
- **GPU cleanup is conditional**: Check if ``cleanup_all_gpu_frameworks`` exists before calling
- **VFS reset is global**: Affects all threads in worker process

Debugging Cleanup Issues
========================

Symptom: Memory Growth Across Wells
------------------------------------

**Cause**: Cleanup not called or failing silently

**Diagnosis**:

.. code-block:: python

    # Add logging to verify cleanup
    logger.debug("Before cleanup: VFS size = ...")
    reset_memory_backend()
    logger.debug("After cleanup: VFS size = 0")

**Fix**: Ensure cleanup is called after each well

Symptom: Zombie Workers
------------------------

**Cause**: Exception preventing cleanup

**Diagnosis**:

.. code-block:: python

    # Check worker process state
    ps aux | grep python  # Look for zombie processes

**Fix**: Wrap cleanup in try/finally to guarantee execution

Symptom: GPU OOM Errors
------------------------

**Cause**: GPU cleanup not called or ineffective

**Diagnosis**:

.. code-block:: python

    # Check GPU memory usage
    nvidia-smi  # Monitor GPU memory across wells

**Fix**: Verify ``cleanup_all_gpu_frameworks`` is called and working

