# Feasibility Analysis: CellProfiler Pipeline Integration with OpenHCS

## Executive Summary

**Feasibility Rating: MODERATE-TO-HIGH (7/10)**

Integrating CellProfiler pipelines into OpenHCS is technically feasible but requires significant architectural work. The integration would provide substantial value by combining CellProfiler's 80+ validated image analysis modules with OpenHCS's GPU acceleration, distributed processing, and modern data handling.

## OpenHCS Architecture Analysis

### Core Strengths for Integration

1. **Extensible Function Registry System**
   - Automatic function discovery from multiple libraries (574+ functions)
   - Unified registry architecture (`LibraryRegistryBase`)
   - Support for external libraries (pyclesperanto, CuCIM, scikit-image)
   - Memory type abstraction (NumPy, CuPy, PyTorch, JAX, pyclesperanto)
   - **Key file**: `openhcs/processing/backends/lib_registry/unified_registry.py`

2. **Flexible Pipeline Architecture**
   - Pipeline = List[AbstractStep]
   - FunctionStep supports 4 execution patterns:
     - Single function
     - Sequential chain
     - Dictionary (channel/well-specific)
     - Grouped execution
   - **Key files**: 
     - `openhcs/core/pipeline/__init__.py`
     - `openhcs/core/steps/function_step.py`

3. **Processing Contracts**
   - PURE_3D: Native 3D processing
   - PURE_2D: 2D-only (processes slices)
   - FLEXIBLE: Adapts to input
   - VOLUMETRIC_TO_SLICE: 3D→2D reduction
   - **Enables**: Automatic handling of CellProfiler's 2D modules on 3D stacks

4. **Memory Management**
   - Automatic conversion between memory types
   - GPU memory cleanup and OOM recovery
   - Zero-copy conversions where possible
   - **Key files**:
     - `openhcs/core/memory/converters.py`
     - `openhcs/core/memory/decorators.py`

5. **Distributed Execution**
   - Multi-well, multi-site, multi-channel parallelization
   - Configurable variable components
   - Memory backend (overlay) + persistent backends (disk/zarr)
   - **Key file**: `openhcs/core/orchestrator/orchestrator.py`

## CellProfiler Architecture Analysis

### Key Characteristics

1. **Module-Based Architecture**
   - 80+ modules for image processing, segmentation, measurement
   - Each module is a Python class with settings and run() method
   - Modules operate on CellProfiler's internal image/object data structures

2. **Pipeline Format**
   - `.cppipe` files (human-readable text format)
   - Contains module sequence + all settings
   - Can be loaded/saved programmatically

3. **Data Model**
   - Workspace object containing:
     - ImageSet: Collection of images
     - ObjectSet: Segmented objects
     - Measurements: Extracted features
   - Modules read from and write to workspace

4. **Execution Model**
   - Sequential module execution
   - Each module processes one image set at a time
   - No native GPU acceleration (CPU-only)
   - No native distributed processing

5. **Python API Status**
   - CellProfiler 4.x is Python 3 based
   - No official stable Python API for programmatic use
   - Can import modules but requires understanding internal structures
   - Headless mode available via CLI

## Integration Approaches

### Approach 1: CellProfiler Module Wrapper (RECOMMENDED)

**Concept**: Create a CellProfiler registry that wraps individual CellProfiler modules as OpenHCS functions.

**Implementation**:
```python
# openhcs/processing/backends/lib_registry/cellprofiler_registry.py
class CellProfilerRegistry(LibraryRegistryBase):
    """Registry for CellProfiler modules."""
    
    def discover_functions(self) -> Dict[str, FunctionMetadata]:
        """Discover CellProfiler modules and wrap them."""
        import cellprofiler_core.modules as cpm
        
        functions = {}
        for module_name in cpm.get_module_names():
            module_class = cpm.get_module_class(module_name)
            
            # Create wrapper function
            wrapped_func = self._create_module_wrapper(module_class)
            
            # Determine contract (most CP modules are 2D)
            contract = ProcessingContract.PURE_2D
            
            metadata = FunctionMetadata(
                name=module_name,
                func=wrapped_func,
                contract=contract,
                registry=self,
                module=module_class.__module__,
                doc=module_class.__doc__ or "",
                tags=["cellprofiler"],
                original_name=module_name
            )
            functions[module_name] = metadata
        
        return functions
    
    def _create_module_wrapper(self, module_class):
        """Create OpenHCS-compatible wrapper for CellProfiler module."""
        @numpy  # CellProfiler uses NumPy arrays
        def wrapper(image_stack, **settings):
            # Convert OpenHCS image stack to CellProfiler workspace
            workspace = self._create_workspace(image_stack)
            
            # Instantiate and configure module
            module = module_class()
            for key, value in settings.items():
                module.set_setting(key, value)
            
            # Run module
            module.run(workspace)
            
            # Extract result from workspace
            result_image = self._extract_result(workspace)
            
            return result_image
        
        return wrapper
```

**Pros**:
- Granular access to individual CellProfiler modules
- Can mix CellProfiler modules with OpenHCS GPU functions
- Leverages OpenHCS's distributed processing
- Each module can be GPU-accelerated if equivalent exists

**Cons**:
- Requires understanding CellProfiler's workspace/settings API
- Need to handle CellProfiler's object/measurement data structures
- May lose some CellProfiler-specific optimizations
- Settings translation layer needed

**Effort**: Medium (2-3 weeks)

### Approach 2: Pipeline File Executor

**Concept**: Parse `.cppipe` files and execute entire CellProfiler pipelines as single OpenHCS steps.

**Implementation**:
```python
# openhcs/processing/backends/cellprofiler_executor.py
@numpy
def execute_cellprofiler_pipeline(image_stack, pipeline_path: str, **overrides):
    """Execute a CellProfiler pipeline on an image stack."""
    import cellprofiler_core.pipeline as cpp
    import cellprofiler_core.workspace as cpw
    
    # Load pipeline
    pipeline = cpp.Pipeline()
    pipeline.load(pipeline_path)
    
    # Apply setting overrides
    for module_name, settings in overrides.items():
        module = pipeline.module(module_name)
        for key, value in settings.items():
            module.set_setting(key, value)
    
    # Create workspace with image stack
    workspace = self._create_workspace_from_stack(image_stack)
    
    # Run pipeline
    pipeline.run(workspace)
    
    # Extract final result
    return self._extract_final_image(workspace)

# Usage in OpenHCS
step = FunctionStep(
    func=(execute_cellprofiler_pipeline, {
        'pipeline_path': '/path/to/analysis.cppipe',
        'overrides': {
            'IdentifyPrimaryObjects': {'diameter': 15}
        }
    }),
    name="CellProfiler Analysis"
)
```

**Pros**:
- Reuse existing CellProfiler pipelines directly
- No need to rewrite validated workflows
- Simpler integration (black box approach)

**Cons**:
- Less granular control
- Can't interleave CellProfiler with OpenHCS GPU functions
- Entire pipeline runs on CPU
- Harder to parallelize individual modules

**Effort**: Low-Medium (1-2 weeks)

### Approach 3: Hybrid - GPU-Accelerated CellProfiler Equivalents

**Concept**: Identify common CellProfiler modules and create GPU-accelerated OpenHCS equivalents.

**Implementation**:
```python
# Map CellProfiler modules to OpenHCS GPU functions
CELLPROFILER_GPU_EQUIVALENTS = {
    'GaussianFilter': cupy_processor.gaussian_filter,
    'MedianFilter': cupy_processor.median_filter,
    'Threshold': cupy_processor.threshold_otsu,
    'MorphologicalOperations': cupy_processor.binary_opening,
    # ... etc
}

def translate_cellprofiler_pipeline(cppipe_path: str) -> Pipeline:
    """Translate CellProfiler pipeline to OpenHCS GPU pipeline."""
    cp_pipeline = load_cellprofiler_pipeline(cppipe_path)
    
    openhcs_steps = []
    for cp_module in cp_pipeline.modules():
        if cp_module.name in CELLPROFILER_GPU_EQUIVALENTS:
            # Use GPU equivalent
            gpu_func = CELLPROFILER_GPU_EQUIVALENTS[cp_module.name]
            params = translate_settings(cp_module.settings)
            openhcs_steps.append(FunctionStep(func=(gpu_func, params)))
        else:
            # Fall back to wrapped CellProfiler module
            wrapped = wrap_cellprofiler_module(cp_module)
            openhcs_steps.append(FunctionStep(func=wrapped))
    
    return Pipeline(openhcs_steps)
```

**Pros**:
- Best performance (GPU acceleration where possible)
- Gradual migration path
- Maintains CellProfiler compatibility

**Cons**:
- Requires manual mapping of modules
- Not all CellProfiler modules have GPU equivalents
- Complex translation logic

**Effort**: High (4-6 weeks initial, ongoing maintenance)

## Technical Challenges

### 1. Data Structure Impedance Mismatch

**Challenge**: CellProfiler uses Workspace/ImageSet/ObjectSet, OpenHCS uses 3D NumPy/CuPy arrays.

**Solution**:
- Create adapter layer to convert between formats
- OpenHCS image stack → CellProfiler ImageSet
- CellProfiler ObjectSet → OpenHCS measurement arrays

### 2. 2D vs 3D Processing

**Challenge**: Most CellProfiler modules are 2D-only, OpenHCS is 3D-native.

**Solution**:
- Use OpenHCS's PURE_2D contract
- Automatically process each Z-slice independently
- Already implemented in OpenHCS registry system

### 3. Settings/Parameters

**Challenge**: CellProfiler modules use complex settings objects, OpenHCS uses simple kwargs.

**Solution**:
- Create settings translation layer
- Map CellProfiler setting names to OpenHCS parameter names
- Provide sensible defaults

### 4. Object Tracking

**Challenge**: CellProfiler tracks objects across modules, OpenHCS is stateless.

**Solution**:
- Extend OpenHCS to support stateful processing contexts
- Store object data in processing context
- Pass context between wrapped modules

### 5. Measurements/Features

**Challenge**: CellProfiler extracts measurements to tables, OpenHCS focuses on image outputs.

**Solution**:
- Extend OpenHCS to support non-image outputs
- Already partially supported via special_outputs
- Store measurements in VFS alongside images

## Recommended Implementation Plan

### Phase 1: Proof of Concept (2 weeks)

1. Create basic CellProfilerRegistry
2. Wrap 3-5 simple modules (GaussianFilter, MedianFilter, Threshold)
3. Test on single image
4. Validate output matches CellProfiler

### Phase 2: Core Integration (3 weeks)

1. Implement workspace adapter layer
2. Handle object data structures
3. Support measurement extraction
4. Add 10-15 common modules

### Phase 3: Pipeline Support (2 weeks)

1. Implement .cppipe parser
2. Create pipeline translator
3. Support setting overrides
4. Test on real CellProfiler pipelines

### Phase 4: GPU Acceleration (4 weeks)

1. Map CellProfiler modules to GPU equivalents
2. Implement hybrid execution
3. Benchmark performance improvements
4. Document GPU-accelerated modules

### Phase 5: Production Readiness (2 weeks)

1. Comprehensive testing
2. Documentation
3. Example pipelines
4. UI integration

**Total Estimated Effort**: 13 weeks (3 months)

## Value Proposition

### For OpenHCS Users

1. **Access to 80+ Validated Modules**: Proven image analysis algorithms
2. **Reuse Existing Pipelines**: Import .cppipe files directly
3. **GPU Acceleration**: 10-100x speedup for compatible modules
4. **Distributed Processing**: Run CellProfiler at scale
5. **Modern Data Handling**: Zarr, cloud storage, streaming

### For CellProfiler Users

1. **GPU Acceleration**: Massive performance improvements
2. **3D Support**: Native 3D processing
3. **Distributed Execution**: Multi-well parallelization
4. **Modern UI**: PyQt6 + Textual interfaces
5. **Cloud Integration**: Process large datasets efficiently

## Risks and Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| CellProfiler API instability | High | Medium | Pin to specific CP version, maintain compatibility layer |
| Performance overhead from wrapping | Medium | High | Profile and optimize hot paths, use GPU equivalents |
| Complex module settings | Medium | High | Start with simple modules, build translation library |
| Object tracking complexity | High | Medium | Extend OpenHCS context system, thorough testing |
| Maintenance burden | Medium | Medium | Automated testing, clear documentation |

## Conclusion

**Recommendation**: PROCEED with Approach 1 (Module Wrapper) + Approach 3 (GPU Equivalents)

This hybrid approach provides:
- **Short-term value**: Quick access to CellProfiler modules
- **Long-term performance**: GPU acceleration where it matters
- **Flexibility**: Mix CellProfiler and OpenHCS functions
- **Compatibility**: Support existing .cppipe files

The integration aligns well with OpenHCS's architecture and would significantly expand its capabilities while maintaining the platform's performance advantages.

