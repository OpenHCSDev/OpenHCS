# 🧠 Napari Streaming System with Enhanced Configuration Architecture

## Summary

This PR implements a **comprehensive napari streaming system** with **dual-axis configuration resolution** and **enhanced UI inheritance patterns**, transforming OpenHCS from basic configuration management into a sophisticated scientific visual programming platform.

**Key Innovation**: Real-time visualization streaming with automatic process management, combined with recursive dual-axis configuration resolution that enables complex inheritance patterns while maintaining clean user APIs.

## 🎯 Core Architectural Advances

### **1. Napari Streaming System**
- **Real-Time Visualization**: Automatic napari viewer creation for pipeline steps with streaming configurations
- **Process-Based Architecture**: Eliminates Qt threading conflicts through dedicated napari processes
- **Configuration-Driven Detection**: Compiler automatically detects ``LazyNapariStreamingConfig`` instances during compilation
- **Persistent Viewers**: Napari windows survive pipeline restarts and maintain ZMQ connections

### **2. Dual-Axis Configuration Resolution**
- **X-Axis (Context Hierarchy)**: Step context → Orchestrator context → Global context → Static defaults
- **Y-Axis (Inheritance Chain)**: MRO-based inheritance traversal with field-specific blocking
- **Recursive Resolution**: Each context level fully exhausted before moving up hierarchy
- **Frame Injection Architecture**: Automatic context discovery through call stack introspection

### **3. Enhanced UI Inheritance System**
- **Cross-Window Consistency**: Pipeline Config ↔ Step Editor placeholder synchronization
- **Live Placeholder Updates**: Real-time updates when parent configurations change
- **User-Set Field Tracking**: Prevents placeholder updates from overwriting user values
- **Reset Behavior**: Proper placeholder restoration after field resets

## 🔧 Technical Implementation

### **Napari Streaming Architecture**

```python
# Pipeline steps declare streaming intent using LazyNapariStreamingConfig
Step(
    name="Image Enhancement Processing",
    func=enhance_images,
    step_materialization_config=LazyStepMaterializationConfig(),
    napari_streaming_config=LazyNapariStreamingConfig(well_filter=2)
)

# Compiler detects streaming configs during compilation
for attr_name in dir(resolved_step):
    config = getattr(resolved_step, attr_name, None)
    if isinstance(actual_config, StreamingConfig):
        has_streaming = True
        required_visualizers.append({
            'backend': actual_config.backend.name,
            'config': actual_config
        })
```

### **Dual-Axis Resolution Engine**

```python
# Recursive dual-axis resolution with frame injection
class RecursiveContextualResolver:
    def resolve_field(self, instance, field_name):
        # X-axis: Context discovery through frame injection
        contexts = self.discover_contexts(target_type=type(instance))

        # Y-axis: Inheritance chain traversal for each context
        for context in contexts:
            for cls in type(instance).__mro__:
                if value := self.get_concrete_value(context, cls, field_name):
                    return value
        return None
```

## 🚀 Critical Issues Resolved

### **Napari Streaming System**
- ✅ **Fixed**: Zombie process issue where napari GUI closes didn't terminate processes
- ✅ **Fixed**: Shared memory import errors preventing large array transfer
- ✅ **Fixed**: Process visibility issues with detached napari viewers
- ✅ **Enhanced**: ZMQ communication with proper handshake and persistence
- ✅ **Enhanced**: Automatic viewer lifecycle management through compiler detection

### **Configuration Resolution**
- ✅ **Fixed**: Cross-window placeholder consistency between Pipeline Config and Step Editor
- ✅ **Fixed**: Field-specific inheritance blocking (concrete overrides block per field, not per class)
- ✅ **Fixed**: Recursive resolution infinite loops causing TUI crashes
- ✅ **Fixed**: Thread-local context contamination during configuration editing
- ✅ **Enhanced**: Frame injection architecture for automatic context discovery

### **UI Inheritance System**
- ✅ **Fixed**: Reset operations showing concrete values instead of proper placeholders
- ✅ **Fixed**: Live placeholder updates when parent configurations change
- ✅ **Fixed**: User-set field tracking to prevent placeholder overwrites
- ✅ **Enhanced**: Cross-window synchronization for consistent inheritance display

---

## 📁 Files Changed

### **Core Resolution Engine**
- `openhcs/core/dual_axis_resolver_recursive.py` - Enhanced recursive dual-axis resolver
- `openhcs/core/composition_detection.py` - Composition-based relationship detection
- `openhcs/core/lazy_config.py` - Frame injection integration with lazy dataclasses
- `openhcs/core/lazy_placeholder.py` - Surgical concrete override detection

### **Napari Streaming System**
- `openhcs/io/napari_stream.py` - Streaming backend implementation
- `openhcs/runtime/napari_stream_visualizer.py` - Process management and Qt integration
- `openhcs/core/config.py` - NapariStreamingConfig and LazyNapariStreamingConfig
- `openhcs/core/pipeline/compiler.py` - Streaming config detection during compilation

### **UI Integration**
- `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py` - Unified inheritance logic
- `openhcs/pyqt_gui/widgets/step_parameter_editor.py` - Context event coordination
- `openhcs/pyqt_gui/windows/config_window.py` - Enhanced context providers

### **Testing Infrastructure**
- `tests/pyqt_gui/integration/test_reset_placeholder_simplified.py` - UI inheritance testing
- `tests/unit/test_composition_vs_inheritance_detection.py` - Configuration analysis
- Integration tests for napari viewer persistence validation

## 🔧 Technical Architecture

### **Dual-Axis Resolution System**

Implements the architecture documented in `docs/source/architecture/configuration_resolution.rst`:

**X-Axis (Context Hierarchy)**:
1. **Step context** - Most specific context (highest priority)
2. **Orchestrator context** - Intermediate context
3. **Global context** - Thread-local global config instance
4. **Static defaults** - Dataclass field defaults (lowest priority)

**Y-Axis (Inheritance Chain)**:
- For each context level, the system searches through the class inheritance hierarchy using Python's Method Resolution Order (MRO)

.. code-block:: python

   # Automatic context discovery and field resolution
   @global_pipeline_config
   @dataclass(frozen=True)
   class StepMaterializationConfig(StepWellFilterConfig, PathPlanningConfig):
       well_filter: Optional[int] = None  # Inherits from step context
       sub_dir: str = "checkpoints"       # Static override blocks inheritance

## 🧪 Testing Infrastructure

### **Enhanced Testing Architecture**

Following established OpenHCS testing conventions with comprehensive integration testing:

- **Cross-Window Consistency Testing**: Validates UI inheritance across forms using real PyQt6 widgets
- **Real Orchestrator Integration**: Tests with actual pipeline orchestrators rather than mocks
- **Placeholder Inheritance Validation**: Comprehensive inheritance behavior testing across configuration hierarchy
- **Configuration Resolution Testing**: Dual-axis resolver validation with thread-local context
- **Process Persistence Testing**: Napari viewer lifecycle validation with ZMQ communication

### **Testing Patterns**

- `tests/pyqt_gui/integration/test_reset_placeholder_simplified.py` - Mathematical simplification with 50%+ code reduction
- `tests/unit/test_composition_vs_inheritance_detection.py` - Composition vs inheritance equivalence validation
- Integration tests for napari viewer persistence and streaming validation
- Dynamic config lookups instead of hardcoded test values

## 🔄 Compatibility & Migration

### **Backward Compatibility** ✅
- **No breaking changes** to existing configuration patterns
- **All existing tests pass** for ImageXpress, Opera Phenix, disk and zarr backends
- **UI workflows preserved** - no changes to user interface patterns
- **API compatibility** - existing lazy dataclass usage continues to work

### **Migration Notes**
**No migration required** - all changes are backward compatible. The enhanced systems provide additional functionality without breaking current workflows.

## 🚀 Benefits for Scientific Programming

### **User Experience**
- **Clean APIs**: Scientists use simple `LazyNapariStreamingConfig()` patterns without complexity
- **Automatic Resolution**: Configuration values resolve based on execution context
- **Consistent Behavior**: Same configuration shows appropriate values in different UI contexts
- **Real-Time Monitoring**: Live visualization without performance impact on pipeline execution

### **Developer Experience**
- **Contained Complexity**: Frame injection isolated in specific service boundaries
- **Well-Tested**: Comprehensive test coverage with integration and unit tests
- **Documented Architecture**: Clear documentation of design decisions and trade-offs
- **Future Extensible**: Architecture supports evolution toward explicit service contracts

### **System Architecture**
- **Domain Appropriate**: Frame injection justified for scientific visual programming
- **Service Boundaries**: Clear separation between user APIs and infrastructure
- **Performance Conscious**: Safety mechanisms prevent frame injection overhead
- **Backward Compatible**: All existing workflows continue unchanged

---

**This PR transforms OpenHCS's configuration system from simple thread-local resolution into a sophisticated dual-axis resolution engine that maintains clean user APIs while providing powerful inheritance and real-time visualization capabilities for complex scientific workflows.**
