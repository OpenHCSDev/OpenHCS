#!/usr/bin/env python3

"""
Test how the compiler actually resolves step-level lazy configs during compilation.
"""

from openhcs.core.lazy_config import LazyStepWellFilterConfig, LazyStepMaterializationConfig, LazyNapariStreamingConfig, resolve_lazy_configurations_for_serialization
from openhcs.core.steps import FunctionStep as Step
from openhcs.processing.backends.processors.numpy_processor import create_composite

def test_compiler_resolution():
    """Test how the compiler resolves step configs during serialization."""
    print("🔍 TESTING COMPILER RESOLUTION")
    print("=" * 50)
    
    # Create a step with explicit well_filter in step_well_filter_config
    step = Step(
        name="Test Step",
        func=create_composite,
        step_well_filter_config=LazyStepWellFilterConfig(well_filter=1),  # Explicit value
        step_materialization_config=LazyStepMaterializationConfig(),      # Should inherit 1
        napari_streaming_config=LazyNapariStreamingConfig()               # Should inherit 1
    )
    
    print("BEFORE COMPILATION:")
    print(f"  step_well_filter_config.well_filter: {step.step_well_filter_config.well_filter}")
    print(f"  step_materialization_config.well_filter: {step.step_materialization_config.well_filter}")
    print(f"  napari_streaming_config.well_filter: {step.napari_streaming_config.well_filter}")
    print()
    
    # Simulate what the compiler does - resolve for serialization
    print("COMPILER RESOLUTION (resolve_lazy_configurations_for_serialization):")
    resolved_step = resolve_lazy_configurations_for_serialization(step)
    
    print(f"  step_well_filter_config.well_filter: {resolved_step.step_well_filter_config.well_filter}")
    print(f"  step_materialization_config.well_filter: {resolved_step.step_materialization_config.well_filter}")
    print(f"  napari_streaming_config.well_filter: {resolved_step.napari_streaming_config.well_filter}")
    print()
    
    # Check if they're the same
    expected = 1
    actual_mat = resolved_step.step_materialization_config.well_filter
    actual_napari = resolved_step.napari_streaming_config.well_filter
    
    print("COMPILER INHERITANCE ANALYSIS:")
    print(f"  step_materialization_config.well_filter should be {expected}, got {actual_mat}")
    print(f"  napari_streaming_config.well_filter should be {expected}, got {actual_napari}")
    print()
    
    if actual_mat == expected and actual_napari == expected:
        print("✅ SUCCESS: Compiler resolves step-level inheritance correctly!")
    else:
        print("❌ FAILURE: Compiler does NOT resolve step-level inheritance!")
        print("This means the compiler uses different resolution logic than step construction.")

def test_isolated_lazy_resolution():
    """Test what happens when we resolve lazy configs in isolation (no step context)."""
    print("\n🔍 TESTING ISOLATED LAZY RESOLUTION")
    print("=" * 50)
    
    # Create isolated lazy configs (no step context)
    isolated_mat = LazyStepMaterializationConfig()
    isolated_napari = LazyNapariStreamingConfig()
    
    print("ISOLATED LAZY CONFIGS (no step context):")
    print(f"  LazyStepMaterializationConfig().well_filter: {isolated_mat.well_filter}")
    print(f"  LazyNapariStreamingConfig().well_filter: {isolated_napari.well_filter}")
    print()
    
    # Resolve them for serialization
    resolved_mat = resolve_lazy_configurations_for_serialization(isolated_mat)
    resolved_napari = resolve_lazy_configurations_for_serialization(isolated_napari)
    
    print("AFTER SERIALIZATION RESOLUTION:")
    print(f"  resolved StepMaterializationConfig.well_filter: {resolved_mat.well_filter}")
    print(f"  resolved NapariStreamingConfig.well_filter: {resolved_napari.well_filter}")
    print()
    
    # These should show class defaults (1) since there's no step context
    if resolved_mat.well_filter == 1 and resolved_napari.well_filter == 1:
        print("✅ Isolated configs resolve to class defaults (1) as expected")
    else:
        print("❌ Isolated configs don't resolve to class defaults")

if __name__ == "__main__":
    test_compiler_resolution()
    test_isolated_lazy_resolution()
