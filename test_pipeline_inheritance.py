#!/usr/bin/env python3

"""
Test pipeline step inheritance - should step configs inherit from each other?
"""

from openhcs.core.lazy_config import LazyStepWellFilterConfig, LazyStepMaterializationConfig, LazyNapariStreamingConfig
from openhcs.core.steps import FunctionStep as Step
from openhcs.processing.backends.processors.numpy_processor import create_composite

def test_step_inheritance():
    """Test if step configs inherit from each other within the same step."""
    print("🔍 TESTING STEP-LEVEL INHERITANCE")
    print("=" * 50)
    
    # Create a step with explicit well_filter in step_well_filter_config
    step = Step(
        name="Test Step",
        func=create_composite,
        step_well_filter_config=LazyStepWellFilterConfig(well_filter=1),  # Explicit value
        step_materialization_config=LazyStepMaterializationConfig(),      # Should inherit 1
        napari_streaming_config=LazyNapariStreamingConfig()               # Should inherit 1
    )
    
    print("Step configuration:")
    print(f"  step_well_filter_config.well_filter: {step.step_well_filter_config.well_filter}")
    print(f"  step_materialization_config.well_filter: {step.step_materialization_config.well_filter}")
    print(f"  napari_streaming_config.well_filter: {step.napari_streaming_config.well_filter}")
    print()
    
    # Expected: All should be 1 (inherited from step_well_filter_config)
    expected = 1
    actual_mat = step.step_materialization_config.well_filter
    actual_napari = step.napari_streaming_config.well_filter
    
    print("Expected inheritance:")
    print(f"  step_materialization_config.well_filter should be {expected}, got {actual_mat}")
    print(f"  napari_streaming_config.well_filter should be {expected}, got {actual_napari}")
    print()
    
    if actual_mat == expected and actual_napari == expected:
        print("✅ SUCCESS: Step-level inheritance working correctly!")
    else:
        print("❌ FAILURE: Step-level inheritance not working!")
        print("This confirms the context discovery bug affects the compiler too.")

if __name__ == "__main__":
    test_step_inheritance()
