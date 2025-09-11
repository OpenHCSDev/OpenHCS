#!/usr/bin/env python3
"""
Debug the regression where StepWellFilterConfig doesn't update StepMaterializationConfig.
"""

import sys
import os
sys.path.insert(0, '/home/ts/code/projects/openhcs')

def test_inheritance_regression():
    """Test the specific regression case."""
    print("=== Testing Inheritance Regression ===")
    
    from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
    from openhcs.core.lazy_config import LazyStepWellFilterConfig, LazyWellFilterConfig, LazyStepMaterializationConfig
    from openhcs.core.context.global_config import set_current_global_config
    from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
    
    print("\n--- Test Case 1: Only step_well_filter_config set ---")
    
    # Set up context with only step_well_filter_config
    pipeline_config = PipelineConfig(
        step_well_filter_config=LazyStepWellFilterConfig(well_filter='5')   # Only this set
    )
    
    global_config = GlobalPipelineConfig(
        step_well_filter_config=pipeline_config.step_well_filter_config
    )
    
    set_current_global_config(GlobalPipelineConfig, global_config)
    
    print(f"Context:")
    print(f"  step_well_filter_config.well_filter = '{global_config.step_well_filter_config.well_filter}'")
    print(f"  well_filter_config = None (not set)")
    
    # Test StepMaterializationConfig inheritance
    placeholder_text = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        LazyStepMaterializationConfig,
        'well_filter',
        app_config=global_config,
        placeholder_prefix="Pipeline default"
    )
    
    print(f"\nStepMaterializationConfig.well_filter placeholder: '{placeholder_text}'")
    print(f"Expected: 'Pipeline default: 5' (inherit from StepWellFilterConfig)")
    
    if placeholder_text == "Pipeline default: 5":
        print("✅ SUCCESS: Inheritance working correctly")
        return True
    else:
        print(f"❌ REGRESSION: Expected '5', got '{placeholder_text}'")
        return False

def test_non_inheritance_case():
    """Test that StepWellFilterConfig doesn't inherit when it has its own value."""
    print("\n\n=== Testing Non-Inheritance Case ===")
    
    from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
    from openhcs.core.lazy_config import LazyStepWellFilterConfig, LazyWellFilterConfig
    from openhcs.core.context.global_config import set_current_global_config
    from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
    
    # Set up context with both configs
    pipeline_config = PipelineConfig(
        well_filter_config=LazyWellFilterConfig(well_filter='2'),           # Lower precedence
        step_well_filter_config=LazyStepWellFilterConfig(well_filter='5')   # Higher precedence
    )
    
    global_config = GlobalPipelineConfig(
        well_filter_config=pipeline_config.well_filter_config,
        step_well_filter_config=pipeline_config.step_well_filter_config
    )
    
    set_current_global_config(GlobalPipelineConfig, global_config)
    
    print(f"Context:")
    print(f"  well_filter_config.well_filter = '{global_config.well_filter_config.well_filter}'")
    print(f"  step_well_filter_config.well_filter = '{global_config.step_well_filter_config.well_filter}'")
    
    # Test that StepWellFilterConfig uses its own value, not inheritance
    # This should be testing a field that StepWellFilterConfig doesn't override
    # Let's test well_filter_mode instead
    placeholder_text = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        LazyStepWellFilterConfig,
        'well_filter',  # This field has its own value
        app_config=global_config,
        placeholder_prefix="Pipeline default"
    )
    
    print(f"\nStepWellFilterConfig.well_filter placeholder: '{placeholder_text}'")
    print(f"Expected: 'Pipeline default: 5' (own value, not inherited)")
    
    if placeholder_text == "Pipeline default: 5":
        print("✅ SUCCESS: Using own value, not inheriting")
        return True
    else:
        print(f"❌ FAILURE: Expected '5', got '{placeholder_text}'")
        return False

if __name__ == "__main__":
    success1 = test_inheritance_regression()
    success2 = test_non_inheritance_case()
    
    print(f"\n=== SUMMARY ===")
    if success1 and success2:
        print("🎉 All tests passed!")
    else:
        print("💥 Some tests failed!")
        if not success1:
            print("  - Inheritance regression detected")
        if not success2:
            print("  - Non-inheritance case failed")
