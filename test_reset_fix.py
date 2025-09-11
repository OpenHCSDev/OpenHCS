#!/usr/bin/env python3
"""
Test the reset fix for StepWellFilterConfig.well_filter multiple inheritance.
"""

import sys
import os
sys.path.insert(0, '/home/ts/code/projects/openhcs')

from openhcs.core.config import GlobalPipelineConfig, WellFilterConfig, StepWellFilterConfig
from openhcs.core.lazy_config import LazyWellFilterConfig, LazyStepWellFilterConfig
from openhcs.core.context.global_config import set_current_global_config
from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService

def test_step_well_filter_reset():
    """Test that StepWellFilterConfig.well_filter shows proper inheritance on reset."""
    print("=== Testing StepWellFilterConfig Reset Inheritance ===")
    
    # Set up context with WellFilterConfig having a value
    global_config = GlobalPipelineConfig(
        well_filter_config=LazyWellFilterConfig(well_filter='parent_value'),
        step_well_filter_config=LazyStepWellFilterConfig(well_filter=None)  # Reset case
    )
    
    set_current_global_config(GlobalPipelineConfig, global_config)
    
    # Test placeholder resolution for reset StepWellFilterConfig
    placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        LazyStepWellFilterConfig, 'well_filter'
    )
    
    print(f"StepWellFilterConfig.well_filter placeholder (reset): '{placeholder}'")
    
    if placeholder and 'parent_value' in placeholder:
        print("✅ SUCCESS: Shows inheritance from WellFilterConfig")
        return True
    else:
        print(f"❌ FAILURE: Expected 'parent_value' in placeholder, got: '{placeholder}'")
        return False

def test_step_well_filter_concrete():
    """Test that StepWellFilterConfig.well_filter uses own value when not reset."""
    print("\n=== Testing StepWellFilterConfig Concrete Value ===")
    
    # Set up context with both configs having values
    global_config = GlobalPipelineConfig(
        well_filter_config=LazyWellFilterConfig(well_filter='parent_value'),
        step_well_filter_config=LazyStepWellFilterConfig(well_filter='own_value')  # Concrete case
    )
    
    set_current_global_config(GlobalPipelineConfig, global_config)
    
    # Test placeholder resolution for concrete StepWellFilterConfig
    placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        LazyStepWellFilterConfig, 'well_filter'
    )
    
    print(f"StepWellFilterConfig.well_filter placeholder (concrete): '{placeholder}'")
    
    if placeholder and 'own_value' in placeholder:
        print("✅ SUCCESS: Uses own value, not inheritance")
        return True
    else:
        print(f"❌ FAILURE: Expected 'own_value' in placeholder, got: '{placeholder}'")
        return False

if __name__ == "__main__":
    success1 = test_step_well_filter_reset()
    success2 = test_step_well_filter_concrete()
    
    print(f"\n=== SUMMARY ===")
    if success1 and success2:
        print("🎉 All tests passed! Reset inheritance fix working!")
    else:
        print("💥 Some tests failed!")
        if not success1:
            print("  - Reset inheritance not working")
        if not success2:
            print("  - Concrete value behavior broken")
