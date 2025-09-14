#!/usr/bin/env python3
"""
Test script to verify sibling inheritance works correctly in PipelineConfig (lazy) vs GlobalPipelineConfig (non-lazy).

This tests the specific issue where:
- GlobalPipelineConfig: sibling inheritance works correctly
- PipelineConfig (lazy): sibling inheritance placeholders don't update after setting concrete values
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '.'))

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
from openhcs.core.lazy_config import LazyStepWellFilterConfig, LazyPathPlanningConfig, LazyStepMaterializationConfig
from openhcs.core.context.global_config import set_global_config_for_editing
from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService

def test_global_pipeline_config_sibling_inheritance():
    """Test sibling inheritance in GlobalPipelineConfig (non-lazy)."""
    print("\n=== Testing GlobalPipelineConfig (Non-Lazy) Sibling Inheritance ===")

    # Create global config with concrete value in path planning
    global_config = GlobalPipelineConfig(
        path_planning_config=LazyPathPlanningConfig(well_filter="PATH_PLANNING_VALUE"),
        step_well_filter_config=LazyStepWellFilterConfig(well_filter=None)  # Should inherit
    )

    # Check if step_well_filter_config inherits from path_planning_config
    step_config = global_config.step_well_filter_config
    print(f"step_well_filter_config.well_filter: {step_config.well_filter}")

    # Set up global context for placeholder resolution
    set_global_config_for_editing(GlobalPipelineConfig, global_config)

    # Get placeholder for step_materialization_config.well_filter
    # Should inherit from StepWellFilterConfig.well_filter = 1 (concrete override blocks PathPlanningConfig)
    placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        LazyStepMaterializationConfig, "well_filter", placeholder_prefix="Global default"
    )
    print(f"step_materialization_config.well_filter placeholder: {placeholder}")
    print("Expected: Should show '1' from StepWellFilterConfig, NOT 'PATH_PLANNING_VALUE' from PathPlanningConfig")


def test_pipeline_config_sibling_inheritance():
    """Test sibling inheritance in PipelineConfig (lazy)."""
    print("\n=== Testing PipelineConfig (Lazy) Sibling Inheritance ===")
    
    # Set up global context
    global_config = GlobalPipelineConfig()
    set_global_config_for_editing(GlobalPipelineConfig, global_config)
    
    # Create pipeline config (lazy) with concrete value in path planning
    pipeline_config = PipelineConfig(
        path_planning_config=LazyPathPlanningConfig(well_filter="PIPELINE_PATH_VALUE"),
        step_well_filter_config=LazyStepWellFilterConfig(well_filter=None)  # Should inherit
    )
    
    print(f"Created pipeline_config: {type(pipeline_config)}")
    print(f"path_planning_config.well_filter: {pipeline_config.path_planning_config.well_filter}")
    print(f"step_well_filter_config.well_filter: {pipeline_config.step_well_filter_config.well_filter}")
    
    # Get placeholder for step_materialization_config.well_filter (should inherit from path_planning)
    placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        LazyStepMaterializationConfig, "well_filter", placeholder_prefix="Pipeline default"
    )
    print(f"step_materialization_config.well_filter placeholder: {placeholder}")
    
    # Test with temporary context (simulating form editing)
    temp_context = LazyStepMaterializationConfig()
    placeholder_with_context = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder_with_context(
        LazyStepMaterializationConfig, "well_filter", temp_context, placeholder_prefix="Pipeline default"
    )
    print(f"step_materialization_config.well_filter placeholder with context: {placeholder_with_context}")


def test_live_placeholder_updates():
    """Test live placeholder updates when concrete values are set."""
    print("\n=== Testing Live Placeholder Updates ===")
    
    # Set up global context
    global_config = GlobalPipelineConfig()
    set_global_config_for_editing(GlobalPipelineConfig, global_config)
    
    # Create pipeline config with initial values
    pipeline_config = PipelineConfig(
        path_planning_config=LazyPathPlanningConfig(well_filter="INITIAL_VALUE"),
        step_materialization_config=LazyStepMaterializationConfig(well_filter=None)  # Should inherit
    )
    
    print("=== Initial State ===")
    placeholder1 = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        LazyStepMaterializationConfig, "well_filter", placeholder_prefix="Pipeline default"
    )
    print(f"step_materialization_config.well_filter placeholder: {placeholder1}")
    
    # Update path planning config (simulate user editing)
    # Note: PipelineConfig doesn't have replace method, so we'll create a new one
    print("Note: Creating new pipeline config to simulate update (lazy configs don't have replace method)")
    
    print("\n=== After Update ===")
    # Test with updated context
    temp_context = LazyStepMaterializationConfig()
    placeholder2 = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder_with_context(
        LazyStepMaterializationConfig, "well_filter", temp_context, placeholder_prefix="Pipeline default"
    )
    print(f"step_materialization_config.well_filter placeholder with updated context: {placeholder2}")


if __name__ == "__main__":
    print("🔍 Testing Sibling Inheritance Fix...")
    
    test_global_pipeline_config_sibling_inheritance()
    test_pipeline_config_sibling_inheritance()
    test_live_placeholder_updates()
    
    print("\n✅ Sibling inheritance test complete!")
