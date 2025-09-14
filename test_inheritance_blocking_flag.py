#!/usr/bin/env python3
"""
Test that inheritance blocking acts as a flag when there's more context hierarchy.
"""

import sys
import os
import logging
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '.'))

# Set up debug logging
logging.basicConfig(level=logging.DEBUG, format='%(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger('openhcs.core.dual_axis_resolver_recursive')
logger.setLevel(logging.DEBUG)

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig, StepMaterializationConfig
from openhcs.core.lazy_config import LazyStepMaterializationConfig, LazyPathPlanningConfig, LazyStepWellFilterConfig
from openhcs.core.context.global_config import set_global_config_for_editing
from openhcs.core.dual_axis_resolver_recursive import get_recursive_resolver

def test_inheritance_blocking_flag():
    """Test that blocking class acts as flag when there's more context hierarchy."""
    print("=== Testing Inheritance Blocking Flag Behavior ===")
    
    # Set up global context with concrete value in step_well_filter_config
    global_config = GlobalPipelineConfig(
        path_planning_config=LazyPathPlanningConfig(well_filter="GLOBAL_PATH_VALUE"),
        step_well_filter_config=LazyStepWellFilterConfig(well_filter="GLOBAL_STEP_VALUE")  # Concrete value
    )
    set_global_config_for_editing(GlobalPipelineConfig, global_config)
    
    print(f"Global config step_well_filter_config.well_filter: {global_config.step_well_filter_config.well_filter}")
    print(f"Global config path_planning_config.well_filter: {global_config.path_planning_config.well_filter}")
    
    # Create pipeline config with None in step_well_filter_config (should act as blocking flag)
    pipeline_config = PipelineConfig(
        path_planning_config=LazyPathPlanningConfig(well_filter="PIPELINE_PATH_VALUE"),
        step_well_filter_config=LazyStepWellFilterConfig(well_filter=None)  # None = blocking flag
    )
    
    print(f"Pipeline config step_well_filter_config.well_filter: {pipeline_config.step_well_filter_config.well_filter}")
    print(f"Pipeline config path_planning_config.well_filter: {pipeline_config.path_planning_config.well_filter}")
    
    # Test resolution - should go to global context, NOT use class default
    resolver = get_recursive_resolver()
    temp_instance = LazyStepMaterializationConfig()
    
    print(f"\nResolving LazyStepMaterializationConfig.well_filter...")
    print("Expected: Should find 'GLOBAL_STEP_VALUE' from global context")
    print("NOT: Should NOT use class default '1' because there's more context hierarchy")
    
    resolved_value = resolver.resolve_field(temp_instance, "well_filter")
    print(f"Resolved value: {resolved_value}")
    
    if resolved_value == "GLOBAL_STEP_VALUE":
        print("✅ CORRECT: Blocking flag worked - went to parent context")
    elif resolved_value == 1:
        print("❌ WRONG: Used class default instead of going to parent context")
    else:
        print(f"❌ UNEXPECTED: Got {resolved_value}")

if __name__ == "__main__":
    test_inheritance_blocking_flag()
