#!/usr/bin/env python3
"""
Debug inheritance blocking behavior in detail.
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

def test_direct_resolution():
    """Test direct resolution with the recursive resolver."""
    print("=== Direct Resolution Test ===")
    
    # Set up global context
    global_config = GlobalPipelineConfig(
        path_planning_config=LazyPathPlanningConfig(well_filter="PATH_VALUE"),
        step_well_filter_config=LazyStepWellFilterConfig(well_filter=None)  # Will get default 1
    )
    set_global_config_for_editing(GlobalPipelineConfig, global_config)
    
    print(f"Global config step_well_filter_config.well_filter: {global_config.step_well_filter_config.well_filter}")
    print(f"Global config path_planning_config.well_filter: {global_config.path_planning_config.well_filter}")

    # Check if there's a step_materialization_config in global config
    if hasattr(global_config, 'step_materialization_config'):
        step_mat_config = global_config.step_materialization_config
        print(f"Global config step_materialization_config.well_filter: {step_mat_config.well_filter}")
    else:
        print("Global config has no step_materialization_config field")

    # Test direct resolution
    resolver = get_recursive_resolver()
    temp_instance = LazyStepMaterializationConfig()

    print(f"\nResolving LazyStepMaterializationConfig.well_filter...")
    resolved_value = resolver.resolve_field(temp_instance, "well_filter")
    print(f"Resolved value: {resolved_value}")
    
    # Test with different context
    print(f"\n=== Testing with PipelineConfig context ===")
    pipeline_config = PipelineConfig(
        path_planning_config=LazyPathPlanningConfig(well_filter="PIPELINE_PATH_VALUE"),
        step_well_filter_config=LazyStepWellFilterConfig(well_filter=None)  # Will get default 1
    )
    
    print(f"Pipeline config step_well_filter_config.well_filter: {pipeline_config.step_well_filter_config.well_filter}")
    print(f"Pipeline config path_planning_config.well_filter: {pipeline_config.path_planning_config.well_filter}")
    
    # Test resolution in pipeline context
    temp_instance2 = LazyStepMaterializationConfig()
    resolved_value2 = resolver.resolve_field(temp_instance2, "well_filter")
    print(f"Resolved value in pipeline context: {resolved_value2}")

if __name__ == "__main__":
    test_direct_resolution()
