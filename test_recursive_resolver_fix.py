#!/usr/bin/env python3
"""
Test script to verify that the recursive resolver fix works for both 
top-level and nested config placeholders.
"""

import sys
import os
sys.path.insert(0, os.path.abspath('.'))

from openhcs.core.config import (
    GlobalPipelineConfig, PipelineConfig, StepMaterializationConfig,
    StepWellFilterConfig, PathPlanningConfig
)
from dataclasses import fields
from openhcs.core.lazy_config import LazyDataclassFactory
from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
from openhcs.core.context.global_config import set_current_global_config


def test_recursive_resolver_fix():
    """Test that recursive resolver works for both top-level and nested configs."""
    print("🧪 Testing Recursive Resolver Fix")
    print("=" * 50)
    
    # Set up global config with concrete values for inheritance
    global_config = GlobalPipelineConfig(
        num_workers=8,  # Top-level field
        materialization_results_path="global_results",  # Top-level field
        step_well_filter_config=StepWellFilterConfig(well_filter=5),  # Nested config
        step_materialization_config=StepMaterializationConfig(
            well_filter=None,  # Should inherit from step_well_filter_config
            sub_dir="global_sub_dir"  # Concrete value
        )
    )
    
    # Set thread-local context
    set_current_global_config(GlobalPipelineConfig, global_config)
    
    # Create lazy types
    LazyPipelineConfig = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
        base_class=PipelineConfig,
        global_config_type=GlobalPipelineConfig,
        lazy_class_name="LazyPipelineConfig"
    )
    
    LazyStepMaterializationConfig = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
        base_class=StepMaterializationConfig,
        global_config_type=GlobalPipelineConfig,
        lazy_class_name="LazyStepMaterializationConfig"
    )
    
    print("\n1. Testing TOP-LEVEL field placeholders (should work with recursive resolver):")
    
    # Test top-level PipelineConfig field
    top_level_placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        LazyPipelineConfig, "num_workers", placeholder_prefix="Global default"
    )
    print(f"   PipelineConfig.num_workers: '{top_level_placeholder}'")
    
    # Test another top-level field
    path_placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        LazyPipelineConfig, "materialization_results_path", placeholder_prefix="Global default"
    )
    print(f"   PipelineConfig.materialization_results_path: '{path_placeholder}'")
    
    print("\n2. Testing NESTED config placeholders (should now work with fixed recursive resolver):")
    
    # Test nested config field that should inherit
    nested_placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        LazyStepMaterializationConfig, "well_filter", placeholder_prefix="Pipeline default"
    )
    print(f"   StepMaterializationConfig.well_filter: '{nested_placeholder}'")
    
    # Test nested config field with concrete value
    sub_dir_placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        LazyStepMaterializationConfig, "sub_dir", placeholder_prefix="Pipeline default"
    )
    print(f"   StepMaterializationConfig.sub_dir: '{sub_dir_placeholder}'")
    
    print("\n3. Testing with PipelineConfig context (simulating form editing):")
    
    # Create a pipeline config context (simulates editing a pipeline config)
    pipeline_config = PipelineConfig(
        num_workers=4,  # Override global
        step_well_filter_config=StepWellFilterConfig(well_filter=10),  # Override global
        step_materialization_config=StepMaterializationConfig(well_filter=None)  # Should inherit
    )

    print(f"   Pipeline config has step_well_filter_config.well_filter = {pipeline_config.step_well_filter_config.well_filter}")
    print(f"   Pipeline config has step_materialization_config.well_filter = {pipeline_config.step_materialization_config.well_filter}")

    # Test with temporary context (simulates live placeholder updates)

    temp_context_placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder_with_context(
        LazyStepMaterializationConfig, "well_filter",
        pipeline_config,  # Pass the full pipeline config as context, not just the nested config
        placeholder_prefix="Pipeline default"
    )
    print(f"   With pipeline context - StepMaterializationConfig.well_filter: '{temp_context_placeholder}'")
    
    print("\n4. Validation:")
    
    # Validate that all placeholders are working
    success = True
    
    if not top_level_placeholder or "8" not in top_level_placeholder:
        print("   ❌ Top-level num_workers placeholder failed")
        success = False
    else:
        print("   ✅ Top-level num_workers placeholder working")
    
    if not nested_placeholder or "5" not in nested_placeholder:
        print("   ❌ Nested well_filter placeholder failed")
        success = False
    else:
        print("   ✅ Nested well_filter placeholder working")
    
    if not sub_dir_placeholder or "global_sub_dir" not in sub_dir_placeholder:
        print("   ❌ Nested sub_dir placeholder failed")
        success = False
    else:
        print("   ✅ Nested sub_dir placeholder working")
    
    if not temp_context_placeholder or "10" not in temp_context_placeholder:
        print(f"   ❌ Context-based placeholder failed (expected '10', got '{temp_context_placeholder}')")
        success = False
    else:
        print("   ✅ Context-based placeholder working")
    
    print(f"\n🎯 Overall Result: {'SUCCESS' if success else 'FAILED'}")
    
    if success:
        print("   Both top-level and nested config placeholders are working!")
        print("   The recursive resolver fix is successful.")
    else:
        print("   Some placeholders are still broken.")
        print("   The recursive resolver needs further fixes.")
    
    return success


if __name__ == "__main__":
    test_recursive_resolver_fix()
