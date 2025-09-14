#!/usr/bin/env python3
"""
Test the dual-axis resolver implementation using real OpenHCS configs and objects.

This test validates:
1. Context-level inheritance blocking
2. Class-level inheritance blocking
3. Parent type inheritance in context resolution
4. Real config hierarchy resolution (StepMaterializationConfig → StepWellFilterConfig)
5. Multiple inheritance scenarios
"""

import sys
import os
sys.path.insert(0, '/home/ts/code/projects/openhcs')

from dataclasses import dataclass
from typing import Optional, Union, List
from pathlib import Path

# Import real OpenHCS configs and lazy versions
from openhcs.core.config import (
    GlobalPipelineConfig, WellFilterConfig, StepWellFilterConfig,
    StepMaterializationConfig, PathPlanningConfig, WellFilterMode
)

# Import the existing lazy dataclasses created by @global_pipeline_config decorator
from openhcs.core.lazy_config import (
    LazyStepMaterializationConfig, LazyStepWellFilterConfig, LazyPathPlanningConfig,
    get_base_type_for_lazy, ensure_global_config_context
)

from openhcs.core.dual_axis_resolver_implementation import (
    ContextualResolver, ContextDiscovery, initialize_dual_axis_resolution
)
from openhcs.core.context.global_config import set_current_global_config

# Initialize the dual-axis system
initialize_dual_axis_resolution()

def test_context_level_blocking():
    """Test that context-level concrete values block inheritance."""
    print("\n=== TEST 1: Context-Level Blocking ===")

    # Create real global config with concrete values
    global_config = GlobalPipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter=8),  # Global default
        step_materialization_config=StepMaterializationConfig(well_filter=5)  # Global materialization
    )

    # Set up thread-local context (this is how OpenHCS works)
    set_current_global_config(GlobalPipelineConfig, global_config)

    # Test 1: User-set value should take precedence
    lazy_step_mat_user = LazyStepMaterializationConfig(well_filter="B01")  # User override
    user_result = lazy_step_mat_user.well_filter  # Use normal lazy resolution
    print(f"User override test: {user_result} (expected: B01)")

    # Test 2: No user value - should resolve from context
    lazy_step_mat_inherit = LazyStepMaterializationConfig()  # No user override
    inherit_result = lazy_step_mat_inherit.well_filter  # Should inherit from context
    print(f"Inheritance test: {inherit_result} (expected: 5 from global step_materialization_config)")

    # Test 3: Direct resolver test for context resolution
    resolver = ContextualResolver(global_config)
    resolver_result = resolver.resolve_field(lazy_step_mat_inherit, 'well_filter')
    print(f"Direct resolver test: {resolver_result} (expected: 5)")

    # Verify the dual-axis resolver is working
    assert inherit_result == 5, f"Expected 5 from global context, got {inherit_result}"
    assert resolver_result == 5, f"Expected 5 from resolver, got {resolver_result}"
    print("✅ Context-level resolution works correctly")


def test_class_level_blocking():
    """Test that class-level concrete overrides block inheritance when no context available."""
    print("\n=== TEST 2: Class-Level Blocking ===")

    # Create minimal context (no step configs)
    global_config = GlobalPipelineConfig(num_workers=4)  # No step configs
    set_current_global_config(GlobalPipelineConfig, global_config)

    # Create lazy instance with no user overrides
    lazy_step_well = LazyStepWellFilterConfig()  # All None - should resolve from context/class

    # Test resolution
    resolver = ContextualResolver(global_config)
    result = resolver.resolve_field(lazy_step_well, 'well_filter')

    print(f"StepWellFilterConfig.well_filter resolved to: {result}")
    print(f"Expected: Should use class default = 1 (no context available)")

    # Should get class default since no context
    assert result == 1, f"Expected class default 1, got {result}"
    print("✅ Class-level blocking works correctly")


def test_parent_type_inheritance():
    """Test that child configs can inherit from parent type instances in context."""
    print("\n=== TEST 3: Parent Type Inheritance ===")

    # Create context with only parent type instance (no child type)
    global_config = GlobalPipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter=["A01", "A02"]),  # Parent type
        # No step_materialization_config - child should inherit from parent
    )
    set_current_global_config(GlobalPipelineConfig, global_config)

    # Create child type lazy instance with no user overrides
    lazy_step_mat = LazyStepMaterializationConfig()  # Should inherit from parent type

    # Test resolution
    resolver = ContextualResolver(global_config)
    result = resolver.resolve_field(lazy_step_mat, 'well_filter')

    print(f"StepMaterializationConfig.well_filter resolved to: {result}")
    print(f"Expected: Should inherit from parent StepWellFilterConfig = ['A01', 'A02']")

    # Should inherit from parent type in context
    assert result == ["A01", "A02"], f"Expected ['A01', 'A02'] from parent type, got {result}"
    print("✅ Parent type inheritance works correctly")


def test_multiple_inheritance_resolution():
    """Test resolution with multiple inheritance (StepMaterializationConfig inherits from both StepWellFilterConfig and PathPlanningConfig)."""
    print("\n=== TEST 4: Multiple Inheritance Resolution ===")

    # Create context with both parent types
    global_config = GlobalPipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter=3),
        path_planning_config=PathPlanningConfig(output_dir_suffix="_custom"),
        # No step_materialization_config - should inherit from both parents
    )
    set_current_global_config(GlobalPipelineConfig, global_config)

    # Create lazy instance
    lazy_step_mat = LazyStepMaterializationConfig()  # Should inherit from both parents

    # Test resolution
    resolver = ContextualResolver(global_config)

    # Test field from first parent (StepWellFilterConfig)
    well_filter_result = resolver.resolve_field(lazy_step_mat, 'well_filter')
    print(f"well_filter resolved to: {well_filter_result} (from StepWellFilterConfig)")

    # Test field from second parent (PathPlanningConfig)
    suffix_result = resolver.resolve_field(lazy_step_mat, 'output_dir_suffix')
    print(f"output_dir_suffix resolved to: {suffix_result} (from PathPlanningConfig)")

    # Verify both inheritances work
    assert well_filter_result == 3, f"Expected 3 from StepWellFilterConfig, got {well_filter_result}"
    assert suffix_result == "_custom", f"Expected '_custom' from PathPlanningConfig, got {suffix_result}"
    print("✅ Multiple inheritance resolution works correctly")


def test_context_priority_over_class():
    """Test that context values always take precedence over class defaults."""
    print("\n=== TEST 5: Context Priority Over Class ===")

    # Create context that should override class defaults
    global_config = GlobalPipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter="context_value")
    )
    set_current_global_config(GlobalPipelineConfig, global_config)

    # Create lazy instance - class has default of 1, context has "context_value"
    lazy_step_well = LazyStepWellFilterConfig()  # Should resolve from context

    # Test resolution
    resolver = ContextualResolver(global_config)
    result = resolver.resolve_field(lazy_step_well, 'well_filter')

    print(f"StepWellFilterConfig.well_filter resolved to: {result}")
    print(f"Class default: 1, Context value: 'context_value'")
    print(f"Expected: Context should win = 'context_value'")

    # Context should always win over class default
    assert result == "context_value", f"Expected 'context_value' from context, got {result}"
    print("✅ Context priority over class works correctly")


if __name__ == "__main__":
    print("Testing Dual-Axis Resolver with Real OpenHCS Configs")
    print("=" * 60)
    
    try:
        test_context_level_blocking()
        test_class_level_blocking() 
        test_parent_type_inheritance()
        test_multiple_inheritance_resolution()
        test_context_priority_over_class()
        
        print("\n" + "=" * 60)
        print("🎉 ALL TESTS PASSED! Dual-axis resolver working correctly.")
        
    except Exception as e:
        print(f"\n❌ TEST FAILED: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
