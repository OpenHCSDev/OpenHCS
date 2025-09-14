#!/usr/bin/env python3
"""
Test script for the recursive dual-axis resolver implementation.

This tests the basic functionality of the recursive algorithm:
1. Check concrete value at current context level
2. Try Y-axis inheritance at current context level
3. If no resolution, recurse to parent context level
4. Continue until thread-local storage
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '.'))

from dataclasses import dataclass
from typing import Optional
from openhcs.core.dual_axis_resolver_recursive import (
    RecursiveContextualResolver,
    initialize_recursive_dual_axis_resolution,
    get_recursive_resolver
)

# Test dataclasses
@dataclass
class StepWellFilterConfig:
    well_filter: Optional[str] = None

@dataclass  
class StepMaterializationConfig(StepWellFilterConfig):
    well_filter: Optional[str] = None
    output_format: Optional[str] = None

@dataclass
class PipelineConfig:
    step_well_filter_config: StepWellFilterConfig
    step_materialization_config: StepMaterializationConfig

@dataclass
class GlobalPipelineConfig:
    step_well_filter_config: StepWellFilterConfig
    step_materialization_config: StepMaterializationConfig

# Mock orchestrator
class MockOrchestrator:
    def __init__(self, pipeline_config: PipelineConfig):
        self.pipeline_config = pipeline_config
        self.plate_path = "/mock/plate/path"

# Mock step
class MockStep:
    def __init__(self, orchestrator: MockOrchestrator):
        self.orchestrator = orchestrator
        self.step_materialization_config = StepMaterializationConfig()

def test_basic_recursive_resolution():
    """Test basic recursive resolution through context hierarchy."""
    print("=== Testing Basic Recursive Resolution ===")

    # Initialize the recursive system
    initialize_recursive_dual_axis_resolution()

    # Create test hierarchy: step → orchestrator → (thread-local would be here)
    global_config = GlobalPipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter="GLOBAL_A01"),
        step_materialization_config=StepMaterializationConfig(well_filter="GLOBAL_MAT_B01")
    )

    pipeline_config = PipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter="PIPELINE_A01"),
        step_materialization_config=StepMaterializationConfig(well_filter=None)  # Should inherit
    )

    orchestrator = MockOrchestrator(pipeline_config)
    step = MockStep(orchestrator)

    # Test context hierarchy discovery
    resolver = get_recursive_resolver()

    # Test 1: Direct context discovery
    print("\n--- Test 1: Context Hierarchy Discovery ---")
    from openhcs.core.lazy_config import get_base_type_for_lazy

    # Mock the base type lookup for our test
    def mock_get_base_type_for_lazy(lazy_type):
        if lazy_type == type(step.step_materialization_config):
            return StepMaterializationConfig
        return None

    # Temporarily replace the function
    original_get_base_type = get_base_type_for_lazy
    import openhcs.core.dual_axis_resolver_recursive as resolver_module
    resolver_module.get_base_type_for_lazy = mock_get_base_type_for_lazy

    try:
        # Test context hierarchy discovery from within step context
        def test_from_step_context():
            # This simulates being called from within a step method
            hierarchy = resolver._discover_context_hierarchy(StepMaterializationConfig)
            print(f"Discovered hierarchy from step context: {[type(ctx).__name__ for ctx in hierarchy]}")
            return hierarchy

        # Call from step context to simulate real usage
        hierarchy = test_from_step_context()

        # Test concrete value resolution at level
        print("\n--- Test 2: Concrete Value Resolution ---")

        # Test getting concrete value from orchestrator level
        concrete_value = resolver._get_concrete_value_at_level(
            orchestrator, StepWellFilterConfig, "well_filter"
        )
        print(f"Concrete value from orchestrator for StepWellFilterConfig.well_filter: {concrete_value}")

        # Test inheritance check
        print("\n--- Test 3: Inheritance Check ---")
        can_inherit = resolver._can_inherit_from(StepWellFilterConfig, "well_filter")
        print(f"Can inherit from StepWellFilterConfig.well_filter: {can_inherit}")

        print("\n--- Test 4: Full Recursive Resolution ---")

        # Test with manual hierarchy to verify algorithm
        manual_hierarchy = [orchestrator]  # Simplified hierarchy for testing
        result = resolver._resolve_field_recursive(
            StepMaterializationConfig,
            "well_filter",
            manual_hierarchy
        )
        print(f"Recursive resolution result (manual hierarchy): {result}")

        # Test with discovered hierarchy
        if hierarchy:
            result2 = resolver._resolve_field_recursive(
                StepMaterializationConfig,
                "well_filter",
                hierarchy
            )
            print(f"Recursive resolution result (discovered hierarchy): {result2}")

    finally:
        # Restore original function
        resolver_module.get_base_type_for_lazy = original_get_base_type

    print("\n=== Test Complete ===")

def test_inheritance_blocking():
    """Test inheritance blocking behavior."""
    print("\n=== Testing Inheritance Blocking ===")

    @dataclass
    class BlockingConfig(StepWellFilterConfig):
        well_filter: str = "BLOCKED_VALUE"  # Concrete override blocks inheritance

    resolver = get_recursive_resolver()

    # Test that concrete override blocks inheritance
    can_inherit = resolver._can_inherit_from(BlockingConfig, "well_filter")
    print(f"Can inherit from BlockingConfig (has concrete override): {can_inherit}")

    # Test that non-concrete allows inheritance
    can_inherit_base = resolver._can_inherit_from(StepWellFilterConfig, "well_filter")
    print(f"Can inherit from StepWellFilterConfig (no concrete override): {can_inherit_base}")

def test_correct_algorithm():
    """Test the correct algorithm: 1. current concrete, 2. parent context concrete, 3. Y-axis, 4. recurse."""
    print("\n=== Testing Correct Algorithm ===")

    # Create test scenarios to verify each step of the algorithm
    resolver = get_recursive_resolver()

    # Scenario 1: Step 1 - Current context concrete value should win
    print("\n--- Scenario 1: Current Context Concrete Wins ---")
    step_config = StepMaterializationConfig(well_filter="STEP_CONCRETE")
    orchestrator_config = PipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter="ORCHESTRATOR_CONCRETE"),
        step_materialization_config=StepMaterializationConfig(well_filter="ORCHESTRATOR_CONCRETE")
    )
    orchestrator = MockOrchestrator(orchestrator_config)

    # Test with manual hierarchy
    result1 = resolver._resolve_field_recursive(
        StepMaterializationConfig,
        "well_filter",
        [step_config, orchestrator]  # step has concrete, orchestrator has concrete
    )
    print(f"Result (step concrete vs orchestrator concrete): {result1}")
    assert result1 == "STEP_CONCRETE", f"Expected STEP_CONCRETE, got {result1}"

    # Scenario 2: Step 2 - Parent context concrete beats Y-axis inheritance
    print("\n--- Scenario 2: Parent Context Concrete Beats Y-axis ---")
    step_config_empty = StepMaterializationConfig(well_filter=None)  # No concrete at step
    step_config_empty.step_well_filter_config = StepWellFilterConfig(well_filter="STEP_INHERITED")  # But inheritance available

    result2 = resolver._resolve_field_recursive(
        StepMaterializationConfig,
        "well_filter",
        [step_config_empty, orchestrator]  # step has None, orchestrator has concrete, step has inheritance
    )
    print(f"Result (parent concrete vs step inheritance): {result2}")
    assert result2 == "ORCHESTRATOR_CONCRETE", f"Expected ORCHESTRATOR_CONCRETE, got {result2}"

    # Scenario 3: Step 3 - Y-axis inheritance works when no parent context concrete
    print("\n--- Scenario 3: Y-axis Inheritance Works ---")
    orchestrator_empty = MockOrchestrator(PipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter="ORCHESTRATOR_INHERITED"),
        step_materialization_config=StepMaterializationConfig(well_filter=None)  # No concrete
    ))

    result3 = resolver._resolve_field_recursive(
        StepMaterializationConfig,
        "well_filter",
        [step_config_empty, orchestrator_empty]  # both have None concrete, but step has inheritance
    )
    print(f"Result (Y-axis inheritance): {result3}")
    # This should find inheritance at step level or orchestrator level

    print("✅ Algorithm test complete!")

def test_simulated_lazy_config_usage():
    """Test simulated lazy config usage pattern."""
    print("\n=== Testing Simulated Lazy Config Usage ===")

    # Create test context
    pipeline_config = PipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter="PIPELINE_A01"),
        step_materialization_config=StepMaterializationConfig(well_filter=None)
    )

    orchestrator = MockOrchestrator(pipeline_config)

    # Simulate being in orchestrator context and accessing lazy config
    def simulate_orchestrator_method():
        # This simulates accessing a lazy config field from within orchestrator
        resolver = get_recursive_resolver()

        # Mock lazy instance
        class MockLazyStepMaterializationConfig:
            pass

        lazy_instance = MockLazyStepMaterializationConfig()

        # Mock the base type lookup
        def mock_get_base_type_for_lazy(lazy_type):
            if lazy_type == MockLazyStepMaterializationConfig:
                return StepMaterializationConfig
            return None

        import openhcs.core.dual_axis_resolver_recursive as resolver_module
        original_get_base_type = resolver_module.get_base_type_for_lazy
        resolver_module.get_base_type_for_lazy = mock_get_base_type_for_lazy

        try:
            # This simulates lazy_config.well_filter access
            result = resolver.resolve_field(lazy_instance, "well_filter")
            print(f"Simulated lazy config resolution: {result}")
            return result
        finally:
            resolver_module.get_base_type_for_lazy = original_get_base_type

    # Call from orchestrator context
    result = simulate_orchestrator_method()
    print(f"Final result: {result}")

if __name__ == "__main__":
    test_basic_recursive_resolution()
    test_inheritance_blocking()
    test_correct_algorithm()
    test_simulated_lazy_config_usage()
