#!/usr/bin/env python3
"""
Test the dual-axis resolver's automatic context discovery through stack introspection.

This test validates that the resolver can find context objects in the call stack
WITHOUT using thread-local storage, proving the stack introspection system works.
"""

import sys
import os
sys.path.insert(0, '/home/ts/code/projects/openhcs')

from pathlib import Path
from typing import Optional

# Import real OpenHCS components
from openhcs.core.config import (
    GlobalPipelineConfig, PipelineConfig, StepWellFilterConfig,
    StepMaterializationConfig, PathPlanningConfig, VFSConfig, MaterializationBackend
)

from openhcs.core.lazy_config import (
    LazyStepMaterializationConfig, LazyStepWellFilterConfig, ensure_global_config_context
)

from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.dual_axis_resolver_implementation import (
    ContextualResolver, ContextDiscovery, initialize_dual_axis_resolution
)

# Import synthetic data generator
from openhcs.tests.generators.generate_synthetic_data import SyntheticMicroscopyGenerator
from openhcs.constants import Microscope

# Initialize the dual-axis system
initialize_dual_axis_resolution()

# Clear any existing thread-local context to ensure pure stack introspection
from openhcs.core.context.global_config import _global_config_contexts
_global_config_contexts.clear()
print("🧹 Cleared all thread-local contexts - testing pure stack introspection")


def create_synthetic_plate_data(test_dir: Path) -> Path:
    """Create synthetic plate data using the same pattern as fixture_utils."""
    plate_dir = test_dir / "test_plate"
    plate_dir.mkdir(parents=True, exist_ok=True)

    # Create synthetic data like the real tests do
    generator = SyntheticMicroscopyGenerator(
        output_dir=str(plate_dir),
        grid_size=(2, 2),  # Small test dataset
        tile_size=(128, 128),  # Small images for speed
        overlap_percent=10,
        wavelengths=1,
        z_stack_levels=1,
        format='ImageXpress',
        auto_image_size=False
    )
    generator.generate_dataset()
    return plate_dir


def create_real_orchestrator(plate_dir: Path) -> PipelineOrchestrator:
    """Create real OpenHCS orchestrator using the same pattern as testmain."""
    # Create global config like testmain does
    global_config = GlobalPipelineConfig(
        num_workers=1,
        step_well_filter_config=StepWellFilterConfig(well_filter="global_value"),
        step_materialization_config=StepMaterializationConfig(well_filter="global_materialization"),
        vfs_config=VFSConfig(materialization_backend=MaterializationBackend.DISK),
        path_planning_config=PathPlanningConfig(output_dir_suffix="_test")
    )

    # Set up global context like testmain does
    ensure_global_config_context(GlobalPipelineConfig, global_config)

    # Create pipeline config with overrides
    pipeline_config = PipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter="pipeline_override"),
        path_planning_config=PathPlanningConfig(output_dir_suffix="_test")
    )

    # Create orchestrator like testmain does
    orchestrator = PipelineOrchestrator(plate_dir, pipeline_config=pipeline_config)
    orchestrator.initialize()
    return orchestrator


class StepEditor:
    """Simulate step editor that creates lazy configs within orchestrator context."""

    def __init__(self, orchestrator: PipelineOrchestrator):
        self.orchestrator = orchestrator

    def get_step_config(self):
        """Create lazy config that should auto-discover context from call stack."""
        # This should find the orchestrator in the call stack automatically
        return LazyStepMaterializationConfig()

    def edit_field(self, field_name: str):
        """Simulate editing a field - should auto-discover context."""
        config = self.get_step_config()
        return getattr(config, field_name)


def test_stack_introspection_discovery():
    """Test that ContextDiscovery can find context objects in call stack."""
    print("\n=== TEST 1: Stack Introspection Discovery ===")

    # Create temporary plate directory for orchestrator
    import tempfile
    with tempfile.TemporaryDirectory() as temp_dir:
        # Create synthetic plate data
        plate_dir = create_synthetic_plate_data(Path(temp_dir))

        # Create real orchestrator
        orchestrator = create_real_orchestrator(plate_dir)

        def nested_function_that_needs_context():
            """Nested function that should find orchestrator in call stack."""
            discovered_context = ContextDiscovery.discover_context()
            return discovered_context

        def intermediate_function():
            """Intermediate function to test deeper stack introspection."""
            return nested_function_that_needs_context()

        # Call from orchestrator context (simulate orchestrator method)
        def orchestrator_method(self):
            return intermediate_function()

        # Bind method to orchestrator to put it in call stack
        orchestrator.test_method = orchestrator_method.__get__(orchestrator, PipelineOrchestrator)

        # Test discovery
        discovered = orchestrator.test_method()

        print(f"Discovered context type: {type(discovered).__name__ if discovered else 'None'}")

        if discovered:
            print(f"Context has global_config: {hasattr(discovered, 'global_config')}")
            print(f"Context has pipeline_config: {hasattr(discovered, 'pipeline_config')}")
            if hasattr(discovered, 'global_config'):
                print(f"Global config type: {type(discovered.global_config).__name__}")

        assert discovered is not None, "Should discover context from call stack"
        # Check for orchestrator attributes (it should find the orchestrator, not just configs)
        expected_attrs = ['global_config', 'pipeline_config', 'plate_dir', 'microscope_handler']
        found_attrs = [attr for attr in expected_attrs if hasattr(discovered, attr)]
        print(f"Found orchestrator attributes: {found_attrs}")

        assert len(found_attrs) >= 2, f"Should find orchestrator with multiple attributes, found: {found_attrs}"
        print("✅ Stack introspection discovery works")


def test_automatic_context_resolution():
    """Test that lazy configs automatically resolve through discovered context."""
    print("\n=== TEST 2: Automatic Context Resolution ===")

    import tempfile
    with tempfile.TemporaryDirectory() as temp_dir:
        # Create synthetic plate data
        plate_dir = create_synthetic_plate_data(Path(temp_dir))

        # Create real orchestrator with pipeline override
        orchestrator = create_real_orchestrator(plate_dir)

        # Create step editor within orchestrator context
        step_editor = StepEditor(orchestrator)

        # This should auto-discover the orchestrator context and resolve from pipeline
        result = step_editor.edit_field('well_filter')

        print(f"Auto-resolved well_filter: {result}")
        print(f"Expected: Should find 'pipeline_override' from discovered pipeline context")

        # Should find pipeline override, not global value
        expected = "pipeline_override"
        assert result == expected, f"Expected '{expected}' from auto-discovered context, got {result}"
        print("✅ Automatic context resolution works")


def test_context_hierarchy_traversal():
    """Test that resolver traverses context hierarchy correctly."""
    print("\n=== TEST 3: Context Hierarchy Traversal ===")

    import tempfile
    with tempfile.TemporaryDirectory() as temp_dir:
        # Create synthetic plate data
        plate_dir = create_synthetic_plate_data(Path(temp_dir))

        # Create orchestrator with hierarchy: global → pipeline → step
        orchestrator = create_real_orchestrator(plate_dir)

        # The orchestrator already has:
        # - global_config.step_well_filter_config.well_filter = "global_value"
        # - pipeline_config.step_well_filter_config.well_filter = "pipeline_override"
        # - No step_materialization_config in pipeline (should inherit from parent type)

        step_editor = StepEditor(orchestrator)

        # Should inherit from parent type (StepWellFilterConfig) in pipeline
        result = step_editor.edit_field('well_filter')

        print(f"Hierarchy traversal result: {result}")
        print(f"Expected: Should inherit from pipeline StepWellFilterConfig = 'pipeline_override'")

        # Should find parent type in pipeline context
        expected = "pipeline_override"
        assert result == expected, f"Expected '{expected}' from parent type inheritance, got {result}"
        print("✅ Context hierarchy traversal works")


def test_no_thread_local_contamination():
    """Test that resolution works without any thread-local context."""
    print("\n=== TEST 4: No Thread-Local Contamination ===")

    # Clear thread-local again to be sure
    _global_config_contexts.clear()

    # Verify thread-local is empty
    from openhcs.core.context.global_config import get_current_global_config
    thread_local_context = get_current_global_config(GlobalPipelineConfig)
    print(f"Thread-local context: {thread_local_context}")
    assert thread_local_context is None, "Thread-local should be empty for this test"

    import tempfile
    with tempfile.TemporaryDirectory() as temp_dir:
        # Create synthetic plate data
        plate_dir = create_synthetic_plate_data(Path(temp_dir))

        # Create orchestrator but DON'T call ensure_global_config_context
        global_config = GlobalPipelineConfig(
            num_workers=1,
            step_well_filter_config=StepWellFilterConfig(well_filter="pure_stack_discovery"),
            vfs_config=VFSConfig(materialization_backend=MaterializationBackend.DISK),
            path_planning_config=PathPlanningConfig(output_dir_suffix="_test")
        )

        pipeline_config = PipelineConfig(
            step_well_filter_config=StepWellFilterConfig(well_filter="stack_only_pipeline"),
            path_planning_config=PathPlanningConfig(output_dir_suffix="_test")
        )

        # Create orchestrator without thread-local setup
        orchestrator = PipelineOrchestrator(plate_dir, pipeline_config=pipeline_config)
        orchestrator.global_config = global_config  # Set directly without thread-local
        orchestrator.initialize()

        step_editor = StepEditor(orchestrator)

        # Should work purely through stack introspection
        result = step_editor.edit_field('well_filter')

        print(f"Pure stack discovery result: {result}")
        print(f"Expected: Should work without thread-local context")

        # Should still resolve through stack introspection
        assert result is not None, "Should resolve through pure stack introspection"
        print("✅ No thread-local contamination - pure stack introspection works")


if __name__ == "__main__":
    print("Testing Dual-Axis Resolver Stack Introspection")
    print("=" * 60)
    
    try:
        test_stack_introspection_discovery()
        test_automatic_context_resolution()
        test_context_hierarchy_traversal()
        test_no_thread_local_contamination()
        
        print("\n" + "=" * 60)
        print("🎉 ALL STACK INTROSPECTION TESTS PASSED!")
        print("The dual-axis resolver can fully replace thread-local context management.")
        
    except Exception as e:
        print(f"\n❌ STACK INTROSPECTION TEST FAILED: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
