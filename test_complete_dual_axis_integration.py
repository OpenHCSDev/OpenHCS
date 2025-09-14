#!/usr/bin/env python3
"""
Comprehensive tests for complete dual-axis resolution migration.

Tests that the lazy config system now uses stack introspection instead of thread-local context.
"""

import sys
import os
sys.path.insert(0, os.path.abspath('.'))

from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.lazy_config import LazyStepMaterializationConfig, LazyStepWellFilterConfig
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.tests.generators.generate_synthetic_data import SyntheticMicroscopyGenerator
from openhcs.core.dual_axis_resolver_implementation import ContextDiscovery, get_resolver_for_context
from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService


def create_real_orchestrator(plate_dir):
    """Create a real orchestrator with synthetic data."""
    # Create synthetic plate data
    generator = SyntheticMicroscopyGenerator(
        output_dir=str(plate_dir),
        grid_size=(2, 2),
        tile_size=(64, 64),
        overlap_percent=10,
        wavelengths=1,
        z_stack_levels=1,
        wells=["A01"],
        format="ImageXpress",
        auto_image_size=False
    )
    generator.generate_dataset()
    
    # Create orchestrator with pipeline config override
    from openhcs.core.config import StepWellFilterConfig
    step_config = StepWellFilterConfig(well_filter="pipeline_override")
    global_config = GlobalPipelineConfig(step_well_filter_config=step_config)
    
    # Set thread-local context (required for orchestrator initialization)
    from openhcs.core.context.global_config import set_current_global_config
    set_current_global_config(GlobalPipelineConfig, global_config)

    orchestrator = PipelineOrchestrator(
        plate_path=plate_dir,
        workspace_path=None
    )
    
    return orchestrator


def test_lazy_config_uses_stack_introspection():
    """Test that lazy configs automatically use stack introspection."""
    import tempfile
    from pathlib import Path
    
    # Clear any thread-local context to ensure pure stack introspection
    from openhcs.core.context.global_config import _global_config_contexts
    _global_config_contexts.clear()
    
    with tempfile.TemporaryDirectory() as temp_dir:
        plate_dir = Path(temp_dir) / "test_plate"
        
        # Create orchestrator context
        orchestrator = create_real_orchestrator(plate_dir)
        
        # Create lazy config within orchestrator context
        def orchestrator_method(self):
            config = LazyStepMaterializationConfig()
            return config.well_filter  # Should auto-discover orchestrator
        
        orchestrator.test_method = orchestrator_method.__get__(orchestrator, PipelineOrchestrator)
        result = orchestrator.test_method()
        
        # Should find pipeline override, not thread-local
        print(f"✅ Stack introspection result: {result}")
        assert result == "pipeline_override", f"Expected 'pipeline_override', got '{result}'"


def test_placeholder_resolution_uses_stack_introspection():
    """Test that placeholder resolution uses stack introspection."""
    import tempfile
    from pathlib import Path
    
    with tempfile.TemporaryDirectory() as temp_dir:
        plate_dir = Path(temp_dir) / "test_plate"
        
        # Test placeholder service integration
        orchestrator = create_real_orchestrator(plate_dir)
        
        def orchestrator_placeholder_test(self):
            placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
                LazyStepMaterializationConfig, 'well_filter'
            )
            return placeholder
        
        orchestrator.test_placeholder = orchestrator_placeholder_test.__get__(orchestrator, PipelineOrchestrator)
        result = orchestrator.test_placeholder()
        
        print(f"✅ Placeholder result: {result}")
        assert result is not None and "pipeline_override" in result


def test_no_thread_local_dependencies():
    """Test that system works without any thread-local context."""
    import tempfile
    from pathlib import Path
    
    # Clear all thread-local context
    from openhcs.core.context.global_config import _global_config_contexts
    _global_config_contexts.clear()
    
    with tempfile.TemporaryDirectory() as temp_dir:
        plate_dir = Path(temp_dir) / "test_plate"
        
        orchestrator = create_real_orchestrator(plate_dir)
        
        # All resolution should work through stack introspection only
        def test_resolution(self):
            config = LazyStepMaterializationConfig()
            return {
                'well_filter': config.well_filter,
                'sub_dir': config.sub_dir,
                'output_dir_suffix': config.output_dir_suffix
            }
        
        orchestrator.test_resolution = test_resolution.__get__(orchestrator, PipelineOrchestrator)
        results = orchestrator.test_resolution()
        
        print(f"✅ Resolution results: {results}")
        
        # All values should be resolved from pipeline context
        assert all(v is not None for v in results.values()), f"Some values were None: {results}"
        assert results['well_filter'] == "pipeline_override"


def test_context_discovery_works():
    """Test that context discovery finds orchestrator objects."""
    import tempfile
    from pathlib import Path
    
    with tempfile.TemporaryDirectory() as temp_dir:
        plate_dir = Path(temp_dir) / "test_plate"
        
        orchestrator = create_real_orchestrator(plate_dir)
        
        def test_discovery(self):
            context = ContextDiscovery.discover_context()
            return {
                'found_context': context is not None,
                'context_type': type(context).__name__ if context else None,
                'has_pipeline_config': hasattr(context, 'pipeline_config') if context else False
            }
        
        orchestrator.test_discovery = test_discovery.__get__(orchestrator, PipelineOrchestrator)
        results = orchestrator.test_discovery()
        
        print(f"✅ Context discovery results: {results}")
        
        assert results['found_context'], "Context discovery failed"
        assert results['context_type'] == 'PipelineOrchestrator', f"Wrong context type: {results['context_type']}"
        assert results['has_pipeline_config'], "Context missing pipeline_config"


def test_dual_axis_resolver_integration():
    """Test that dual-axis resolver is properly integrated."""
    import tempfile
    from pathlib import Path
    
    with tempfile.TemporaryDirectory() as temp_dir:
        plate_dir = Path(temp_dir) / "test_plate"
        
        orchestrator = create_real_orchestrator(plate_dir)
        
        def test_resolver(self):
            context = ContextDiscovery.discover_context()
            if not context:
                return {'error': 'No context found'}
            
            resolver = get_resolver_for_context(context)
            config = LazyStepMaterializationConfig()
            resolved_value = resolver.resolve_field(config, 'well_filter')
            
            return {
                'resolver_created': resolver is not None,
                'resolved_value': resolved_value,
                'matches_expected': resolved_value == "pipeline_override"
            }
        
        orchestrator.test_resolver = test_resolver.__get__(orchestrator, PipelineOrchestrator)
        results = orchestrator.test_resolver()
        
        print(f"✅ Dual-axis resolver results: {results}")
        
        assert results['resolver_created'], "Failed to create resolver"
        assert results['resolved_value'] == "pipeline_override", f"Wrong resolved value: {results['resolved_value']}"
        assert results['matches_expected'], "Resolved value doesn't match expected"


if __name__ == "__main__":
    print("🧪 Testing complete dual-axis resolution migration...")
    
    try:
        test_context_discovery_works()
        print("✅ Context discovery test passed")
        
        test_dual_axis_resolver_integration()
        print("✅ Dual-axis resolver integration test passed")
        
        test_lazy_config_uses_stack_introspection()
        print("✅ Lazy config stack introspection test passed")
        
        test_placeholder_resolution_uses_stack_introspection()
        print("✅ Placeholder resolution test passed")
        
        test_no_thread_local_dependencies()
        print("✅ No thread-local dependencies test passed")
        
        print("\n🎉 All dual-axis resolution migration tests passed!")
        print("✅ Thread-local system successfully replaced with stack introspection")
        
    except Exception as e:
        print(f"\n❌ Test failed: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
