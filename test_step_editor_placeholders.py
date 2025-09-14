#!/usr/bin/env python3

"""
Test step editor placeholder resolution vs pipeline config placeholder resolution.
"""

from openhcs.core.config import GlobalPipelineConfig, StepMaterializationConfig, StepWellFilterConfig
from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
from openhcs.core.context.global_config import set_current_global_config
from openhcs.core.lazy_config import LazyDataclassFactory

def test_pipeline_config_placeholders():
    """Test how pipeline config placeholders work (this should work correctly)."""
    print("🧪 Testing pipeline config placeholders...")
    
    # Set up thread-local context
    context_global_config = GlobalPipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter=5),  # Context value: 5
        step_materialization_config=StepMaterializationConfig(well_filter=None)  # Should inherit
    )
    
    set_current_global_config(GlobalPipelineConfig, context_global_config)
    
    # Create lazy pipeline config
    LazyPipelineConfig = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
        base_class=GlobalPipelineConfig,
        global_config_type=GlobalPipelineConfig,
        lazy_class_name="LazyPipelineConfig"
    )
    
    # Test placeholder for pipeline config editing
    placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        LazyPipelineConfig, "step_materialization_config", placeholder_prefix="Global default"
    )
    print(f"  Pipeline config placeholder: '{placeholder}'")
    
    # Test nested field placeholder
    lazy_step_mat = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
        base_class=StepMaterializationConfig,
        global_config_type=GlobalPipelineConfig,
        lazy_class_name="LazyStepMaterializationConfig"
    )
    nested_placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        lazy_step_mat, "well_filter", placeholder_prefix="Pipeline default"
    )
    print(f"  Nested step materialization placeholder: '{nested_placeholder}'")

def test_step_editor_placeholders():
    """Test how step editor placeholders work with different orchestrator context."""
    print(f"\n🧪 Testing step editor placeholders...")

    # Set up thread-local context with one value
    thread_local_global_config = GlobalPipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter=100),  # Thread-local value: 100
        step_materialization_config=StepMaterializationConfig(well_filter=None)
    )

    set_current_global_config(GlobalPipelineConfig, thread_local_global_config)

    # Create orchestrator with DIFFERENT pipeline config values
    class MockOrchestrator:
        def __init__(self, pipeline_config):
            self.pipeline_config = pipeline_config
            self.plate_path = "/fake/plate/path"

    # Create pipeline config for orchestrator with DIFFERENT values
    LazyPipelineConfig = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
        base_class=GlobalPipelineConfig,
        global_config_type=GlobalPipelineConfig,
        lazy_class_name="LazyPipelineConfig"
    )

    # Create orchestrator pipeline config with explicit different values
    orchestrator_pipeline_config = LazyPipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter=200)  # Orchestrator value: 200
    )

    orchestrator = MockOrchestrator(orchestrator_pipeline_config)

    print(f"  Thread-local context well_filter: {thread_local_global_config.step_well_filter_config.well_filter}")
    print(f"  Orchestrator pipeline well_filter: {orchestrator_pipeline_config.step_well_filter_config.well_filter}")

    # Simulate step editor creating lazy step configs
    def simulate_step_editor_placeholder_resolution():
        """Simulate what happens in step editor when getting placeholders."""
        # This simulates the step editor context where orchestrator is in the call stack

        # Create lazy step config (like step editor does)
        lazy_step_mat = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
            base_class=StepMaterializationConfig,
            global_config_type=GlobalPipelineConfig,
            lazy_class_name="LazyStepMaterializationConfig"
        )

        # Get placeholder (this should find orchestrator in call stack)
        placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
            lazy_step_mat, "well_filter", placeholder_prefix="Pipeline default"
        )
        return placeholder

    # Call from within orchestrator context
    result = simulate_step_editor_placeholder_resolution()
    print(f"  Step editor placeholder: '{result}'")

    # Expected: "Pipeline default: 200" (from orchestrator pipeline config)
    # If we get: "Pipeline default: 100" (thread-local), then it's not using orchestrator context

    if result == "Pipeline default: 200":
        print("✅ SUCCESS: Step editor using orchestrator context!")
    elif result == "Pipeline default: 100":
        print("❌ FAILURE: Step editor using thread-local instead of orchestrator context")
    elif result == "Pipeline default: 1":
        print("❌ FAILURE: Step editor falling back to static defaults")
    else:
        print(f"❓ UNEXPECTED: Got '{result}'")

def test_context_discovery_differences():
    """Test the differences in context discovery between pipeline and step editors."""
    print(f"\n🧪 Testing context discovery differences...")
    
    # Set up context
    context_global_config = GlobalPipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter=9)
    )
    set_current_global_config(GlobalPipelineConfig, context_global_config)
    
    # Test 1: Direct thread-local context (pipeline config style)
    print("Test 1: Direct thread-local context discovery")
    from openhcs.core.dual_axis_resolver_implementation import ContextDiscovery
    
    thread_local_context = ContextDiscovery.discover_context()
    print(f"  Thread-local context found: {thread_local_context is not None}")
    if thread_local_context:
        print(f"  Context type: {type(thread_local_context).__name__}")
    
    # Test 2: Orchestrator context (step editor style)
    print("Test 2: Orchestrator context discovery")
    
    class MockOrchestrator:
        def __init__(self):
            LazyPipelineConfig = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
                base_class=GlobalPipelineConfig,
                global_config_type=GlobalPipelineConfig,
                lazy_class_name="LazyPipelineConfig"
            )
            self.pipeline_config = LazyPipelineConfig()
            self.plate_path = "/fake/plate"
    
    def test_with_orchestrator():
        orchestrator = MockOrchestrator()  # This puts orchestrator in call stack
        
        # Try to discover context
        discovered_context = ContextDiscovery.discover_context()
        print(f"  Orchestrator context found: {discovered_context is not None}")
        if discovered_context:
            print(f"  Context type: {type(discovered_context).__name__}")
            print(f"  Is orchestrator: {hasattr(discovered_context, 'pipeline_config') and hasattr(discovered_context, 'plate_path')}")
        
        return discovered_context
    
    orchestrator_context = test_with_orchestrator()
    
    # Test 3: Compare placeholder resolution with different contexts
    print("Test 3: Placeholder resolution comparison")
    
    lazy_step_mat = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
        base_class=StepMaterializationConfig,
        global_config_type=GlobalPipelineConfig,
        lazy_class_name="LazyStepMaterializationConfig"
    )
    
    # Direct resolution (should use thread-local)
    direct_placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        lazy_step_mat, "well_filter", placeholder_prefix="Direct"
    )
    print(f"  Direct resolution: '{direct_placeholder}'")
    
    # Orchestrator resolution
    def test_orchestrator_resolution():
        orchestrator = MockOrchestrator()
        lazy_step_mat_local = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
            base_class=StepMaterializationConfig,
            global_config_type=GlobalPipelineConfig,
            lazy_class_name="LazyStepMaterializationConfig"
        )
        placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
            lazy_step_mat_local, "well_filter", placeholder_prefix="Orchestrator"
        )
        return placeholder
    
    orchestrator_placeholder = test_orchestrator_resolution()
    print(f"  Orchestrator resolution: '{orchestrator_placeholder}'")

if __name__ == "__main__":
    test_pipeline_config_placeholders()
    test_step_editor_placeholders()
    test_context_discovery_differences()
