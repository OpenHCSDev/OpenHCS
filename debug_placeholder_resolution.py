#!/usr/bin/env python3

"""
Debug placeholder resolution to see why it's showing global config instead of pipeline config.
"""

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig, StepWellFilterConfig
from openhcs.core.context.global_config import set_global_config_for_editing, get_current_global_config
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
from openhcs.core.dual_axis_resolver_recursive import ContextDiscovery, get_recursive_resolver
from pathlib import Path

def debug_placeholder_resolution():
    """Debug why placeholders show global config instead of pipeline config."""
    print("🔍 DEBUGGING PLACEHOLDER RESOLUTION")
    print("=" * 50)
    
    # Set up global config with well_filter=5
    global_config = GlobalPipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter=5)
    )
    set_global_config_for_editing(GlobalPipelineConfig, global_config)
    print(f"✅ Global config set: step_well_filter_config.well_filter = {global_config.step_well_filter_config.well_filter}")
    
    # Create pipeline config with well_filter=9
    pipeline_config = PipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter=9)
    )
    print(f"✅ Pipeline config created: step_well_filter_config.well_filter = {pipeline_config.step_well_filter_config.well_filter}")
    
    # Create orchestrator with pipeline config
    import tempfile
    import os
    temp_dir = tempfile.mkdtemp()
    os.makedirs(temp_dir, exist_ok=True)

    orchestrator = PipelineOrchestrator(
        plate_path=Path(temp_dir),
        pipeline_config=pipeline_config
    )
    print(f"✅ Orchestrator created with pipeline config")
    print(f"   orchestrator.pipeline_config.step_well_filter_config.well_filter = {orchestrator.pipeline_config.step_well_filter_config.well_filter}")
    
    # Test context discovery
    print("\n🔍 Testing context discovery:")
    context = ContextDiscovery.discover_context(StepWellFilterConfig)
    print(f"   Discovered context: {context} (type: {type(context).__name__})")
    
    # Test context discovery with orchestrator in call stack
    print("\n🔍 Testing context discovery with orchestrator context:")
    with orchestrator.config_context(for_serialization=True):
        # Debug: Check if frame injection worked
        import inspect
        frame = inspect.currentframe()
        print(f"   Current frame locals: {list(frame.f_locals.keys())}")
        for key, value in frame.f_locals.items():
            if 'context' in key:
                print(f"     {key}: {type(value).__name__}")

        # Debug: Check parent frames too
        parent_frame = frame.f_back
        frame_count = 0
        while parent_frame and frame_count < 5:
            frame_count += 1
            print(f"   Frame {frame_count} locals: {list(parent_frame.f_locals.keys())}")
            for key, value in parent_frame.f_locals.items():
                if 'context' in key:
                    print(f"     {key}: {type(value).__name__}")
            parent_frame = parent_frame.f_back

        context_with_orchestrator = ContextDiscovery.discover_context(StepWellFilterConfig)
        print(f"   Discovered context: {context_with_orchestrator} (type: {type(context_with_orchestrator).__name__})")

        # Test resolver directly
        print("\n🔍 Testing resolver directly:")
        resolver = get_recursive_resolver()
        temp_instance = StepWellFilterConfig()
        resolved_value = resolver.resolve_field(temp_instance, 'well_filter')
        print(f"   Resolved well_filter = {resolved_value}")
    
    # Test placeholder service without orchestrator
    print("\n🔍 Testing placeholder service WITHOUT orchestrator:")
    placeholder_without = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        StepWellFilterConfig, 'well_filter'
    )
    print(f"   Placeholder: {placeholder_without}")
    
    # Test placeholder service with orchestrator
    print("\n🔍 Testing placeholder service WITH orchestrator:")
    placeholder_with = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        StepWellFilterConfig, 'well_filter', orchestrator=orchestrator
    )
    print(f"   Placeholder: {placeholder_with}")

    # Test what happens inside the orchestrator context
    print("\n🔍 Testing inside orchestrator.config_context:")
    with orchestrator.config_context(for_serialization=True):
        print("   Inside orchestrator context:")

        # Check if the frame injection worked
        import inspect
        frame = inspect.currentframe()
        print(f"   Current frame locals: {list(frame.f_locals.keys())}")

        # Walk up the call stack to see all frames
        current_frame = frame
        frame_count = 0
        while current_frame and frame_count < 5:
            print(f"   Frame {frame_count} locals: {list(current_frame.f_locals.keys())}")
            for var_name in current_frame.f_locals.keys():
                if '__orchestrator_context__' in var_name:
                    print(f"     Found injected context: {var_name}")
            current_frame = current_frame.f_back
            frame_count += 1

        # Check context discovery
        context_inside = ContextDiscovery.discover_context(StepWellFilterConfig)
        print(f"   Discovered context: {type(context_inside).__name__}")

        # Test resolver directly
        resolver = get_recursive_resolver()
        temp_instance = StepWellFilterConfig()
        resolved_value_inside = resolver.resolve_field(temp_instance, 'well_filter')
        print(f"   Resolved well_filter = {resolved_value_inside}")

        del frame
    
    # Test what the compiler actually produces
    print("\n🔍 Testing what the compiler produces:")
    try:
        from openhcs.core.pipeline.compiler import PipelineCompiler
        from openhcs.core.steps.abstract import AbstractStep

        # Create a simple step to test compilation
        class TestStep(AbstractStep):
            def __init__(self):
                super().__init__()

            def process(self, image, context):
                return image

        test_step = TestStep()
        pipeline_definition = [test_step]

        # Compile the pipeline
        compiled_contexts = PipelineCompiler.compile_pipelines(
            orchestrator, pipeline_definition, axis_filter=["test_axis"]
        )

        print(f"   Compiled contexts: {list(compiled_contexts.keys())}")
        if compiled_contexts:
            context = list(compiled_contexts.values())[0]
            print(f"   ProcessingContext type: {type(context).__name__}")
            print(f"   ProcessingContext.global_config type: {type(context.global_config).__name__}")

            # Check the resolved values in the compiled context
            if hasattr(context.global_config, 'step_well_filter_config'):
                step_config = context.global_config.step_well_filter_config
                print(f"   Compiled step_well_filter_config.well_filter = {step_config.well_filter}")
                print(f"   Compiled step_well_filter_config type: {type(step_config).__name__}")
            else:
                print("   No step_well_filter_config in compiled context")

    except Exception as e:
        print(f"   Compilation failed: {e}")

    print("\n" + "=" * 50)
    print("EXPECTED: Pipeline default: 9")
    print("ACTUAL  : " + str(placeholder_with))
    print("MATCH   : " + ("✅ YES" if "9" in str(placeholder_with) else "❌ NO"))

if __name__ == "__main__":
    debug_placeholder_resolution()
