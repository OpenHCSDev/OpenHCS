#!/usr/bin/env python3

"""
Debug recursive resolver field resolution for lazy types.
"""

from openhcs.core.config import PipelineConfig, StepWellFilterConfig, GlobalPipelineConfig
from openhcs.core.lazy_config import LazyStepWellFilterConfig
from openhcs.core.dual_axis_resolver_recursive import RecursiveContextualResolver
from openhcs.core.context.global_config import set_current_global_config

def debug_recursive_resolver():
    """Debug why recursive resolver fails for nested configs."""
    print("🔍 DEBUGGING RECURSIVE RESOLVER")
    print("=" * 50)
    
    # Set up context similar to step editor scenario
    global_config = GlobalPipelineConfig(
        step_well_filter_config=StepWellFilterConfig(well_filter="5")  # Concrete value
    )
    set_current_global_config(GlobalPipelineConfig, global_config)
    
    # Create pipeline config (like in orchestrator)
    pipeline_config = PipelineConfig(
        step_well_filter_config=LazyStepWellFilterConfig(well_filter="3")  # Concrete value
    )
    
    print(f"Global config step_well_filter_config.well_filter: {global_config.step_well_filter_config.well_filter}")
    print(f"Pipeline config step_well_filter_config.well_filter: {pipeline_config.step_well_filter_config.well_filter}")
    print()
    
    # Create resolver with pipeline config as context
    resolver = RecursiveContextualResolver()
    
    # Test resolving StepWellFilterConfig.well_filter with pipeline context
    target_type = StepWellFilterConfig
    field_name = "well_filter"
    context_hierarchy = [pipeline_config, global_config]
    
    print(f"🔍 Testing resolution of {target_type.__name__}.{field_name}")
    print(f"Context hierarchy: {[type(c).__name__ for c in context_hierarchy]}")
    print()
    
    # Test _get_concrete_value_at_level for each context level
    for i, context in enumerate(context_hierarchy):
        print(f"🔍 Level {i}: {type(context).__name__}")
        try:
            value = resolver._get_concrete_value_at_level(context, target_type, field_name)
            print(f"  Result: {value}")
        except Exception as e:
            print(f"  Error: {e}")
            import traceback
            traceback.print_exc()
        print()
    
    # Test full recursive resolution
    print("🔍 Full recursive resolution:")
    try:
        result = resolver._resolve_field_recursive(target_type, field_name, context_hierarchy)
        print(f"  Final result: {result}")
    except Exception as e:
        print(f"  Error: {e}")
        import traceback
        traceback.print_exc()
    print()
    
    # Test with lazy instance (like step editor would do)
    print("🔍 Testing with lazy instance:")
    lazy_instance = LazyStepWellFilterConfig()
    try:
        # This should use the recursive resolver internally
        resolved_value = getattr(lazy_instance, field_name)
        print(f"  Lazy instance resolution: {resolved_value}")
    except Exception as e:
        print(f"  Error: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    debug_recursive_resolver()
