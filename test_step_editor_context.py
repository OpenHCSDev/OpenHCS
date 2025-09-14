#!/usr/bin/env python3

"""
Test to debug step editor context resolution.
"""

from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.lazy_config import PipelineConfig, LazyStepWellFilterConfig
from openhcs.core.context.global_config import set_global_config_for_editing
from openhcs.core.dual_axis_resolver_implementation import ContextDiscovery

class MockOrchestrator:
    """Mock orchestrator with PipelineConfig."""
    
    def __init__(self, pipeline_config):
        self.pipeline_config = pipeline_config

def test_step_editor_context():
    """Test step editor context discovery."""
    print("🧪 Testing step editor context discovery...")
    
    # Create GlobalPipelineConfig with concrete values
    global_config = GlobalPipelineConfig(
        num_workers=42,
        test_str_field="concrete_value"
    )
    
    # Set it in thread-local context
    set_global_config_for_editing(GlobalPipelineConfig, global_config)
    print(f"Set thread-local GlobalPipelineConfig: num_workers={global_config.num_workers}")
    
    # Create PipelineConfig with some values (simulating orchestrator state)
    pipeline_config = PipelineConfig(
        num_workers=10,  # Different from global config
        test_str_field="pipeline_value"
    )
    print(f"Created PipelineConfig: num_workers={pipeline_config.num_workers}")
    
    # Create mock orchestrator
    orchestrator = MockOrchestrator(pipeline_config)
    
    # Test context discovery for step config
    print(f"\n🔍 Testing context discovery for LazyStepWellFilterConfig...")
    
    # This simulates what happens in the step editor
    discovered_context = ContextDiscovery.discover_context(LazyStepWellFilterConfig)
    
    print(f"Discovered context: {type(discovered_context).__name__ if discovered_context else None}")
    
    if discovered_context:
        if hasattr(discovered_context, 'num_workers'):
            print(f"Context num_workers: {discovered_context.num_workers}")
        if hasattr(discovered_context, 'test_str_field'):
            print(f"Context test_str_field: {discovered_context.test_str_field}")
    
    # Expected behavior:
    # - Should find PipelineConfig (num_workers=10) from orchestrator
    # - Should NOT go directly to GlobalPipelineConfig (num_workers=42)
    
    if discovered_context and hasattr(discovered_context, 'num_workers'):
        if discovered_context.num_workers == 10:
            print("✅ CORRECT: Found PipelineConfig from orchestrator")
        elif discovered_context.num_workers == 42:
            print("❌ BUG: Skipped PipelineConfig, went directly to GlobalPipelineConfig")
        else:
            print(f"❓ UNEXPECTED: Found unexpected num_workers value: {discovered_context.num_workers}")
    else:
        print("❌ BUG: No context discovered")

if __name__ == "__main__":
    test_step_editor_context()
