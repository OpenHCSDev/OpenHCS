#!/usr/bin/env python3

"""
Test to debug MRO relationships for step config inheritance.
"""

from openhcs.core.config import GlobalPipelineConfig, WellFilterConfig
from openhcs.core.lazy_config import PipelineConfig, LazyStepWellFilterConfig

def test_mro_relationships():
    """Test MRO relationships for step config inheritance."""
    print("🧪 Testing MRO relationships...")
    
    # Check LazyStepWellFilterConfig MRO
    print(f"\nLazyStepWellFilterConfig MRO:")
    for i, cls in enumerate(LazyStepWellFilterConfig.__mro__):
        print(f"  {i}: {cls.__name__}")
    
    # Check what parent types should be valid for LazyStepWellFilterConfig
    target_type = LazyStepWellFilterConfig
    parent_types = target_type.__mro__[1:]  # Skip the target type itself
    
    print(f"\nParent types for {target_type.__name__}:")
    for cls in parent_types:
        print(f"  - {cls.__name__}")
    
    # Check if PipelineConfig is in the parent types
    print(f"\nIs PipelineConfig a parent of LazyStepWellFilterConfig? {PipelineConfig in parent_types}")
    print(f"Is GlobalPipelineConfig a parent of LazyStepWellFilterConfig? {GlobalPipelineConfig in parent_types}")
    print(f"Is WellFilterConfig a parent of LazyStepWellFilterConfig? {WellFilterConfig in parent_types}")
    
    # Test the context provider logic
    print(f"\n🔍 Testing context provider logic...")
    
    # Simulate what _is_context_provider does
    def test_context_provider(obj, target_type):
        """Test context provider logic."""
        print(f"\nTesting {type(obj).__name__} as context provider for {target_type.__name__}")
        
        # Check if object has dataclass attributes
        for attr_name in dir(obj):
            if attr_name.startswith('_'):
                continue
            try:
                attr_value = getattr(obj, attr_name)
                if hasattr(attr_value, '__dataclass_fields__'):
                    attr_type = type(attr_value)
                    print(f"  Found dataclass attribute: {attr_name}: {attr_type.__name__}")
                    
                    # Check if this dataclass is relevant to target_type
                    if hasattr(target_type, '__mro__'):
                        parent_types = target_type.__mro__[1:]  # Skip the target type itself
                        if attr_type in parent_types:
                            print(f"    ✅ {attr_type.__name__} is PARENT of {target_type.__name__}")
                            return True
                        else:
                            print(f"    ❌ {attr_type.__name__} is NOT in parent types of {target_type.__name__}")
            except:
                continue
        return False
    
    # Test with PipelineConfig
    pipeline_config = PipelineConfig()
    
    class MockOrchestrator:
        def __init__(self, pipeline_config):
            self.pipeline_config = pipeline_config
    
    orchestrator = MockOrchestrator(pipeline_config)
    
    result = test_context_provider(orchestrator, LazyStepWellFilterConfig)
    print(f"\nResult: MockOrchestrator is context provider for LazyStepWellFilterConfig: {result}")

if __name__ == "__main__":
    test_mro_relationships()
