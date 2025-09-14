#!/usr/bin/env python3

"""
Debug field path detection for lazy vs non-lazy type matching.
"""

from openhcs.core.config import PipelineConfig, StepWellFilterConfig, StepMaterializationConfig
from openhcs.core.lazy_config import LazyStepWellFilterConfig, LazyStepMaterializationConfig
from openhcs.core.field_path_detection import FieldPathDetector
from openhcs.core.lazy_config import get_base_type_for_lazy
from dataclasses import fields

def debug_field_path_detection():
    """Debug why field path detection fails for lazy types."""
    print("🔍 DEBUGGING FIELD PATH DETECTION")
    print("=" * 50)
    
    # Test case: Looking for StepWellFilterConfig in PipelineConfig
    target_type = StepWellFilterConfig
    context_type = PipelineConfig
    
    print(f"Target type: {target_type.__name__}")
    print(f"Context type: {context_type.__name__}")
    print()
    
    # Show what fields PipelineConfig actually has
    print("📋 PipelineConfig fields:")
    for field in fields(context_type):
        print(f"  {field.name}: {field.type}")
        if hasattr(field.type, '__name__'):
            base_type = get_base_type_for_lazy(field.type)
            if base_type:
                print(f"    -> Base type: {base_type.__name__}")
    print()
    
    # Test FieldPathDetector.find_all_field_paths_unified
    print("🔍 FieldPathDetector.find_all_field_paths_unified results:")
    field_paths = FieldPathDetector.find_all_field_paths_unified(context_type, target_type)
    print(f"  Found paths: {field_paths}")
    print()
    
    # Test individual components
    print("🔍 Individual component results:")
    
    # Test inheritance-based paths
    inheritance_paths = FieldPathDetector.find_all_field_paths_for_type(context_type, target_type)
    print(f"  Inheritance paths: {inheritance_paths}")
    
    # Test composition-based paths
    from openhcs.core.composition_detection import find_all_composition_paths_for_type
    composition_paths = find_all_composition_paths_for_type(context_type, target_type)
    print(f"  Composition paths: {composition_paths}")
    print()
    
    # Test manual lazy type detection
    print("🔍 Manual lazy type detection:")
    for field in fields(context_type):
        field_type = field.type
        base_type = get_base_type_for_lazy(field_type)
        if base_type == target_type:
            print(f"  ✅ Found lazy field: {field.name} ({field_type.__name__} -> {base_type.__name__})")
        else:
            print(f"  ❌ No match: {field.name} ({field_type.__name__} -> {base_type})")
    print()
    
    # Test with LazyStepMaterializationConfig too
    print("🔍 Testing StepMaterializationConfig:")
    target_type2 = StepMaterializationConfig
    field_paths2 = FieldPathDetector.find_all_field_paths_unified(context_type, target_type2)
    print(f"  Found paths: {field_paths2}")
    
    for field in fields(context_type):
        field_type = field.type
        base_type = get_base_type_for_lazy(field_type)
        if base_type == target_type2:
            print(f"  ✅ Found lazy field: {field.name} ({field_type.__name__} -> {base_type.__name__})")

if __name__ == "__main__":
    debug_field_path_detection()
