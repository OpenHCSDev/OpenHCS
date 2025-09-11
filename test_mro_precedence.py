#!/usr/bin/env python3
"""
Test MRO-based precedence detection for multiple inheritance scenarios.
"""

import sys
import os
sys.path.insert(0, '/home/ts/code/projects/openhcs')

from dataclasses import fields, is_dataclass
import dataclasses
from openhcs.core.config import (
    StepMaterializationConfig, StepWellFilterConfig, WellFilterConfig, 
    PathPlanningConfig, StreamingConfig, NapariStreamingConfig, FijiStreamingConfig
)

def test_mro_precedence_detection():
    """Test MRO-based precedence detection for multiple inheritance."""
    print("=== Testing MRO Precedence Detection ===")
    
    test_cases = [
        {
            'name': 'StepMaterializationConfig',
            'target_class': StepMaterializationConfig,
            'field': 'well_filter',
            'expected_highest': StepWellFilterConfig,
            'description': 'Should inherit from StepWellFilterConfig (precedence over PathPlanningConfig)'
        },
        {
            'name': 'NapariStreamingConfig', 
            'target_class': NapariStreamingConfig,
            'field': 'well_filter',
            'expected_highest': StepWellFilterConfig,
            'description': 'Should inherit from StepWellFilterConfig (precedence over WellFilterConfig)'
        },
        {
            'name': 'FijiStreamingConfig',
            'target_class': FijiStreamingConfig, 
            'field': 'well_filter',
            'expected_highest': StepWellFilterConfig,
            'description': 'Should inherit from StepWellFilterConfig (precedence over WellFilterConfig)'
        }
    ]
    
    for test_case in test_cases:
        print(f"\n--- {test_case['name']} ---")
        print(f"Description: {test_case['description']}")
        
        target_class = test_case['target_class']
        field_name = test_case['field']
        expected = test_case['expected_highest']
        
        print(f"Target class: {target_class.__name__}")
        print(f"Field: {field_name}")
        print(f"MRO: {[cls.__name__ for cls in target_class.__mro__]}")
        
        # Test the precedence detection logic
        highest_precedence = find_highest_precedence_field_definer(target_class, field_name)
        
        print(f"Expected highest precedence: {expected.__name__}")
        print(f"Actual highest precedence: {highest_precedence.__name__ if highest_precedence else None}")
        
        if highest_precedence == expected:
            print("✅ CORRECT: Precedence detection working")
        else:
            print("❌ WRONG: Precedence detection failed")
            
        # Test inheritance scenarios
        print(f"\nInheritance scenarios for {target_class.__name__}:")
        
        # Should allow inheritance from highest precedence
        should_allow_highest = highest_precedence == expected
        print(f"  From {expected.__name__}: {'✅ ALLOW' if should_allow_highest else '❌ BLOCK'}")
        
        # Should block inheritance from lower precedence
        if expected == StepWellFilterConfig:
            should_allow_lower = highest_precedence == WellFilterConfig
            print(f"  From WellFilterConfig: {'❌ WRONG - ALLOW' if should_allow_lower else '✅ CORRECT - BLOCK'}")

def find_highest_precedence_field_definer(target_base_class: type, field_name: str) -> type:
    """Find the highest precedence parent class that defines a field using Python's MRO."""
    print(f"  Searching MRO for field '{field_name}':")
    
    # Use Python's MRO to find the first parent that defines this field with a concrete value
    for i, mro_class in enumerate(target_base_class.__mro__[1:], 1):  # Skip self (index 0)
        if is_dataclass(mro_class):
            mro_fields = {f.name: f for f in fields(mro_class)}
            if field_name in mro_fields:
                field_obj = mro_fields[field_name]
                field_default = field_obj.default if field_obj.default is not dataclasses.MISSING else None
                
                print(f"    {i}. {mro_class.__name__}.{field_name} = {field_default}")
                
                # Return the first parent with a concrete (non-None) value = highest precedence
                if field_default is not None:
                    print(f"    ✅ FIRST CONCRETE VALUE: {mro_class.__name__} (highest precedence)")
                    return mro_class
            else:
                print(f"    {i}. {mro_class.__name__} (no {field_name} field)")
    
    print(f"    ❌ No concrete value found in MRO")
    return None

def debug_field_values():
    """Debug field values in the inheritance hierarchy."""
    print("\n=== Field Values in Inheritance Hierarchy ===")
    
    classes = [
        StepMaterializationConfig, StepWellFilterConfig, WellFilterConfig, PathPlanningConfig,
        StreamingConfig, NapariStreamingConfig, FijiStreamingConfig
    ]
    
    for cls in classes:
        if is_dataclass(cls):
            cls_fields = {f.name: f for f in fields(cls)}
            if 'well_filter' in cls_fields:
                field_obj = cls_fields['well_filter']
                field_default = field_obj.default if field_obj.default is not dataclasses.MISSING else None
                print(f"{cls.__name__}.well_filter = {field_default}")

if __name__ == "__main__":
    debug_field_values()
    test_mro_precedence_detection()
    
    print(f"\n=== SUMMARY ===")
    print(f"✅ StepWellFilterConfig should be highest precedence for well_filter field")
    print(f"❌ WellFilterConfig should be blocked (lower precedence)")
    print(f"🎯 This ensures step configs inherit from step-level defaults, not global defaults")
