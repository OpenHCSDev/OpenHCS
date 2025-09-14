#!/usr/bin/env python3
"""
Debug script to check MRO and inheritance blocking logic.
"""

import sys
import os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '.'))

from openhcs.core.config import StepMaterializationConfig, StepWellFilterConfig, PathPlanningConfig, WellFilterConfig
from openhcs.core.lazy_placeholder import _has_concrete_field_override

def debug_mro():
    """Debug the MRO and inheritance blocking."""
    print("=== MRO Analysis ===")
    print(f"StepMaterializationConfig MRO: {[cls.__name__ for cls in StepMaterializationConfig.__mro__]}")
    
    print("\n=== Field Override Analysis ===")
    for cls in StepMaterializationConfig.__mro__:
        if hasattr(cls, 'well_filter'):
            has_override = _has_concrete_field_override(cls, 'well_filter')
            class_attr = getattr(cls, 'well_filter', 'NOT_FOUND')
            print(f"{cls.__name__}.well_filter = {class_attr} (has_override: {has_override})")
    
    print("\n=== Expected Inheritance Behavior ===")
    print("StepMaterializationConfig.well_filter should inherit from:")
    print("1. StepWellFilterConfig.well_filter = 1 (BLOCKED - has concrete override)")
    print("2. PathPlanningConfig.well_filter = None (ALLOWED - no concrete override)")
    print("3. WellFilterConfig.well_filter = None (ALLOWED - no concrete override)")

if __name__ == "__main__":
    debug_mro()
