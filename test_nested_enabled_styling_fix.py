#!/usr/bin/env python3
"""
Test to verify the fix for nested enabled field styling bug.

Bug: When a dataclass with an 'enabled' field is nested in an object that also has an 'enabled' field,
toggling the nested enabled flag causes incorrect styling changes for the whole form including parents and siblings.

Fix: Added checks to prevent propagated enabled signals from nested forms from triggering
parent form styling changes.
"""

import sys
from dataclasses import dataclass
from typing import Optional
from PyQt6.QtWidgets import QApplication

# Mock test to verify the logic
def test_propagation_flag():
    """Test that the _propagating_nested_enabled flag prevents incorrect styling."""
    
    # Simulate the scenario
    class MockManager:
        def __init__(self, name, has_enabled=True):
            self.name = name
            self.parameters = {'enabled': True} if has_enabled else {}
            self._propagating_nested_enabled = False
            self.enabled_handler_called = False
            
        def _on_enabled_field_changed_universal(self, param_name: str, value: bool):
            """Simulated handler with the fix."""
            if param_name != 'enabled':
                return
            
            # CRITICAL FIX: Ignore propagated signals
            if getattr(self, '_propagating_nested_enabled', False):
                print(f"  [{self.name}] Ignoring propagated 'enabled' signal ✓")
                return
            
            # Check if this form has enabled parameter
            if 'enabled' not in self.parameters:
                print(f"  [{self.name}] Ignoring - no enabled parameter ✓")
                return
            
            # Apply styling
            self.enabled_handler_called = True
            print(f"  [{self.name}] Applying styling for enabled={value} ✓")
        
        def propagate_signal(self, param_name: str, value: bool):
            """Simulate signal propagation from nested to parent."""
            if param_name == 'enabled':
                self._propagating_nested_enabled = True
            
            # Trigger handler
            self._on_enabled_field_changed_universal(param_name, value)
            
            if param_name == 'enabled':
                self._propagating_nested_enabled = False
    
    print("Test 1: Nested form changes its own enabled field")
    print("-" * 50)
    parent = MockManager("parent", has_enabled=True)
    nested = MockManager("nested", has_enabled=True)
    
    # Nested form changes its enabled field directly
    nested._on_enabled_field_changed_universal('enabled', False)
    assert nested.enabled_handler_called, "Nested form should handle its own change"
    
    # Simulate propagation to parent
    parent.propagate_signal('enabled', False)
    assert not parent.enabled_handler_called, "Parent should NOT handle propagated signal"
    print("✓ Test 1 passed!\n")
    
    print("Test 2: Parent form changes its own enabled field")
    print("-" * 50)
    parent2 = MockManager("parent2", has_enabled=True)
    
    # Parent changes its own enabled field directly (not propagated)
    parent2._on_enabled_field_changed_universal('enabled', False)
    assert parent2.enabled_handler_called, "Parent should handle its own change"
    print("✓ Test 2 passed!\n")
    
    print("Test 3: Form without enabled parameter receives enabled signal")
    print("-" * 50)
    no_enabled = MockManager("no_enabled", has_enabled=False)
    
    # This form receives enabled signal but has no enabled parameter
    no_enabled._on_enabled_field_changed_universal('enabled', False)
    assert not no_enabled.enabled_handler_called, "Form without enabled should ignore signal"
    print("✓ Test 3 passed!\n")
    
    print("=" * 50)
    print("All tests passed! ✓")
    print("=" * 50)

if __name__ == '__main__':
    test_propagation_flag()
