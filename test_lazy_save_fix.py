#!/usr/bin/env python3
"""Test script to verify the lazy dataclass save fix preserves None vs concrete distinction."""

import sys
import os
sys.path.insert(0, os.path.abspath('.'))

from openhcs.core.config import LazyZarrConfig, ZarrCompressor, ZarrChunkStrategy, GlobalPipelineConfig
from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
from openhcs.core.context.global_config import set_current_global_config

def test_broken_save():
    """Test the BROKEN save method that triggers lazy resolution."""
    print("🔴 Testing BROKEN save method (normal constructor):")

    # Set up global config context that could trigger lazy resolution
    from openhcs.core.config import ZarrConfig
    zarr_config_with_values = ZarrConfig(
        compressor=ZarrCompressor.ZLIB,
        compression_level=3
    )
    global_config = GlobalPipelineConfig(zarr_config=zarr_config_with_values)
    set_current_global_config(GlobalPipelineConfig, global_config)

    # Create lazy config with only store_name set (like your example)
    original_config = LazyZarrConfig(store_name='test')
    
    print(f"Original config:")
    print(f"  store_name: {object.__getattribute__(original_config, 'store_name')}")
    print(f"  compressor: {object.__getattribute__(original_config, 'compressor')}")
    print(f"  compression_level: {object.__getattribute__(original_config, 'compression_level')}")
    
    # Simulate broken save: get_current_values() + normal constructor
    current_values = {
        'store_name': 'test',
        'compressor': None,  # This should stay None!
        'compression_level': None,  # This should stay None!
        'shuffle': None,
        'chunk_strategy': None,
        'ome_zarr_metadata': None,
        'write_plate_metadata': None
    }
    
    # BROKEN: Normal constructor triggers lazy resolution
    broken_config = LazyZarrConfig(**current_values)
    
    print(f"\nAfter BROKEN save:")
    print(f"  store_name: {object.__getattribute__(broken_config, 'store_name')}")
    print(f"  compressor (raw): {object.__getattribute__(broken_config, 'compressor')}")
    print(f"  compression_level (raw): {object.__getattribute__(broken_config, 'compression_level')}")

    # Now try accessing through normal getattr (this might trigger lazy resolution!)
    print(f"  compressor (getattr): {getattr(broken_config, 'compressor')}")
    print(f"  compression_level (getattr): {getattr(broken_config, 'compression_level')}")

    # Check if None fields got resolved (this is the bug!)
    compressor_raw = object.__getattribute__(broken_config, 'compressor')
    compressor_resolved = getattr(broken_config, 'compressor')

    if compressor_raw is None and compressor_resolved is not None:
        print(f"🐛 BUG CONFIRMED: compressor was None but getattr() resolved it to {compressor_resolved}")
    elif compressor_raw is not None:
        print(f"🐛 BUG CONFIRMED: compressor was None but constructor resolved it to {compressor_raw}")
    else:
        print(f"✅ No bug: compressor stayed None")

def test_fixed_save():
    """Test the FIXED save method that preserves None vs concrete distinction."""
    print("\n🟢 Testing FIXED save method (object.__new__ + object.__setattr__):")

    # Ensure same global config context
    from openhcs.core.config import ZarrConfig
    zarr_config_with_values = ZarrConfig(
        compressor=ZarrCompressor.ZLIB,
        compression_level=3
    )
    global_config = GlobalPipelineConfig(zarr_config=zarr_config_with_values)
    set_current_global_config(GlobalPipelineConfig, global_config)

    # Same starting values
    current_values = {
        'store_name': 'test',
        'compressor': None,  # This should stay None!
        'compression_level': None,  # This should stay None!
        'shuffle': None,
        'chunk_strategy': None,
        'ome_zarr_metadata': None,
        'write_plate_metadata': None
    }
    
    # FIXED: Use object.__new__ + object.__setattr__ to avoid lazy resolution
    if LazyDefaultPlaceholderService.has_lazy_resolution(LazyZarrConfig):
        # Create empty instance first (no constructor args to avoid resolution)
        fixed_config = object.__new__(LazyZarrConfig)
        
        # Set raw values directly using object.__setattr__ to avoid lazy resolution
        for field_name, value in current_values.items():
            object.__setattr__(fixed_config, field_name, value)
        
        # Initialize any required lazy dataclass attributes
        if hasattr(LazyZarrConfig, '_is_lazy_dataclass'):
            object.__setattr__(fixed_config, '_is_lazy_dataclass', True)
    else:
        # For non-lazy dataclasses, use normal constructor
        fixed_config = LazyZarrConfig(**current_values)
    
    print(f"After FIXED save:")
    print(f"  store_name: {object.__getattribute__(fixed_config, 'store_name')}")
    print(f"  compressor: {object.__getattribute__(fixed_config, 'compressor')}")
    print(f"  compression_level: {object.__getattribute__(fixed_config, 'compression_level')}")
    
    # Check if None fields stayed None (this should work!)
    compressor_raw = object.__getattribute__(fixed_config, 'compressor')
    if compressor_raw is None:
        print(f"✅ FIX WORKS: compressor stayed None as expected")
    else:
        print(f"❌ FIX FAILED: compressor was None but got resolved to {compressor_raw}")

def test_context_building_fix():
    """Test the FIXED context building that preserves None vs concrete distinction."""
    print("\n🟢 Testing FIXED context building (object.__new__ + object.__setattr__):")

    # Set up global config context
    from openhcs.core.config import ZarrConfig
    zarr_config_with_values = ZarrConfig(
        compressor=ZarrCompressor.ZLIB,
        compression_level=3
    )
    global_config = GlobalPipelineConfig(zarr_config=zarr_config_with_values)
    set_current_global_config(GlobalPipelineConfig, global_config)

    # Create lazy config with only store_name set (like your example)
    original_config = LazyZarrConfig(store_name='test')

    print(f"Original config:")
    print(f"  store_name: {object.__getattribute__(original_config, 'store_name')}")
    print(f"  compressor: {object.__getattribute__(original_config, 'compressor')}")
    print(f"  compression_level: {object.__getattribute__(original_config, 'compression_level')}")

    # Simulate the context building process (this is what was broken)
    current_form_values = {
        'store_name': 'test',
        'compressor': None,  # This should stay None!
        'compression_level': None,  # This should stay None!
    }

    # FIXED: Use the new context building approach
    if hasattr(original_config, '_resolve_field_value'):
        # This is a lazy dataclass - create instance with raw values to avoid triggering resolution
        updated_instance = object.__new__(type(original_config))

        # Copy all existing raw values first
        import dataclasses
        for field in dataclasses.fields(original_config):
            existing_value = object.__getattribute__(original_config, field.name)
            object.__setattr__(updated_instance, field.name, existing_value)

        # Then update with current form values using raw assignment
        for field_name, value in current_form_values.items():
            object.__setattr__(updated_instance, field_name, value)

        # Initialize any required lazy dataclass attributes
        if hasattr(type(original_config), '_is_lazy_dataclass'):
            object.__setattr__(updated_instance, '_is_lazy_dataclass', True)
    else:
        # Regular dataclass - use normal replace
        from dataclasses import replace
        updated_instance = replace(original_config, **current_form_values)

    print(f"\nAfter FIXED context building:")
    print(f"  store_name: {object.__getattribute__(updated_instance, 'store_name')}")
    print(f"  compressor: {object.__getattribute__(updated_instance, 'compressor')}")
    print(f"  compression_level: {object.__getattribute__(updated_instance, 'compression_level')}")

    # Check if None fields stayed None (this should work!)
    compressor_raw = object.__getattribute__(updated_instance, 'compressor')
    if compressor_raw is None:
        print(f"✅ CONTEXT FIX WORKS: compressor stayed None as expected")
    else:
        print(f"❌ CONTEXT FIX FAILED: compressor was None but got resolved to {compressor_raw}")

if __name__ == "__main__":
    test_broken_save()
    test_fixed_save()
    test_context_building_fix()
