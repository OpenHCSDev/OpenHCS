#!/usr/bin/env python3
"""
Debug script to inspect PipelineConfig behavior
"""

print("🔍 Testing PipelineConfig creation behavior...")

# Import the lazy config system
from openhcs.core.config import PipelineConfig, GlobalPipelineConfig

print("\n1. Creating PipelineConfig() with no arguments:")
pc1 = PipelineConfig()
print(f"   PipelineConfig(): {pc1}")
print(f"   Type: {type(pc1)}")
print(f"   num_workers: {pc1.num_workers}")
print(f"   step_well_filter_config: {pc1.step_well_filter_config}")

print("\n2. Creating GlobalPipelineConfig() with no arguments:")
gpc1 = GlobalPipelineConfig()
print(f"   GlobalPipelineConfig(): {gpc1}")
print(f"   Type: {type(gpc1)}")
print(f"   num_workers: {gpc1.num_workers}")
print(f"   step_well_filter_config: {gpc1.step_well_filter_config}")

print("\n3. Checking if PipelineConfig is lazy:")
print(f"   PipelineConfig.__module__: {PipelineConfig.__module__}")
print(f"   PipelineConfig.__name__: {PipelineConfig.__name__}")

print("\n4. Checking class attributes:")
from dataclasses import fields
pc_fields = fields(PipelineConfig)
print(f"   PipelineConfig fields: {len(pc_fields)}")
for field in pc_fields[:5]:  # Show first 5 fields
    print(f"     {field.name}: default={field.default}, default_factory={field.default_factory}")

print("\n5. Testing field access on fresh PipelineConfig:")
pc2 = PipelineConfig()
try:
    print(f"   pc2.num_workers (before any global config): {pc2.num_workers}")
except Exception as e:
    print(f"   Error accessing num_workers: {e}")

print("\n6. Checking what global config is currently loaded:")
from openhcs.core.context.global_config import get_current_global_config
try:
    current_global = get_current_global_config()
    print(f"   Current global config: {current_global}")
    if current_global:
        print(f"   Current global num_workers: {current_global.num_workers}")
        print(f"   Current global step_well_filter_config: {current_global.step_well_filter_config}")
        if hasattr(current_global, 'step_well_filter_config') and current_global.step_well_filter_config:
            print(f"   Current global step_well_filter_config.well_filter: {current_global.step_well_filter_config.well_filter}")
except Exception as e:
    print(f"   Error getting current global config: {e}")

print("\n7. Testing dual-axis resolution with orchestrator context:")
from openhcs.core.dual_axis_resolver_implementation import ContextDiscovery
context = ContextDiscovery.discover_context()
print(f"   Discovered context: {context} (type: {type(context)})")

print("\n8. Creating PipelineConfig with explicit None values:")
pc4 = PipelineConfig(num_workers=None, step_well_filter_config=None)
print(f"   pc4 with explicit None: {pc4}")
print(f"   pc4.num_workers: {pc4.num_workers}")
print(f"   pc4.step_well_filter_config: {pc4.step_well_filter_config}")

print("\n9. Checking PipelineConfig field definitions:")
from dataclasses import fields
pc_fields = fields(PipelineConfig)
for field in pc_fields:
    if 'step_well_filter' in field.name or 'step_materialization' in field.name:
        print(f"   {field.name}:")
        print(f"     type: {field.type}")
        print(f"     default: {field.default}")
        print(f"     default_factory: {field.default_factory}")

print("\n10. Testing default factory behavior:")
pc5 = PipelineConfig()
print(f"   Fresh PipelineConfig() step_well_filter_config type: {type(pc5.step_well_filter_config)}")
print(f"   Fresh PipelineConfig() step_materialization_config type: {type(pc5.step_materialization_config)}")

# Check if the field has a default factory
import dataclasses
step_well_filter_field = next(f for f in fields(PipelineConfig) if f.name == 'step_well_filter_config')
print(f"   step_well_filter_config field default_factory: {step_well_filter_field.default_factory}")
if step_well_filter_field.default_factory != dataclasses.MISSING:
    print(f"   Calling default_factory(): {step_well_filter_field.default_factory()}")
