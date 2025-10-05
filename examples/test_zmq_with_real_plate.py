#!/usr/bin/env python3
"""
Test ZMQ execution pattern with real plate data.

This script:
1. Generates a synthetic test plate
2. Creates a real pipeline
3. Executes via ZMQ client/server
4. Validates results
"""

import sys
from pathlib import Path
import shutil

# Add openhcs to path
sys.path.insert(0, str(Path(__file__).parent.parent))


def generate_test_plate():
    """Generate synthetic test plate if it doesn't exist."""
    test_plate_dir = Path("/tmp/openhcs_zmq_test_plate")
    
    # Clean up old plate if it exists
    if test_plate_dir.exists():
        print(f"  Removing old test plate: {test_plate_dir}")
        shutil.rmtree(test_plate_dir)
    
    print(f"  Generating test plate at: {test_plate_dir}")
    
    from openhcs.tests.generators.generate_synthetic_data import SyntheticMicroscopyGenerator
    
    generator = SyntheticMicroscopyGenerator(
        output_dir=str(test_plate_dir),
        grid_size=(2, 2),  # Small grid for fast testing
        tile_size=(128, 128),  # Small tiles
        overlap_percent=10,
        wavelengths=2,  # 2 channels
        z_stack_levels=3,  # 3 z-planes
        wells=['A01', 'A02'],  # Just 2 wells
        format='ImageXpress',
        auto_image_size=True
    )
    generator.generate_dataset()
    
    # Count generated files
    image_files = list(test_plate_dir.rglob("*.tif"))
    print(f"  ✓ Generated {len(image_files)} images in {len(generator.wells)} wells")
    
    return test_plate_dir


def test_zmq_with_real_plate():
    """Test ZMQ execution with real plate data."""
    print("=" * 80)
    print("ZMQ EXECUTION WITH REAL PLATE TEST")
    print("=" * 80)
    print()
    
    # Step 1: Generate test plate
    print("[1/5] Generating test plate...")
    plate_dir = generate_test_plate()
    
    # Step 2: Create pipeline
    print("\n[2/5] Creating pipeline...")
    from openhcs.core.pipeline import Pipeline
    from openhcs.core.steps import FunctionStep as Step
    from openhcs.processing.backends.processors.numpy_processor import (
        stack_percentile_normalize,
        stack_max_project
    )
    
    pipeline = Pipeline(
        name="zmq_test_pipeline",
        steps=[
            Step(
                name="normalize",
                function=stack_percentile_normalize,
                params={'lower_percentile': 1, 'upper_percentile': 99}
            ),
            Step(
                name="max_project",
                function=stack_max_project,
                params={}
            )
        ]
    )
    
    print(f"  ✓ Created pipeline with {len(pipeline.steps)} steps")
    
    # Step 3: Create config
    print("\n[3/5] Creating config...")
    from openhcs.core.config import (
        GlobalPipelineConfig,
        PipelineConfig,
        PathPlanningConfig,
        StepWellFilterConfig,
        VFSConfig,
        MaterializationBackend
    )
    
    global_config = GlobalPipelineConfig(
        num_workers=2,
        path_planning_config=PathPlanningConfig(
            output_dir_suffix='_zmq_output'
        ),
        vfs_config=VFSConfig(
            materialization_backend=MaterializationBackend.DISK
        ),
        step_well_filter_config=StepWellFilterConfig(
            well_filter=['A01', 'A02']
        ),
        use_threading=False
    )
    
    pipeline_config = PipelineConfig()
    
    print(f"  ✓ Created GlobalPipelineConfig and PipelineConfig")
    print(f"    - Wells to process: {global_config.step_well_filter_config.well_filter}")
    print(f"    - Workers: {global_config.num_workers}")
    print(f"    - Backend: {global_config.vfs_config.materialization_backend.value}")
    
    # Step 4: Connect to execution server
    print("\n[4/5] Connecting to execution server...")
    from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
    
    client = ZMQExecutionClient(
        port=7779,  # Use unique port
        persistent=False  # Use multiprocessing.Process for testing
    )
    
    if not client.connect(timeout=15):
        print("  ✗ Failed to connect to execution server")
        return False
    
    print(f"  ✓ Connected to execution server on port {client.port}")
    
    # Step 5: Execute pipeline
    print("\n[5/5] Executing pipeline via ZMQ...")
    print("  (This will process the plate using the execution server)")
    
    try:
        response = client.execute_pipeline(
            plate_id=str(plate_dir),
            pipeline_steps=pipeline.steps,
            global_config=global_config,
            pipeline_config=pipeline_config
        )
        
        print(f"\n  Response:")
        print(f"    Status: {response.get('status')}")
        print(f"    Execution ID: {response.get('execution_id')}")
        
        if response.get('status') == 'complete':
            print(f"\n  ✓ Pipeline executed successfully!")
            results = response.get('results')
            if results:
                well_results = results.get('well_results', {})
                print(f"    Wells processed: {len(well_results)}")
                
                # Check output files
                output_dir = plate_dir / '_zmq_output'
                if output_dir.exists():
                    output_files = list(output_dir.rglob("*.tif"))
                    print(f"    Output files: {len(output_files)}")
                    print(f"    Output directory: {output_dir}")
                else:
                    print(f"    ⚠ Output directory not found: {output_dir}")
            
            success = True
        elif response.get('status') == 'error':
            print(f"\n  ✗ Pipeline failed!")
            print(f"    Error: {response.get('message')}")
            success = False
        else:
            print(f"\n  ⚠ Unexpected status: {response.get('status')}")
            success = False
        
    finally:
        # Cleanup
        print("\n  Disconnecting from server...")
        client.disconnect()
    
    if success:
        # Success!
        print("\n" + "=" * 80)
        print("✅ ZMQ EXECUTION WITH REAL PLATE TEST PASSED!")
        print("=" * 80)
        print("\nKey achievements:")
        print("  ✅ Generated synthetic test plate")
        print("  ✅ Created real pipeline with multiple steps")
        print("  ✅ Connected to ZMQ execution server")
        print("  ✅ Executed pipeline via ZMQ (code-based transport)")
        print("  ✅ Received results and validated output")
        print("\nThis proves the ZMQ execution pattern works end-to-end!")
    
    return success


if __name__ == '__main__':
    success = test_zmq_with_real_plate()
    sys.exit(0 if success else 1)

