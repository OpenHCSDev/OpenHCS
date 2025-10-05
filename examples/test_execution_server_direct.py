#!/usr/bin/env python3
"""
Test execution server using EXACT same setup as test_main.py.
Reuses shared pipeline creation and config functions to ensure identical code paths.
"""

import sys
import time
import zmq
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

# Build a minimal pipeline locally (same mechanism as UI export)
from openhcs.debug.pickle_to_python import generate_complete_pipeline_steps_code
from openhcs.core.pipeline import Pipeline
from openhcs.core.steps import FunctionStep as Step
from openhcs.processing.backends.processors.numpy_processor import stack_percentile_normalize


def generate_test_plate():
    """Generate synthetic test plate if it doesn't exist."""
    test_plate_dir = Path("/tmp/openhcs_test_plate")

    if test_plate_dir.exists():
        print(f"[1/2] Test plate already exists at: {test_plate_dir}")
        return test_plate_dir

    print(f"[1/2] Generating test plate...")

    from openhcs.tests.generators.generate_synthetic_data import generate_synthetic_plate

    generate_synthetic_plate(
        output_dir=test_plate_dir,
        plate_name="openhcs_test_plate",
        num_wells=2,
        num_sites=2,
        num_channels=2,
        num_z_planes=3,
        num_timepoints=1,
        image_size=(512, 512),
        microscope_format='imagexpress'
    )

    print(f"  ✓ Generated test plate at: {test_plate_dir}")
    return test_plate_dir


def test_execution_server(plate_path: Path):
    """Test execution server using EXACT same setup as test_main.py."""
    print(f"\n[2/2] Testing execution server...")
    print(f"  Plate path: {plate_path}")

    # Use shared functions to create pipeline and config (EXACT same as test_main.py)
    well_filter = ['A01', 'A02']

    # Create pipeline using shared function
    pipeline = create_test_pipeline(
        well_filter=well_filter,
        enable_napari=False  # Disable napari for server test
    )

    # Create config using shared function
    global_config, pipeline_config = create_pipeline_config(
        num_workers=4,
        output_dir_suffix='_output',
        well_filter=well_filter,
        use_threading=False,  # Use ProcessPoolExecutor (same as test_main.py)
        materialization_backend='disk'
    )

    # Generate code for server-side compilation (same as UI Code button)
    pipeline_code = generate_complete_pipeline_steps_code(
        pipeline_steps=pipeline.steps,
        clean_mode=True
    )

    # Send config parameters instead of code - let server call create_pipeline_config()
    config_params = {
        'num_workers': global_config.num_workers,
        'output_dir_suffix': global_config.path_planning_config.output_dir_suffix,
        'well_filter': global_config.step_well_filter_config.well_filter,
        'use_threading': global_config.use_threading,
        'materialization_backend': global_config.vfs_config.materialization_backend.value
    }

    context = zmq.Context()
    socket = context.socket(zmq.REQ)
    socket.connect("tcp://localhost:7777")

    request = {
        'command': 'execute',
        'plate_id': str(plate_path),
        'pipeline_code': pipeline_code,
        'config_params': config_params
    }

    print(f"  Sending pipeline to execution server...")
    print(f"  (Server executes synchronously - this will block until complete)")
    socket.send_json(request)

    # Server now executes synchronously, so response contains final result
    response = socket.recv_json()

    if response['status'] == 'completed':
        print(f"  ✓ Pipeline completed successfully!")
        print(f"  Execution ID: {response['execution_id']}")
        print(f"  Wells processed: {response.get('wells_processed')}")
    elif response['status'] == 'error':
        print(f"  ✗ Pipeline failed!")
        print(f"  Error: {response.get('message')}")
    else:
        print(f"  ✗ Unexpected response: {response}")
    
    socket.close()
    context.term()


if __name__ == '__main__':
    plate_path = generate_test_plate()
    test_execution_server(plate_path)
