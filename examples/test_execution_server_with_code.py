#!/usr/bin/env python3
"""
Test execution server using config_code approach (like RemoteOrchestrator does).
This tests that the server can handle both config_params and config_code.
"""

import sys
import zmq
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from openhcs.runtime.pipeline_execution import create_test_pipeline
from openhcs.debug.pickle_to_python import generate_complete_pipeline_steps_code, generate_config_code
from openhcs.core.config import GlobalPipelineConfig


def test_with_config_code():
    """Test execution server with config_code (Python code) instead of config_params (dict)."""
    print("\n[TEST] Testing execution server with config_code approach...")
    
    # Create pipeline
    pipeline = create_test_pipeline(well_filter=['A01'], enable_napari=False)
    
    # Generate pipeline code
    pipeline_code = generate_complete_pipeline_steps_code(
        pipeline_steps=pipeline.steps,
        clean_mode=True
    )
    
    # Create config and generate config code
    global_config = GlobalPipelineConfig(
        num_workers=2,
        use_threading=False  # Use ProcessPoolExecutor
    )
    
    config_code = generate_config_code(
        config_obj=global_config,
        config_class=GlobalPipelineConfig,
        clean_mode=True
    )
    
    print(f"  Generated pipeline code: {len(pipeline_code)} chars")
    print(f"  Generated config code: {len(config_code)} chars")
    
    # Connect to server
    context = zmq.Context()
    socket = context.socket(zmq.REQ)
    socket.connect("tcp://localhost:7777")
    
    # Send request with config_code (not config_params)
    request = {
        'command': 'execute',
        'plate_id': '/tmp/test_plate',
        'pipeline_code': pipeline_code,
        'config_code': config_code  # ← Using config_code approach
    }
    
    print(f"  Sending request to server...")
    socket.send_json(request)
    
    print(f"  Waiting for response...")
    response = socket.recv_json()
    
    socket.close()
    context.term()
    
    print(f"\n  Response:")
    print(f"    Status: {response.get('status')}")
    print(f"    Execution ID: {response.get('execution_id')}")
    if response.get('status') == 'error':
        print(f"    Error: {response.get('message')}")
        return False
    
    print(f"\n✅ Test passed! Server accepted config_code approach.")
    return True


if __name__ == '__main__':
    success = test_with_config_code()
    sys.exit(0 if success else 1)

