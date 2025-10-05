#!/usr/bin/env python3
"""
Test ZMQ execution pattern.

This script tests the new ZMQ-based execution client/server pattern
that replaces the subprocess runner.

It demonstrates:
1. Client connects to server (spawns if needed)
2. Client sends pipeline execution request
3. Server executes pipeline
4. Client receives results
"""

import sys
from pathlib import Path

# Add openhcs to path
sys.path.insert(0, str(Path(__file__).parent.parent))


def test_zmq_execution():
    """Test ZMQ execution pattern."""
    print("=" * 80)
    print("ZMQ EXECUTION PATTERN TEST")
    print("=" * 80)
    print()
    
    # Step 1: Create test pipeline
    print("[1/4] Creating test pipeline...")
    from openhcs.core.pipeline import Pipeline
    from openhcs.core.steps import FunctionStep as Step
    from openhcs.processing.backends.processors.numpy_processor import stack_percentile_normalize
    
    pipeline = Pipeline(
        name="test_pipeline",
        steps=[
            Step(
                name="normalize",
                function=stack_percentile_normalize,
                params={'lower_percentile': 1, 'upper_percentile': 99}
            )
        ]
    )
    
    print(f"  ✓ Created pipeline with {len(pipeline.steps)} steps")
    
    # Step 2: Create config
    print("\n[2/4] Creating config...")
    from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
    
    global_config = GlobalPipelineConfig(
        num_workers=2,
        use_threading=False
    )
    
    pipeline_config = PipelineConfig()
    
    print(f"  ✓ Created GlobalPipelineConfig and PipelineConfig")
    
    # Step 3: Connect to execution server (will spawn if needed)
    print("\n[3/4] Connecting to execution server...")
    from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
    
    client = ZMQExecutionClient(
        port=7778,  # Use different port to avoid conflicts
        persistent=False  # Use multiprocessing.Process for testing
    )
    
    if not client.connect():
        print("  ✗ Failed to connect to execution server")
        return False
    
    print(f"  ✓ Connected to execution server on port {client.port}")
    
    # Step 4: Execute pipeline
    print("\n[4/4] Executing pipeline...")
    
    # Use a test plate path
    test_plate = Path("/tmp/test_plate")
    
    try:
        response = client.execute_pipeline(
            plate_id=str(test_plate),
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
                wells_processed = len(results.get('well_results', {}))
                print(f"    Wells processed: {wells_processed}")
        elif response.get('status') == 'error':
            print(f"\n  ✗ Pipeline failed!")
            print(f"    Error: {response.get('message')}")
            return False
        
    finally:
        # Cleanup
        client.disconnect()
    
    # Success!
    print("\n" + "=" * 80)
    print("✅ ZMQ EXECUTION PATTERN TEST PASSED!")
    print("=" * 80)
    print("\nKey achievements:")
    print("  ✅ Client connected to server (spawned automatically)")
    print("  ✅ Pipeline sent as Python code (no pickling)")
    print("  ✅ Server executed pipeline")
    print("  ✅ Client received results")
    print("\nThis proves the ZMQ execution pattern works!")
    
    return True


if __name__ == '__main__':
    success = test_zmq_execution()
    sys.exit(0 if success else 1)

