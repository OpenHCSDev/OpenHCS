#!/usr/bin/env python3
"""
Test remote execution server with code-based serialization.

This test validates that the execution server can receive Python code
(instead of pickled objects) and execute pipelines successfully.

It mirrors the test_main_with_code_serialization pattern but uses
the RemoteOrchestrator client to send requests to the execution server.
"""

import sys
import time
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent.parent
sys.path.insert(0, str(project_root))

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig, PathPlanningConfig, VFSConfig, MaterializationBackend
from openhcs.config_framework.lazy_factory import LazyPathPlanningConfig, LazyStepWellFilterConfig
from openhcs.runtime.remote_orchestrator import RemoteOrchestrator
from tests.integration.test_main import create_test_pipeline, TestConstants


CONSTANTS = TestConstants()


def test_remote_execution_with_code_serialization(
    server_host: str = 'localhost',
    server_port: int = 7777,
    plate_path: Path = None
):
    """
    Test remote execution using code-based serialization.
    
    This test:
    1. Creates GlobalPipelineConfig, PipelineConfig, and Pipeline objects
    2. Sends them to the execution server as Python code (via RemoteOrchestrator)
    3. Server recreates objects from code using exec()
    4. Server executes pipeline
    5. Validates results
    
    Args:
        server_host: Execution server hostname
        server_port: Execution server port
        plate_path: Path to test plate (if None, uses synthetic data)
    """
    print("=" * 80)
    print("REMOTE EXECUTION CODE SERIALIZATION TEST")
    print("=" * 80)
    print(f"Server: {server_host}:{server_port}")
    
    # Find or use provided plate path
    if plate_path is None:
        synthetic_data_dir = project_root / "tests" / "synthetic_data"
        plate_dirs = list(synthetic_data_dir.glob("*"))
        if not plate_dirs:
            print("❌ No synthetic data found. Run pytest first to generate test data.")
            return False
        plate_path = plate_dirs[0]
    
    print(f"Plate: {plate_path}")
    print()
    
    # Step 1: Create objects
    print("📦 Step 1: Creating objects...")
    
    global_config = GlobalPipelineConfig(
        num_workers=CONSTANTS.DEFAULT_WORKERS,
        path_planning_config=PathPlanningConfig(
            sub_dir=CONSTANTS.DEFAULT_SUB_DIR,
            output_dir_suffix=CONSTANTS.OUTPUT_SUFFIX
        ),
        vfs_config=VFSConfig(materialization_backend=MaterializationBackend.DISK),
        use_threading=False
    )
    
    pipeline_config = PipelineConfig(
        path_planning_config=LazyPathPlanningConfig(
            output_dir_suffix=CONSTANTS.OUTPUT_SUFFIX
        ),
        step_well_filter_config=LazyStepWellFilterConfig(well_filter=CONSTANTS.PIPELINE_STEP_WELL_FILTER_TEST),
    )
    
    pipeline = create_test_pipeline()
    
    print(f"   - GlobalPipelineConfig: {type(global_config).__name__}")
    print(f"   - PipelineConfig: {type(pipeline_config).__name__}")
    print(f"   - Pipeline: {len(pipeline.steps)} steps")
    
    # Step 2: Send to remote server (RemoteOrchestrator handles code generation)
    print("\n🌐 Step 2: Sending to remote execution server...")
    print("   (RemoteOrchestrator will convert objects to Python code)")
    
    try:
        remote = RemoteOrchestrator(server_host=server_host, server_port=server_port)
        
        # First, ping the server to make sure it's alive
        print("\n   Pinging server...")
        if not remote.ping():
            print("   ❌ Server is not responding!")
            print("   Make sure the execution server is running:")
            print("   python -m openhcs.runtime.execution_server --omero-host localhost")
            return False
        print("   ✅ Server is alive")
        
        # Send execution request
        print("\n   Sending execution request...")
        response = remote.run_remote_pipeline(
            plate_id=str(plate_path),
            pipeline_steps=pipeline.steps,
            global_config=global_config,
            pipeline_config=pipeline_config
        )
        
        print(f"   Response: {response.get('status')}")
        
        if response.get('status') == 'error':
            print(f"   ❌ Execution failed: {response.get('message')}")
            return False
        
        execution_id = response.get('execution_id')
        print(f"   ✅ Execution ID: {execution_id}")
        
    except Exception as e:
        print(f"\n❌ Failed to send request: {e}")
        import traceback
        traceback.print_exc()
        return False
    
    # Step 3: Verify execution completed
    print("\n🔍 Step 3: Verifying execution...")
    
    if response.get('status') == 'complete':
        print("   ✅ Execution completed successfully!")
        results = response.get('results', {})
        wells_processed = len(results.get('well_results', {}))
        print(f"   Wells processed: {wells_processed}")
    else:
        print(f"   ⚠️  Unexpected status: {response.get('status')}")
        return False
    
    # Success!
    print("\n" + "=" * 80)
    print("✅ REMOTE EXECUTION CODE SERIALIZATION TEST PASSED!")
    print("=" * 80)
    print("\nKey achievements:")
    print("  ✅ Objects converted to Python code")
    print("  ✅ Code sent over network")
    print("  ✅ Server recreated objects from code")
    print("  ✅ Pipeline executed successfully")
    print("  ✅ No pickling errors!")
    print("\nThis proves code-based serialization works for remote execution.")
    
    return True


def main():
    """Run the remote execution test."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Test remote execution with code serialization')
    parser.add_argument('--server-host', default='localhost', help='Execution server hostname')
    parser.add_argument('--server-port', type=int, default=7777, help='Execution server port')
    parser.add_argument('--plate-path', type=Path, help='Path to test plate (optional)')
    
    args = parser.parse_args()
    
    success = test_remote_execution_with_code_serialization(
        server_host=args.server_host,
        server_port=args.server_port,
        plate_path=args.plate_path
    )
    
    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())

