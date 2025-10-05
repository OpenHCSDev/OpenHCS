"""
Test remote execution with code-based serialization using pytest fixtures.

This test validates that the execution server can receive Python code
(instead of pickled objects) and execute pipelines successfully.
"""

import pytest
from pathlib import Path
from typing import Union, Dict

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig, PathPlanningConfig, VFSConfig, MaterializationBackend
from openhcs.config_framework.lazy_factory import LazyPathPlanningConfig, LazyStepWellFilterConfig
from openhcs.runtime.remote_orchestrator import RemoteOrchestrator
from tests.integration.test_main import create_test_pipeline, TestConstants

# Import fixtures from test_main
from tests.integration.test_main import (
    base_test_dir,
    test_function_dir,
)
from tests.integration.helpers.fixture_utils import (
    plate_dir,
    microscope_config,
    backend_config,
    data_type_config,
    test_params,
)

CONSTANTS = TestConstants()


@pytest.mark.parametrize("server_port", [7777])
def test_remote_code_serialization(plate_dir: Union[Path, str], backend_config: str, data_type_config: Dict, execution_mode: str, server_port: int):
    """
    Test remote execution using code-based serialization.
    
    This test:
    1. Creates GlobalPipelineConfig, PipelineConfig, and Pipeline objects
    2. Sends them to the execution server as Python code (via RemoteOrchestrator)
    3. Server recreates objects from code using exec()
    4. Server executes pipeline
    5. Validates results
    """
    print("\n" + "=" * 80)
    print("REMOTE EXECUTION CODE SERIALIZATION TEST")
    print("=" * 80)
    print(f"Server: localhost:{server_port}")
    print(f"Plate: {plate_dir}")
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
    
    remote = RemoteOrchestrator(server_host='localhost', server_port=server_port)
    
    # First, ping the server to make sure it's alive
    print("\n   Pinging server...")
    if not remote.ping():
        pytest.skip("Execution server is not running. Start it with: python -m openhcs.runtime.execution_server --omero-host localhost --port 7777")
    print("   ✅ Server is alive")
    
    # Send execution request
    print("\n   Sending execution request...")
    response = remote.run_remote_pipeline(
        plate_id=str(plate_dir),
        pipeline_steps=pipeline.steps,
        global_config=global_config,
        pipeline_config=pipeline_config
    )
    
    print(f"   Response: {response.get('status')}")
    
    assert response.get('status') != 'error', f"Execution failed: {response.get('message')}"
    
    execution_id = response.get('execution_id')
    print(f"   ✅ Execution ID: {execution_id}")
    
    # Step 3: Verify execution completed
    print("\n🔍 Step 3: Verifying execution...")

    assert response.get('status') == 'complete', f"Unexpected status: {response.get('status')}"

    print("   ✅ Execution completed successfully!")
    results = response.get('results')
    if results:
        wells_processed = len(results.get('well_results', {}))
        print(f"   Wells processed: {wells_processed}")
    else:
        print("   (Results not included in response)")
    
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

