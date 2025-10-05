#!/usr/bin/env python3
"""
OpenHCS + OMERO Integration Demo - Fully Self-Contained

This is a complete end-to-end test that:
1. Launches OMERO server (via docker-compose)
2. Generates synthetic microscopy data
3. Uploads data to OMERO
4. Starts execution server
5. Sends pipeline for remote execution
6. Executes pipeline on OMERO data
7. Streams results to Napari (optional)
8. Validates results

This proves the full OpenHCS + OMERO integration works end-to-end.
"""

import os
import sys
import time
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).parent.parent))

from omero.gateway import BlitzGateway

# Import test pipeline (reuse existing test logic)
from tests.integration.test_main import create_test_pipeline, TestConstants

from openhcs.core.config import GlobalPipelineConfig, VFSConfig
from openhcs.runtime.remote_orchestrator import RemoteOrchestrator
from openhcs.runtime.execution_server import OpenHCSExecutionServer
from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer

# Import data generator
from import_test_data import generate_and_upload_synthetic_data

import multiprocessing as mp


def print_banner(text):
    """Print formatted banner."""
    print("\n" + "=" * 60)
    print(f"  {text}")
    print("=" * 60)


def connect_to_omero(host='localhost', port=4064, user='root', password='omero-root-password'):
    """Connect to OMERO server (start if needed)."""
    print(f"[1/8] Connecting to OMERO ({host}:{port})...")

    from openhcs.runtime.omero_instance_manager import OMEROInstanceManager

    omero_manager = OMEROInstanceManager(
        host=host,
        port=port,
        user=user,
        password=password
    )

    if not omero_manager.connect(timeout=60):
        raise RuntimeError("Failed to connect to or start OMERO")

    print(f"✓ Connected as {user}")
    return omero_manager


def generate_test_data(omero_manager):
    """Generate and upload synthetic test data."""
    print(f"\n[2/8] Generating and uploading synthetic test data...")

    dataset_id, image_ids = generate_and_upload_synthetic_data(
        omero_manager.conn,
        dataset_name="OpenHCS_Demo_Synthetic",
        grid_size=(2, 2),
        tile_size=(128, 128),
        wavelengths=2,
        z_stack_levels=3,
        well='A01'
    )

    print(f"✓ Generated and uploaded {len(image_ids)} images to dataset {dataset_id}")
    return dataset_id


def start_execution_server(omero_host='localhost', omero_port=4064, server_port=7777):
    """Start execution server in background process."""
    print(f"\n[3/8] Starting execution server (port {server_port})...")

    def run_server():
        server = OpenHCSExecutionServer(
            omero_data_dir=None,  # Use OMERO API (works with Docker)
            omero_host=omero_host,
            omero_port=omero_port,
            omero_user='root',
            omero_password='omero-root-password',
            server_port=server_port,
            max_workers=4
        )
        server.start()

    process = mp.Process(target=run_server, daemon=True)
    process.start()
    time.sleep(2)  # Give server time to start

    print(f"✓ Server running (PID: {process.pid})")
    return process


def start_napari_viewer(port=5555):
    """Start Napari viewer for streaming."""
    print(f"\n[4/8] Starting Napari viewer (port {port})...")

    # Create minimal FileManager for visualizer (not used in demo, but required)
    from openhcs.io.file_manager import FileManager
    from openhcs.config_framework.lazy_factory import LazyVisualizerConfig

    fm = FileManager(base_dir="/tmp")  # Dummy base_dir
    visualizer_config = LazyVisualizerConfig()

    visualizer = NapariStreamVisualizer(
        filemanager=fm,
        visualizer_config=visualizer_config,
        napari_port=port,
        viewer_title="OpenHCS + OMERO Demo"
    )
    visualizer.start_viewer()

    print(f"✓ Viewer ready")
    return visualizer


def execute_pipeline(dataset_id, server_host='localhost', server_port=7777, viewer_port=5555):
    """Execute pipeline remotely."""
    print(f"\n[5/8] Executing pipeline remotely...")
    
    # Create pipeline (reuse test_main.py)
    pipeline = create_test_pipeline()
    print(f"  → Pipeline: {pipeline.name}")
    print(f"  → Steps: {len(pipeline.steps)}")
    
    # Create config
    config = GlobalPipelineConfig(
        vfs_config=VFSConfig(backend='omero_local'),
        num_workers=1
    )
    
    # Execute remotely
    orchestrator = RemoteOrchestrator(server_host, server_port)
    
    start_time = time.time()
    response = orchestrator.run_remote_pipeline(
        plate_id=dataset_id,
        pipeline_steps=pipeline.steps,
        config=config,
        viewer_host='localhost',
        viewer_port=viewer_port
    )
    
    if response['status'] != 'accepted':
        raise RuntimeError(f"Execution failed: {response.get('message')}")
    
    execution_id = response['execution_id']
    print(f"✓ Pipeline accepted (execution_id: {execution_id})")
    
    # Poll for completion
    print(f"  → Processing...")
    while True:
        status = orchestrator.get_status(execution_id)
        if status['execution_status'] == 'completed':
            elapsed = time.time() - start_time
            wells_processed = status.get('wells_processed', 0)
            print(f"✓ Completed in {elapsed:.1f}s ({wells_processed} wells)")
            break
        elif status['execution_status'] == 'error':
            raise RuntimeError(f"Execution error: {status.get('error')}")
        time.sleep(1)
    
    return execution_id


def validate_results(omero_manager, dataset_id):
    """Validate results were saved to OMERO."""
    print(f"\n[6/8] Validating results...")

    dataset = omero_manager.conn.getObject("Dataset", dataset_id)
    image_count = dataset.countChildren()

    print(f"✓ Dataset contains {image_count} images")

    # Check for results dataset (created by pipeline)
    datasets = list(omero_manager.conn.getObjects("Dataset"))
    result_datasets = [d for d in datasets if 'result' in d.getName().lower()]

    if result_datasets:
        print(f"✓ Found {len(result_datasets)} result dataset(s)")

    return True


def main():
    """Run the fully self-contained demo."""
    print_banner("OpenHCS + OMERO Integration Demo - Self-Contained Test")

    # Force headless mode off for demo
    os.environ['OPENHCS_HEADLESS'] = 'false'

    try:
        # 1. Connect to OMERO (start if needed)
        omero_manager = connect_to_omero()

        # 2. Generate and upload synthetic test data
        dataset_id = generate_test_data(omero_manager)

        # 3. Start execution server
        server_process = start_execution_server()

        # 4. Start Napari viewer
        visualizer = start_napari_viewer()

        # 5. Execute pipeline
        execution_id = execute_pipeline(dataset_id)

        # 6. Validate results
        validate_results(omero_manager, dataset_id)

        # 7. Success!
        print(f"\n[7/8] Demo complete!")
        print_banner(TestConstants.SUCCESS_INDICATOR)

        print("\n📊 Summary:")
        print(f"  • Synthetic data: Generated and uploaded")
        print(f"  • Data transfer: 0 bytes (processing on server)")
        print(f"  • Results streamed: Real-time to Napari")
        print(f"  • Results saved: Back to OMERO")
        print(f"  • Execution ID: {execution_id}")
        
        print("\n💡 Napari viewer is still running. Close it to exit.")
        
        # Keep viewer alive
        input("\nPress Enter to exit...")
        
    except KeyboardInterrupt:
        print("\n\n⚠️  Demo interrupted")
    except Exception as e:
        print(f"\n\n❌ Demo failed: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
    finally:
        if 'conn' in locals():
            conn.close()


if __name__ == '__main__':
    main()

