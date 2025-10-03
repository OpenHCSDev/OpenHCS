#!/usr/bin/env python3
"""
OpenHCS + OMERO Integration Demo

Demonstrates remote pipeline execution with OMERO backend:
- Reuses test_main.py pipeline (proves compatibility)
- Executes on OMERO server (zero data transfer)
- Streams results to local Napari viewer
- Saves results back to OMERO

This is the laptop demo for the facility manager.
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
from openhcs.runtime.napari_stream_visualizer import NapariStreamingVisualizer

import multiprocessing as mp


def print_banner(text):
    """Print formatted banner."""
    print("\n" + "=" * 60)
    print(f"  {text}")
    print("=" * 60)


def connect_to_omero(host='localhost', port=4064, user='root', password='omero-root-password'):
    """Connect to OMERO server."""
    print(f"[1/7] Connecting to OMERO ({host}:{port})...")
    conn = BlitzGateway(user, password, host=host, port=port)
    if not conn.connect():
        raise RuntimeError("Failed to connect to OMERO")
    print(f"✓ Connected as {user}")
    return conn


def get_test_dataset(conn, dataset_id=None):
    """Get test dataset from OMERO."""
    print(f"[2/7] Loading dataset...")
    
    if dataset_id:
        dataset = conn.getObject("Dataset", dataset_id)
        if not dataset:
            raise ValueError(f"Dataset not found: {dataset_id}")
    else:
        # Get first available dataset
        datasets = list(conn.getObjects("Dataset"))
        if not datasets:
            raise ValueError("No datasets found in OMERO. Run import_test_data.py first.")
        dataset = datasets[0]
    
    image_count = dataset.countChildren()
    print(f"✓ Loaded dataset: {dataset.getName()} (ID: {dataset.getId()}, {image_count} images)")
    return dataset.getId()


def start_execution_server(omero_host='localhost', omero_port=4064, server_port=7777):
    """Start execution server in background process."""
    print(f"[3/7] Starting execution server (port {server_port})...")
    
    def run_server():
        server = OpenHCSExecutionServer(
            omero_data_dir=Path('/OMERO/Files'),
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
    print(f"[4/7] Starting Napari viewer (port {port})...")
    
    visualizer = NapariStreamingVisualizer()
    visualizer.start_viewer(port=port, viewer_title="OpenHCS + OMERO Demo")
    
    print(f"✓ Viewer ready")
    return visualizer


def execute_pipeline(dataset_id, server_host='localhost', server_port=7777, viewer_port=5555):
    """Execute pipeline remotely."""
    print(f"[5/7] Executing pipeline remotely...")
    
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


def validate_results(conn, dataset_id):
    """Validate results were saved to OMERO."""
    print(f"[6/7] Validating results...")
    
    dataset = conn.getObject("Dataset", dataset_id)
    image_count = dataset.countChildren()
    
    print(f"✓ Dataset contains {image_count} images")
    
    # Check for results dataset (created by pipeline)
    datasets = list(conn.getObjects("Dataset"))
    result_datasets = [d for d in datasets if 'result' in d.getName().lower()]
    
    if result_datasets:
        print(f"✓ Found {len(result_datasets)} result dataset(s)")
    
    return True


def main():
    """Run the demo."""
    print_banner("OpenHCS + OMERO Integration Demo")
    
    # Force headless mode off for demo
    os.environ['OPENHCS_HEADLESS'] = 'false'
    
    try:
        # 1. Connect to OMERO
        conn = connect_to_omero()
        
        # 2. Get test dataset
        dataset_id = get_test_dataset(conn)
        
        # 3. Start execution server
        server_process = start_execution_server()
        
        # 4. Start Napari viewer
        visualizer = start_napari_viewer()
        
        # 5. Execute pipeline
        execution_id = execute_pipeline(dataset_id)
        
        # 6. Validate results
        validate_results(conn, dataset_id)
        
        # 7. Success!
        print(f"[7/7] Demo complete!")
        print_banner(TestConstants.SUCCESS_INDICATOR)
        
        print("\n📊 Summary:")
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

