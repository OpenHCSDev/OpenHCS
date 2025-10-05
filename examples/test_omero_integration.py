#!/usr/bin/env python3
"""
Test OMERO integration end-to-end.

This script tests the full workflow:
1. Connect to OMERO (start if needed)
2. Generate synthetic plate
3. Upload to OMERO
4. Submit pipeline via RemoteOrchestrator
5. Monitor execution
6. Verify results

This simulates what the OMERO.web plugin does.

Follows the same pattern as Napari instance management:
- Check if OMERO is running
- Connect to existing instance if available
- Start new instance if needed
"""

import sys
import time
from pathlib import Path

# Add openhcs to path
sys.path.insert(0, str(Path(__file__).parent.parent))


def test_omero_integration():
    """Test full OMERO integration workflow."""

    print("=" * 60)
    print("OMERO Integration Test")
    print("=" * 60)

    # Step 1: Connect to OMERO (start if needed)
    print("\n[1/6] Connecting to OMERO...")
    from openhcs.runtime.omero_instance_manager import OMEROInstanceManager

    omero_manager = OMEROInstanceManager()

    if not omero_manager.connect(timeout=60):
        print("❌ Failed to connect to or start OMERO")
        return False

    conn = omero_manager.conn
    print("✓ Connected to OMERO")

    try:
        # Step 2: Generate and upload synthetic plate
        print("\n[2/6] Generating and uploading synthetic plate...")
        from import_test_data import generate_and_upload_synthetic_plate

        plate_id = generate_and_upload_synthetic_plate(
            conn,
            plate_name="Test_Plate_Integration",
            wells=['A01', 'A02']
        )

        print(f"✓ Created plate ID: {plate_id}")

        # Step 3: Start execution server if needed
        print("\n[3/6] Checking execution server...")
        from openhcs.runtime.remote_orchestrator import RemoteOrchestrator

        remote = RemoteOrchestrator(server_host='localhost', server_port=7777)

        if not remote.ping():
            print("⚠ Execution server not running, starting it...")
            # Start execution server in background
            import subprocess
            import multiprocessing as mp

            def start_server():
                from openhcs.runtime.execution_server import OpenHCSExecutionServer
                server = OpenHCSExecutionServer(
                    omero_data_dir=None,
                    omero_host='localhost',
                    omero_port=4064,
                    omero_user='root',
                    omero_password='omero-root-password',
                    server_port=7777
                )
                server.start()

            server_process = mp.Process(target=start_server, daemon=True)
            server_process.start()

            # Wait for server to be ready
            max_wait = 10
            for i in range(max_wait):
                time.sleep(1)
                if remote.ping():
                    print(f"✓ Execution server started")
                    break
            else:
                print("❌ Execution server failed to start")
                return False
        else:
            print("✓ Execution server is running")

        # Step 4: Submit pipeline via RemoteOrchestrator (same as OMERO.web plugin)
        print("\n[4/6] Submitting pipeline to execution server...")

        # Create test pipeline
        from tests.integration.test_main import create_test_pipeline
        from openhcs.core.config import GlobalPipelineConfig, VFSConfig
        from openhcs.constants import Backend

        pipeline = create_test_pipeline()

        # Create config - OMERO backend will be used for reading
        # (execution server registers OMERO backend on startup)
        global_config = GlobalPipelineConfig(
            vfs_config=VFSConfig(
                read_backend=Backend.AUTO  # Will use OMERO backend registered by server
            ),
            num_workers=1
        )

        # Submit via RemoteOrchestrator (uses code serialization)
        response = remote.run_remote_pipeline(
            plate_id=plate_id,
            pipeline_steps=pipeline.steps,
            global_config=global_config
        )

        if response.get('status') != 'complete':
            print(f"❌ Pipeline execution failed: {response.get('message', 'Unknown error')}")
            print(f"   Response: {response}")
            return False

        execution_id = response.get('execution_id')
        print(f"✓ Pipeline executed! Execution ID: {execution_id}")

        # Step 5: Verify execution completed
        print("\n[5/6] Verifying execution...")

        # Since we're using synchronous execution, it's already complete
        results = response.get('results')
        if results:
            wells_processed = len(results.get('well_results', {}))
            print(f"✓ Processing complete!")
            print(f"  Wells processed: {wells_processed}")
        else:
            print(f"✓ Processing complete!")
            print(f"  (No detailed results returned)")

        print(f"  Execution ID: {execution_id}")

        # Step 6: Verify results
        print("\n[6/6] Verifying results...")
        
        plate = conn.getObject("Plate", plate_id)
        if not plate:
            print("❌ Could not retrieve plate")
            return False
        
        # Count images in plate
        image_count = 0
        for well in plate.listChildren():
            for ws in well.listChildren():
                image_count += 1
        
        print(f"✓ Plate has {image_count} images")
        
        # Success!
        print("\n" + "=" * 60)
        print("✅ OMERO Integration Test PASSED!")
        print("=" * 60)
        print(f"\nPlate ID: {plate_id}")
        print(f"View in OMERO.web: http://localhost:4080/webclient/?show=plate-{plate_id}")
        print("\nNext steps:")
        print("1. Install OMERO.web plugin: cd omero_openhcs && pip install -e .")
        print("2. Configure OMERO.web: see omero_openhcs/INSTALL.md")
        print("3. Browse to plate and use OpenHCS tab!")
        
        return True

    finally:
        omero_manager.close()


if __name__ == '__main__':
    success = test_omero_integration()
    sys.exit(0 if success else 1)

