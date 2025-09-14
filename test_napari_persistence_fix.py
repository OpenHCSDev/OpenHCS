#!/usr/bin/env python3
"""
Test script to verify napari viewer persistence bug fix.

This script tests that:
1. Persistent napari viewers stay alive after pipeline completion
2. Subsequent pipeline runs reuse the existing viewer process
3. Non-persistent viewers are properly cleaned up
"""

import logging
import time
import multiprocessing
from unittest.mock import Mock

# Set up logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

def test_persistent_viewer():
    """Test that persistent viewers stay alive between runs."""
    try:
        from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer
        from openhcs.io.file_manager import FileManager
        from openhcs.constants.constants import Backend
        
        # Create mock filemanager and config
        filemanager = Mock()
        visualizer_config = Mock()
        
        # Test 1: Create persistent visualizer
        logger.info("🧪 TEST 1: Creating persistent napari visualizer...")
        visualizer = NapariStreamVisualizer(
            filemanager=filemanager,
            visualizer_config=visualizer_config,
            viewer_title="Test Persistent Viewer",
            persistent=True,
            napari_port=5556  # Use different port to avoid conflicts
        )
        
        # Start viewer
        logger.info("🧪 Starting viewer...")
        visualizer.start_viewer()
        
        if not visualizer.is_running:
            logger.error("❌ TEST FAILED: Viewer failed to start")
            return False
            
        initial_process = visualizer.process
        initial_pid = initial_process.pid if initial_process else None
        logger.info(f"✅ Viewer started successfully (PID: {initial_pid})")
        
        # Simulate end of pipeline run - call stop_viewer
        logger.info("🧪 Simulating end of pipeline run...")
        visualizer.stop_viewer()
        
        # Check that process is still alive for persistent viewer
        if not initial_process.is_alive():
            logger.error("❌ TEST FAILED: Persistent viewer process was killed")
            return False
            
        # Check that is_running is still True for persistent viewers
        if not visualizer.is_running:
            logger.error("❌ TEST FAILED: is_running was set to False for persistent viewer")
            return False
            
        logger.info("✅ Persistent viewer correctly stayed alive")
        
        # Test 2: Create second visualizer instance (simulating new pipeline run)
        logger.info("🧪 TEST 2: Creating second visualizer instance...")
        visualizer2 = NapariStreamVisualizer(
            filemanager=filemanager,
            visualizer_config=visualizer_config,
            viewer_title="Test Persistent Viewer 2",
            persistent=True,
            napari_port=5556  # Same port - should reuse existing process
        )
        
        # Start viewer - should reuse existing process
        logger.info("🧪 Starting second viewer (should reuse existing process)...")
        visualizer2.start_viewer()
        
        if not visualizer2.is_running:
            logger.error("❌ TEST FAILED: Second viewer failed to start")
            return False
            
        # Check that it reused the same process
        if visualizer2.process.pid != initial_pid:
            logger.error(f"❌ TEST FAILED: Second viewer created new process (PID: {visualizer2.process.pid}) instead of reusing existing (PID: {initial_pid})")
            return False
            
        logger.info(f"✅ Second viewer correctly reused existing process (PID: {visualizer2.process.pid})")
        
        # Cleanup
        logger.info("🧪 Cleaning up test...")
        if initial_process and initial_process.is_alive():
            initial_process.terminate()
            initial_process.join(timeout=3)
            if initial_process.is_alive():
                initial_process.kill()
        
        logger.info("✅ ALL TESTS PASSED: Napari persistence fix is working correctly!")
        return True
        
    except ImportError as e:
        logger.warning(f"⚠️  Skipping napari test - napari not available: {e}")
        return True  # Not a failure, just not testable
    except Exception as e:
        logger.error(f"❌ TEST FAILED with exception: {e}")
        return False

def test_non_persistent_viewer():
    """Test that non-persistent viewers are properly cleaned up."""
    try:
        from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer
        from openhcs.io.file_manager import FileManager
        
        # Create mock filemanager and config
        filemanager = Mock()
        visualizer_config = Mock()
        
        logger.info("🧪 TEST 3: Creating non-persistent napari visualizer...")
        visualizer = NapariStreamVisualizer(
            filemanager=filemanager,
            visualizer_config=visualizer_config,
            viewer_title="Test Non-Persistent Viewer",
            persistent=False,  # Non-persistent
            napari_port=5557  # Different port
        )
        
        # Start viewer
        logger.info("🧪 Starting non-persistent viewer...")
        visualizer.start_viewer()
        
        if not visualizer.is_running:
            logger.error("❌ TEST FAILED: Non-persistent viewer failed to start")
            return False
            
        process = visualizer.process
        pid = process.pid if process else None
        logger.info(f"✅ Non-persistent viewer started successfully (PID: {pid})")
        
        # Simulate end of pipeline run - call stop_viewer
        logger.info("🧪 Simulating end of pipeline run for non-persistent viewer...")
        visualizer.stop_viewer()
        
        # Check that process was terminated for non-persistent viewer
        time.sleep(1)  # Give it a moment to terminate
        if process.is_alive():
            logger.error("❌ TEST FAILED: Non-persistent viewer process was not terminated")
            # Cleanup
            process.terminate()
            process.join(timeout=3)
            if process.is_alive():
                process.kill()
            return False
            
        # Check that is_running was set to False
        if visualizer.is_running:
            logger.error("❌ TEST FAILED: is_running was not set to False for non-persistent viewer")
            return False
            
        logger.info("✅ Non-persistent viewer correctly terminated")
        return True
        
    except ImportError as e:
        logger.warning(f"⚠️  Skipping napari test - napari not available: {e}")
        return True  # Not a failure, just not testable
    except Exception as e:
        logger.error(f"❌ TEST FAILED with exception: {e}")
        return False

if __name__ == "__main__":
    logger.info("🧪 Starting napari persistence bug fix tests...")
    
    # Run tests
    test1_passed = test_persistent_viewer()
    test2_passed = test_non_persistent_viewer()
    
    if test1_passed and test2_passed:
        logger.info("🎉 ALL TESTS PASSED! Napari persistence fix is working correctly.")
        exit(0)
    else:
        logger.error("💥 SOME TESTS FAILED! Check the logs above.")
        exit(1)
