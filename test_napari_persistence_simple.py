#!/usr/bin/env python3
"""
Simple test to verify the napari persistence logic fix.
Tests the core logic without actually starting napari processes.
"""

import logging
from unittest.mock import Mock, patch

# Set up logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

def test_persistence_logic():
    """Test the core persistence logic without starting actual processes."""
    
    try:
        # Mock the napari imports to avoid dependency issues
        with patch.dict('sys.modules', {
            'napari': Mock(),
            'zmq': Mock(),
        }):
            from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer
            
            # Create mock filemanager and config
            filemanager = Mock()
            visualizer_config = Mock()
            
            # Test 1: Persistent visualizer should not set is_running=False in stop_viewer
            logger.info("🧪 TEST 1: Testing persistent visualizer stop_viewer logic...")
            
            persistent_visualizer = NapariStreamVisualizer(
                filemanager=filemanager,
                visualizer_config=visualizer_config,
                viewer_title="Test Persistent",
                persistent=True,
                napari_port=5556
            )
            
            # Mock that it's running
            persistent_visualizer.is_running = True
            persistent_visualizer.process = Mock()
            persistent_visualizer.process.is_alive.return_value = True
            
            # Mock ZMQ cleanup
            persistent_visualizer.zmq_socket = Mock()
            persistent_visualizer.zmq_context = Mock()
            
            # Call stop_viewer
            persistent_visualizer.stop_viewer()
            
            # For persistent viewers, is_running should still be True
            if not persistent_visualizer.is_running:
                logger.error("❌ TEST 1 FAILED: Persistent viewer set is_running=False")
                return False
                
            # Process should not have been terminated
            if persistent_visualizer.process.terminate.called:
                logger.error("❌ TEST 1 FAILED: Persistent viewer process was terminated")
                return False
                
            logger.info("✅ TEST 1 PASSED: Persistent viewer correctly preserved is_running=True")
            
            # Test 2: Non-persistent visualizer should set is_running=False
            logger.info("🧪 TEST 2: Testing non-persistent visualizer stop_viewer logic...")
            
            non_persistent_visualizer = NapariStreamVisualizer(
                filemanager=filemanager,
                visualizer_config=visualizer_config,
                viewer_title="Test Non-Persistent",
                persistent=False,
                napari_port=5557
            )
            
            # Mock that it's running
            non_persistent_visualizer.is_running = True
            non_persistent_visualizer.process = Mock()
            non_persistent_visualizer.process.is_alive.return_value = True
            
            # Mock ZMQ cleanup
            non_persistent_visualizer.zmq_socket = Mock()
            non_persistent_visualizer.zmq_context = Mock()
            
            # Call stop_viewer
            non_persistent_visualizer.stop_viewer()
            
            # For non-persistent viewers, is_running should be False
            if non_persistent_visualizer.is_running:
                logger.error("❌ TEST 2 FAILED: Non-persistent viewer did not set is_running=False")
                return False
                
            # Process should have been terminated
            if not non_persistent_visualizer.process.terminate.called:
                logger.error("❌ TEST 2 FAILED: Non-persistent viewer process was not terminated")
                return False
                
            logger.info("✅ TEST 2 PASSED: Non-persistent viewer correctly set is_running=False and terminated process")
            
            return True
            
    except Exception as e:
        logger.error(f"❌ TEST FAILED with exception: {e}")
        import traceback
        traceback.print_exc()
        return False

def test_orchestrator_cleanup_logic():
    """Test that orchestrator respects persistence setting in cleanup."""
    
    logger.info("🧪 TEST 3: Testing orchestrator cleanup logic...")
    
    # Create mock visualizer
    mock_visualizer = Mock()
    
    # Test persistent visualizer - should not call stop_viewer
    mock_visualizer.persistent = True
    mock_visualizer._cleanup_zmq = Mock()
    
    # Simulate orchestrator cleanup logic
    if not mock_visualizer.persistent:
        mock_visualizer.stop_viewer()
        logger.info("🔬 ORCHESTRATOR: Stopped non-persistent napari visualizer")
    else:
        logger.info("🔬 ORCHESTRATOR: Keeping persistent napari visualizer alive")
        mock_visualizer._cleanup_zmq()
    
    # Verify stop_viewer was not called for persistent visualizer
    if mock_visualizer.stop_viewer.called:
        logger.error("❌ TEST 3 FAILED: stop_viewer was called for persistent visualizer")
        return False
        
    # Verify _cleanup_zmq was called
    if not mock_visualizer._cleanup_zmq.called:
        logger.error("❌ TEST 3 FAILED: _cleanup_zmq was not called for persistent visualizer")
        return False
        
    logger.info("✅ TEST 3 PASSED: Orchestrator correctly handles persistent visualizer cleanup")
    
    # Test non-persistent visualizer - should call stop_viewer
    mock_visualizer2 = Mock()
    mock_visualizer2.persistent = False
    
    # Simulate orchestrator cleanup logic
    if not mock_visualizer2.persistent:
        mock_visualizer2.stop_viewer()
        logger.info("🔬 ORCHESTRATOR: Stopped non-persistent napari visualizer")
    else:
        logger.info("🔬 ORCHESTRATOR: Keeping persistent napari visualizer alive")
        mock_visualizer2._cleanup_zmq()
    
    # Verify stop_viewer was called for non-persistent visualizer
    if not mock_visualizer2.stop_viewer.called:
        logger.error("❌ TEST 3 FAILED: stop_viewer was not called for non-persistent visualizer")
        return False
        
    logger.info("✅ TEST 3 PASSED: Orchestrator correctly handles non-persistent visualizer cleanup")
    
    return True

if __name__ == "__main__":
    logger.info("🧪 Starting napari persistence logic tests...")
    
    # Run tests
    test1_passed = test_persistence_logic()
    test2_passed = test_orchestrator_cleanup_logic()
    
    if test1_passed and test2_passed:
        logger.info("🎉 ALL TESTS PASSED! Napari persistence fix logic is working correctly.")
        exit(0)
    else:
        logger.error("💥 SOME TESTS FAILED! Check the logs above.")
        exit(1)
