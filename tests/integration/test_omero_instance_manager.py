"""
Test OMERO instance manager.

Verifies that the OMERO instance manager follows the same pattern as Napari:
- Check if OMERO is running
- Connect to existing instance if available
- Start new instance if needed
"""

import pytest
import time


def test_omero_instance_manager_connect_to_existing():
    """Test connecting to an existing OMERO instance."""
    from openhcs.runtime.omero_instance_manager import OMEROInstanceManager
    
    # Create manager
    manager = OMEROInstanceManager()
    
    # Try to connect (will start OMERO if not running)
    assert manager.connect(timeout=60), "Failed to connect to or start OMERO"
    
    # Verify connection is alive
    assert manager.conn is not None, "Connection should not be None"
    
    # Verify we can query OMERO
    try:
        manager.conn.getEventContext()
        print("✓ Successfully connected to OMERO")
    except Exception as e:
        pytest.fail(f"Failed to query OMERO: {e}")
    
    # Close connection
    manager.close()
    assert manager.conn is None, "Connection should be None after close"


def test_omero_instance_manager_reuse_connection():
    """Test that multiple managers can connect to the same OMERO instance."""
    from openhcs.runtime.omero_instance_manager import OMEROInstanceManager
    
    # Create first manager
    manager1 = OMEROInstanceManager()
    assert manager1.connect(timeout=60), "Failed to connect to or start OMERO"
    
    # Create second manager - should connect to existing instance
    manager2 = OMEROInstanceManager()
    assert manager2.connect(timeout=10), "Failed to connect to existing OMERO"
    
    # Both should be connected
    assert manager1.conn is not None
    assert manager2.conn is not None
    
    # Both should be able to query OMERO
    manager1.conn.getEventContext()
    manager2.conn.getEventContext()
    
    print("✓ Multiple managers can connect to same OMERO instance")
    
    # Cleanup
    manager1.close()
    manager2.close()


def test_omero_instance_manager_context_manager():
    """Test using OMERO instance manager as context manager."""
    from openhcs.runtime.omero_instance_manager import OMEROInstanceManager
    
    with OMEROInstanceManager() as manager:
        assert manager.conn is not None, "Connection should be established"
        manager.conn.getEventContext()
        print("✓ Context manager works")
    
    # Connection should be closed after context exit
    assert manager.conn is None, "Connection should be closed after context exit"


if __name__ == '__main__':
    # Run tests
    print("Testing OMERO instance manager...")
    
    print("\n[1/3] Test: Connect to existing OMERO")
    test_omero_instance_manager_connect_to_existing()
    
    print("\n[2/3] Test: Reuse connection")
    test_omero_instance_manager_reuse_connection()
    
    print("\n[3/3] Test: Context manager")
    test_omero_instance_manager_context_manager()
    
    print("\n✅ All tests passed!")

