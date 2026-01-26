Troubleshooting & FAQ
============================

Common Issues
-------------

Remote Execution Server Stops Responding
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: When using remote execution (ZMQ execution server), the server stops accepting new pipeline runs after successfully completing a few executions. You need to kill and restart the server.

**Solution**: This was a critical bug in the ZMQ socket handling that has been fixed. Update to the latest version of OpenHCS. If you're running an older version, restart the server as a temporary workaround.


(Under Construction - More troubleshooting entries coming soon)
