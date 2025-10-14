Viewer Management Guide
=======================

Overview
--------

OpenHCS supports streaming images to external viewers for interactive visualization:

- **Napari**: Python-based viewer with layer management and advanced visualization
- **Fiji/ImageJ**: Java-based viewer with hyperstack support and extensive plugin ecosystem

Both viewers can be used simultaneously, and viewers are automatically reused across different parts of OpenHCS (pipelines, image browser, manual streaming).

This guide covers how to use viewers effectively from a user perspective.

.. note::
   For architecture details and developer information, see :doc:`../architecture/viewer_streaming_architecture`

Using the Image Browser
-----------------------

The image browser is the main interface for viewing images interactively.

Opening the Image Browser
~~~~~~~~~~~~~~~~~~~~~~~~~~

1. Load a plate in the PyQt GUI
2. Click the "Image Browser" tab
3. The browser shows a folder tree and image table

Enabling Viewers
~~~~~~~~~~~~~~~~

**Napari** (enabled by default):

- Check "Enable Napari Streaming" to activate
- Configure display settings (LUT, contrast, etc.)
- Images will stream to Napari viewer

**Fiji** (disabled by default):

- Check "Enable Fiji Streaming" to activate
- Configure dimension mapping and display settings
- Images will stream to Fiji/ImageJ viewer

**Both viewers**:

- Enable both checkboxes to stream to both viewers simultaneously
- Useful for comparing visualization approaches

Viewing Images
~~~~~~~~~~~~~~

**Single image**:

1. Click an image in the table
2. Click "View in Napari" or "View in Fiji" button
3. Viewer opens (if not already open) and displays image

**Multiple images** (recommended for hyperstacks):

1. Select multiple images (Ctrl+Click or Shift+Click)
2. Click "View in Napari" or "View in Fiji"
3. All images stream as a batch and build a hyperstack

**Double-click**:

- Double-click any image to stream to enabled viewer(s)
- If both enabled, streams to both
- If neither enabled, shows a message

Progressive Hyperstack Building
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

You can build hyperstacks incrementally by sending images one at a time:

1. Select and view first z-slice → Creates hyperstack with 1 Z
2. Select and view second z-slice → Adds to hyperstack → Now has 2 Z
3. Select and view different channel → Adds to hyperstack → Now has 2 Z × 2 channels

This works for both Napari and Fiji viewers.

Managing Viewer Instances
~~~~~~~~~~~~~~~~~~~~~~~~~~

The "Napari Instances" panel shows all detected viewers:

**Status indicators**:

- ✅ Ready - Viewer is running and ready to receive images
- 🚀 Starting... - Viewer is launching (wait a few seconds)

**Viewer types**:

- "Napari Port 5555" - Napari viewer on port 5555
- "Fiji Port 5556" - Fiji viewer on port 5556
- "Port 5557" - External viewer (type unknown)

**Killing viewers**:

1. Select viewer in the list
2. Click "Kill Selected Instances"
3. Viewer process is terminated and port is freed

.. warning::
   Only kill viewers when you're done with them. Killing a viewer that's being used by a running pipeline may cause errors.

Viewer Comparison
-----------------

Napari vs Fiji
~~~~~~~~~~~~~~

**Napari**:

- ✅ Modern Python-based interface
- ✅ Layer-based visualization (easy to toggle layers)
- ✅ Advanced rendering (GPU-accelerated)
- ✅ Plugin ecosystem for analysis
- ❌ Slower startup time
- ❌ Higher memory usage

**Fiji/ImageJ**:

- ✅ Fast startup
- ✅ Extensive plugin ecosystem (decades of development)
- ✅ Hyperstack-based (traditional microscopy workflow)
- ✅ Lower memory usage
- ❌ Java-based (separate process)
- ❌ Less modern interface

**When to use which**:

- **Napari**: Interactive exploration, modern workflows, GPU rendering
- **Fiji**: Quick checks, traditional ImageJ workflows, plugin compatibility
- **Both**: Compare visualizations, leverage strengths of each

Common Issues
-------------

Viewer Won't Start
~~~~~~~~~~~~~~~~~~

**Symptoms**: Clicking "View" does nothing, or shows "Starting..." forever

**Solutions**:

1. Check if port is already in use: ``lsof -i :5555``
2. Kill any stuck processes on the port
3. Try a different port in the config
4. Check logs in ``~/.local/share/openhcs/logs/``

Images Not Appearing
~~~~~~~~~~~~~~~~~~~~

**Symptoms**: Viewer opens but images don't show

**Solutions**:

1. Wait for "✅ Ready" status in instance list
2. Check if viewer window is hidden behind other windows
3. For Fiji: Ensure PyImageJ is installed correctly
4. Check that images are actually loading (check file paths)

Hyperstack Has Wrong Dimensions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Symptoms**: Fiji hyperstack shows wrong number of channels/slices/frames

**Solutions**:

1. Select all images before clicking "View" (batch streaming)
2. Check that filenames have correct metadata (channel, z-index, etc.)
3. Verify dimension mapping in Fiji config
4. Close and reopen hyperstack to rebuild

Memory Issues
~~~~~~~~~~~~~

**Symptoms**: System runs out of memory when viewing many images

**Solutions**:

1. View fewer images at once
2. Use Napari instead of Fiji (more efficient memory management)
3. Close unused viewer windows
4. Reduce image resolution if possible

Tips and Best Practices
-----------------------

Efficient Workflow
~~~~~~~~~~~~~~~~~~

1. **Enable only what you need**: Disable unused viewers to save resources
2. **Batch selection**: Select all images you want to view before clicking "View"
3. **Reuse viewers**: OpenHCS automatically reuses viewers - no need to close and reopen
4. **Progressive building**: Build hyperstacks incrementally by sending images one at a time
5. **Check status first**: Wait for "✅ Ready" before expecting images to appear

Performance
~~~~~~~~~~~

1. **Use Fiji for quick checks**: Faster startup and lower memory usage
2. **Use Napari for exploration**: Better for interactive analysis and modern workflows
3. **Close unused windows**: Free up memory by closing viewer windows you're done with
4. **Limit batch size**: Don't try to view hundreds of images at once

Troubleshooting
~~~~~~~~~~~~~~~

1. **Check logs**: ``~/.local/share/openhcs/logs/`` contains detailed error messages
2. **Kill and restart**: If viewer is unresponsive, kill it and let OpenHCS create a new one
3. **Try different port**: If port conflicts occur, change the port in config
4. **Verify installation**: Ensure Napari and PyImageJ are installed correctly

Performance Characteristics
---------------------------

Startup Times
~~~~~~~~~~~~~

- **Single viewer**: ~2-5 seconds (depends on Napari import time)
- **Multiple viewers (sequential)**: N × 2-5 seconds
- **Multiple viewers (parallel)**: ~2-5 seconds (same as single!)

Memory Usage
~~~~~~~~~~~~

- **Per viewer process**: ~200-500 MB (Napari + Qt + NumPy)
- **ZMQ overhead**: Negligible (~1 MB per connection)

Throughput
~~~~~~~~~~

- **Image streaming**: Limited by ZMQ (typically >100 MB/s on localhost)
- **Bottleneck**: Usually Napari rendering, not network

See Also
--------

For more detailed information:

- :doc:`../architecture/viewer_streaming_architecture` - Architecture and implementation details
- :doc:`../api/runtime` - API reference for viewer classes
- :doc:`../configuration/streaming_config` - Configuration options

