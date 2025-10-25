OMERO Integration
=================

Complete server-side execution support for OpenHCS on OMERO servers with zero data transfer overhead.

Overview
--------

The OMERO integration enables running OpenHCS pipelines directly on OMERO servers, processing data where it lives without downloading to local machines. This eliminates data transfer bottlenecks for large high-content screening datasets.

**Key Features:**

- **Virtual Backend**: On-demand filename generation from OMERO plate structure
- **Native Metadata**: Direct OMERO API queries with per-plate caching
- **Multiprocessing-Safe**: Connection management that works across process boundaries
- **Automatic Instance Management**: Auto-detect, connect, and start OMERO via Docker
- **Transparent File Handling**: JSON/CSV results saved as OMERO FileAnnotations
- **Zero-Copy Access**: Server-side execution eliminates data transfer

Quick Start
-----------

Installation
~~~~~~~~~~~~

.. code-block:: bash

   # Install OpenHCS with OMERO support
   pip install "openhcs[omero]"
   
   # Or install OMERO dependencies separately
   pip install omero-py

Start OMERO Server
~~~~~~~~~~~~~~~~~~

Using Docker Compose (automatic via instance manager):

.. code-block:: bash

   cd openhcs/omero
   docker-compose up -d
   ./wait_for_omero.sh

Or manually:

.. code-block:: bash

   docker run -d --name omero-server \
     -p 4064:4064 -p 4080:4080 \
     -e OMERO_ROOT_PASSWORD=openhcs \
     openmicroscopy/omero-server-standalone

Basic Usage
~~~~~~~~~~~

.. code-block:: python

   from openhcs.runtime.omero_instance_manager import OMEROInstanceManager
   from openhcs.io.omero_local import OMEROLocalBackend
   from openhcs.core.orchestrator import PipelineOrchestrator
   
   # Connect to OMERO
   with OMEROInstanceManager() as manager:
       conn = manager.get_connection()
       
       # Create backend
       backend = OMEROLocalBackend(omero_conn=conn)
       
       # Run pipeline on OMERO plate
       orchestrator = PipelineOrchestrator(
           plate_paths=[123],  # OMERO plate ID
           steps=pipeline_steps,
           global_config=global_config
       )
       
       orchestrator.run()

Configuration
-------------

Connection Settings
~~~~~~~~~~~~~~~~~~~

Default OMERO connection settings:

.. code-block:: python

   DEFAULT_OMERO_HOST = 'localhost'
   DEFAULT_OMERO_PORT = 4064
   DEFAULT_OMERO_WEB_PORT = 4080
   DEFAULT_OMERO_USER = 'openhcs'
   DEFAULT_OMERO_PASSWORD = 'openhcs'

Custom connection:

.. code-block:: python

   from openhcs.runtime.omero_instance_manager import OMEROInstanceManager
   
   manager = OMEROInstanceManager(
       host='omero-server.example.com',
       port=4064,
       username='myuser',
       password='mypassword'
   )

Docker Compose
~~~~~~~~~~~~~~

The OMERO module includes a Docker Compose configuration:

.. code-block:: yaml

   # openhcs/omero/docker-compose.yml
   services:
     omero-server:
       image: openmicroscopy/omero-server-standalone
       ports:
         - "4064:4064"  # OMERO server
         - "4080:4080"  # OMERO.web
       environment:
         OMERO_ROOT_PASSWORD: openhcs

Automatic Instance Management
------------------------------

The instance manager provides automatic OMERO lifecycle management:

Auto-Detection
~~~~~~~~~~~~~~

.. code-block:: python

   from openhcs.runtime.omero_instance_manager import OMEROInstanceManager
   
   manager = OMEROInstanceManager()
   
   if manager.is_running():
       print("OMERO is running")
   else:
       print("OMERO is not running")

Auto-Connection
~~~~~~~~~~~~~~~

.. code-block:: python

   # Try to connect (with timeout)
   if manager.connect(timeout=10):
       print(f"Connected to OMERO at {manager.host}:{manager.port}")
       conn = manager.get_connection()
   else:
       print("Failed to connect")

Auto-Start
~~~~~~~~~~

.. code-block:: python

   # Start OMERO if not running
   if not manager.is_running():
       manager.start_via_docker_compose()
       manager.wait_for_ready(timeout=60)
   
   # Now connect
   manager.connect()

Context Manager
~~~~~~~~~~~~~~~

.. code-block:: python

   # Automatic cleanup
   with OMEROInstanceManager() as manager:
       conn = manager.get_connection()
       # Use connection
       # Automatic cleanup on exit

Server-Side Execution
---------------------

The OMERO backend combines with the ZMQ execution system for true server-side processing:

Local Client, Remote Server
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
   
   # Client runs on local machine
   client = ZMQExecutionClient(
       host='omero-server.example.com',
       port=7777
   )
   
   # Execute pipeline on OMERO server
   response = client.execute_pipeline(
       plate_id=123,  # OMERO plate ID
       pipeline_steps=steps,
       global_config=config
   )
   
   # Processing happens server-side
   # Results streamed back to local client
   # Zero data transfer overhead

This pattern eliminates data transfer bottlenecks by processing data where it lives.

Data Import
-----------

Import Test Data
~~~~~~~~~~~~~~~~

The integration tests in ``tests/integration/test_main.py`` demonstrate the complete workflow for uploading data to OMERO and running pipelines. See :doc:`../development/omero_testing` for details.

Import from ImageXpress
~~~~~~~~~~~~~~~~~~~~~~~

Use the OMERO CLI or OMERO.web interface to import ImageXpress plates. OpenHCS will automatically detect the format when processing via ``/omero/plate_{plate_id}`` paths.

List Plates
~~~~~~~~~~~

.. code-block:: python

   from openhcs.omero import OMEROInstanceManager
   
   with OMEROInstanceManager() as manager:
       conn = manager.get_connection()
       
       # List all plates
       plates = conn.getObjects('Plate')
       for plate in plates:
           print(f"Plate {plate.getId()}: {plate.getName()}")

Testing
-------

Integration Tests
~~~~~~~~~~~~~~~~~

OMERO tests are integrated into the main test suite:

.. code-block:: bash

   # Run all tests including OMERO
   pytest tests/integration/test_main.py -v
   
   # Run only OMERO tests
   pytest tests/integration/test_main.py -k omero -v

The test suite automatically:

1. Detects if OMERO is running
2. Skips OMERO tests if not available
3. Imports test data
4. Runs full pipeline execution
5. Opens browser to view results

Running Tests
~~~~~~~~~~~~~

.. code-block:: bash

   # Run OMERO integration tests
   pytest tests/integration/test_main.py --it-microscopes=OMERO --it-backends=disk -v

   # See full testing guide
   # docs/source/development/omero_testing.rst

Troubleshooting
---------------

Connection Issues
~~~~~~~~~~~~~~~~~

**Problem**: Cannot connect to OMERO server

**Solutions**:

1. Check OMERO is running:

   .. code-block:: bash
   
      docker ps | grep omero

2. Check port is accessible:

   .. code-block:: bash
   
      nc -zv localhost 4064

3. Check credentials:

   .. code-block:: python
   
      manager = OMEROInstanceManager(
          username='openhcs',
          password='openhcs'
      )

Import Failures
~~~~~~~~~~~~~~~

**Problem**: Plate import fails

**Solutions**:

1. Check file permissions
2. Verify plate directory structure
3. Check OMERO disk space
4. Review OMERO logs:

   .. code-block:: bash
   
      docker logs omero-server

Performance Issues
~~~~~~~~~~~~~~~~~~

**Problem**: Slow OMERO operations

**Solutions**:

1. Use server-side execution (ZMQ pattern)
2. Enable metadata caching (automatic)
3. Increase OMERO memory:

   .. code-block:: yaml
   
      # docker-compose.yml
      environment:
        OMERO_JVM_MEMORY: 4096m

Advanced Usage
--------------

Custom Metadata Handlers
~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   from openhcs.microscopes.omero import OMEROMetadataHandler
   
   class CustomOMEROHandler(OMEROMetadataHandler):
       def get_custom_metadata(self, plate_id: int) -> Dict:
           """Custom metadata extraction."""
           # Your custom logic
           pass

FileAnnotation Handling
~~~~~~~~~~~~~~~~~~~~~~~

Analysis results (JSON/CSV) are automatically saved as OMERO FileAnnotations:

.. code-block:: python

   # This automatically becomes a FileAnnotation
   filemanager.save(
       results_dict,
       'analysis_results.json',
       backend='omero'
   )
   
   # Attached to appropriate OMERO object (plate/well/image)

Plate Structure Caching
~~~~~~~~~~~~~~~~~~~~~~~

Metadata is cached at the plate level for performance:

.. code-block:: python

   # First access: Queries OMERO
   channels = handler.get_channel_values(plate_id)
   
   # Subsequent accesses: From cache
   z_values = handler.get_z_index_values(plate_id)
   t_values = handler.get_timepoint_values(plate_id)

See Also
--------

- :doc:`../architecture/omero_backend_system` - OMERO backend architecture
- :doc:`../architecture/zmq_execution_system` - ZMQ execution system
- `OMERO Documentation <https://docs.openmicroscopy.org/>`_ - Official OMERO docs

