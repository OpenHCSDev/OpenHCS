OMERO Integration Testing
==========================

This guide explains how to run OpenHCS integration tests with OMERO.

Quick Start
-----------

**TL;DR:** Start OMERO, run the test.

.. code-block:: bash

   # 1. Start OMERO
   cd openhcs/omero
   docker-compose up -d
   ./wait_for_omero.sh

   # 2. Run OMERO integration tests
   cd ../..  # Back to project root
   pytest tests/integration/test_main.py --it-microscopes=OMERO --it-backends=disk -v

Prerequisites
-------------

1. **Docker** - For running OMERO server
2. **Python 3.12+** - With OpenHCS installed
3. **OMERO Python dependencies**:

   .. code-block:: bash

      pip install "openhcs[omero]"
      # Or separately:
      pip install omero-py

Step-by-Step Setup
-------------------

1. Start OMERO Server
~~~~~~~~~~~~~~~~~~~~~

The OMERO server runs in Docker containers (PostgreSQL + OMERO.server + OMERO.web):

.. code-block:: bash

   # Navigate to OMERO directory
   cd openhcs/omero

   # Start all services
   docker-compose up -d

   # Wait for OMERO to be ready (~30 seconds)
   ./wait_for_omero.sh

**What this does:**

- Starts PostgreSQL database (port 5432, internal only)
- Starts OMERO.server (port 4064)
- Starts OMERO.web (port 4080)
- Uses password: ``openhcs`` (not ``omero-root-password``)

**Check status:**

.. code-block:: bash

   docker-compose ps

All services should show "Up".

**View OMERO.web:**

.. code-block:: bash

   # Open in browser
   open http://localhost:4080

   # Login credentials
   # Username: root
   # Password: openhcs

2. Run Integration Tests
~~~~~~~~~~~~~~~~~~~~~~~~~

The integration tests automatically:

1. Generate synthetic microscopy data
2. Upload it to OMERO as a Plate
3. Run the full OpenHCS pipeline
4. Save results back to OMERO as FileAnnotations
5. Open browser to view results

.. code-block:: bash

   # Navigate back to project root
   cd ../..  # From openhcs/omero back to project root

   # Run OMERO integration tests
   pytest tests/integration/test_main.py --it-microscopes=OMERO --it-backends=disk -v

   # Run with more detail
   pytest tests/integration/test_main.py --it-microscopes=OMERO --it-backends=disk -v -s

   # Run specific test variant
   pytest tests/integration/test_main.py::test_main[disk-OMERO-3d-multiprocessing-direct] -v -s

**Test parameters:**

- ``--it-microscopes=OMERO`` - Test OMERO backend
- ``--it-backends=disk`` - Use disk backend for output (can also use ``zarr``)
- ``-v`` - Verbose output
- ``-s`` - Show print statements (useful for debugging)

What the Test Does
------------------

Fixture Setup
~~~~~~~~~~~~~

The ``omero_plate_data`` fixture (in ``tests/integration/helpers/fixture_utils.py``):

1. Connects to OMERO server
2. Generates synthetic ImageXpress data (2x2 grid, 2 channels, 3 z-planes, 4 wells)
3. Uploads to OMERO as a proper HCS Plate structure
4. Stores metadata (parser type, microscope type, **grid dimensions**)
5. Returns plate ID

Test Execution
~~~~~~~~~~~~~~

The ``test_main`` function (in ``tests/integration/test_main.py``):

1. Creates pipeline with cell counting and segmentation
2. Executes on OMERO plate using ``/omero/plate_{plate_id}`` path
3. Saves results as OMERO FileAnnotations (JSON, CSV, TXT)
4. Validates output

Cleanup
~~~~~~~

- Plates are **NOT** deleted (left in OMERO for inspection)
- Connection is closed

Expected Output
---------------

**Expected log messages:**

.. code-block:: text

   INFO - Found grid_dimensions (2, 2) in OMERO metadata
   INFO - Attached A01_cell_counts.json as FileAnnotation to plate 123
   INFO - Attached A01_cell_counts_details.csv as FileAnnotation to plate 123
   INFO - Attached A01_segmentation_masks_segmentation_summary.txt as FileAnnotation to plate 123
   ...
   PASSED

**Browser opens automatically** to show results in OMERO.web.

Troubleshooting
---------------

OMERO Won't Start
~~~~~~~~~~~~~~~~~

.. code-block:: bash

   # Check Docker status
   cd openhcs/omero
   docker-compose ps

   # View logs
   docker-compose logs omeroserver
   docker-compose logs omeroweb

   # Restart services
   docker-compose restart

   # Nuclear option: full reset (WARNING: Deletes all data!)
   docker-compose down -v
   docker-compose up -d
   ./wait_for_omero.sh

Connection Refused
~~~~~~~~~~~~~~~~~~

**Problem:** Test can't connect to OMERO

**Solution:**

.. code-block:: bash

   # Make sure OMERO is running
   cd openhcs/omero
   docker-compose ps

   # Check if ports are accessible
   nc -zv localhost 4064  # OMERO.server
   nc -zv localhost 4080  # OMERO.web

   # Check firewall/Docker networking
   docker network ls
   docker network inspect omero_omero

Test Hangs
~~~~~~~~~~

**Problem:** Test starts but never completes

**Possible causes:**

1. OMERO server is slow (wait longer)
2. Multiprocessing deadlock (check logs)
3. Connection not being closed properly

**Solution:**

.. code-block:: bash

   # Kill test with Ctrl+C

   # Check OMERO logs
   cd openhcs/omero
   docker-compose logs --tail=100 omeroserver

   # Restart OMERO
   docker-compose restart

Grid Dimensions Not Found
~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem:** ``WARNING - Grid dimensions not found in OMERO metadata``

**Cause:** Old test data uploaded without grid dimensions metadata

**Solution:**

.. code-block:: bash

   # Delete old plates via OMERO.web
   open http://localhost:4080
   # Login, delete old test plates

   # Or reset OMERO completely
   cd openhcs/omero
   docker-compose down -v
   docker-compose up -d
   ./wait_for_omero.sh

Import Errors
~~~~~~~~~~~~~

**Problem:** ``ModuleNotFoundError: No module named 'omero'``

**Solution:**

.. code-block:: bash

   # Install OMERO dependencies
   pip install omero-py

   # Or install with all extras
   pip install -e ".[omero]"

Configuration
-------------

OMERO Connection Settings
~~~~~~~~~~~~~~~~~~~~~~~~~~

**Default values** (in ``openhcs/omero/docker-compose.yml``):

- Host: ``localhost``
- Port: ``4064``
- User: ``root``
- Password: ``openhcs``
- Web Port: ``4080``

**Override via environment variables:**

.. code-block:: bash

   export OMERO_HOST=localhost
   export OMERO_PORT=4064
   export OMERO_USER=root
   export OMERO_PASSWORD=openhcs
   export OMERO_WEB_HOST=localhost
   export OMERO_WEB_PORT=4080

Test Parameters
~~~~~~~~~~~~~~~

**Available test variants** (via pytest parametrization):

- Microscopes: ``ImageXpress``, ``OperaPhenix``, ``OMERO``
- Backends: ``disk``, ``zarr``
- Dimensions: ``2d``, ``3d``
- Execution modes: ``threading``, ``multiprocessing``
- ZMQ modes: ``direct``, ``zmq``

**Run specific combinations:**

.. code-block:: bash

   # Only OMERO with disk backend
   pytest tests/integration/test_main.py --it-microscopes=OMERO --it-backends=disk -v

   # OMERO with zarr backend
   pytest tests/integration/test_main.py --it-microscopes=OMERO --it-backends=zarr -v

   # All OMERO tests (disk + zarr)
   pytest tests/integration/test_main.py --it-microscopes=OMERO -v

Manual Testing
--------------

Import Test Data Manually
~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: bash

   # Generate and upload synthetic plate
   python examples/import_test_data.py

This creates a plate with 4 wells (A01, A02, B01, B02) and opens OMERO.web to view it.

Run Pipeline on Existing Plate
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   from openhcs.omero import OMEROInstanceManager
   from openhcs.io.omero_local import OMEROLocalBackend
   from openhcs.core.orchestrator import Orchestrator
   from openhcs.core.pipeline import Pipeline

   # Connect to OMERO
   with OMEROInstanceManager() as manager:
       # Create pipeline
       pipeline = Pipeline(...)
       
       # Execute on plate (use plate ID from OMERO.web)
       orchestrator = Orchestrator(
           plate_dir=f"/omero/plate_123",  # Replace 123 with actual plate ID
           pipeline=pipeline,
           backend='omero_local'
       )
       orchestrator.run()

Architecture Notes
------------------

Why Grid Dimensions Are Stored as Metadata
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem:** OMERO doesn't natively store grid dimensions (rows × cols of sites per well).

**Solution:** OpenHCS stores grid dimensions in the plate's MapAnnotation:

- Key: ``openhcs.grid_dimensions``
- Value: ``"rows,cols"`` (e.g., ``"2,2"``)
- Namespace: ``openhcs.metadata``

**This is set during upload:**

.. code-block:: python

   # In examples/import_test_data.py
   upload_plate_to_omero(
       conn,
       data_dir,
       plate_name="Test_Plate",
       microscope_format='ImageXpress',
       grid_dimensions=(2, 2)  # Stored as metadata
   )

**And read during processing:**

.. code-block:: python

   # In openhcs/microscopes/omero.py - OMEROMetadataHandler.get_grid_dimensions()
   for ann in plate.listAnnotations():
       if ann.getNs() == "openhcs.metadata":
           for nv in ann.getMapValue():
               if nv.name == "openhcs.grid_dimensions":
                   rows, cols = map(int, nv.value.split(','))
                   return (rows, cols)

Virtual Filesystem Paths
~~~~~~~~~~~~~~~~~~~~~~~~~

OMERO uses virtual paths (no real files on disk):

- Format: ``/omero/plate_{plate_id}/well_{well_id}/site_{site_id}/...``
- Example: ``/omero/plate_123/A01_s001_w1_z001.tif``

These paths are generated on-demand by ``OMEROFilenameParser`` based on OMERO's plate structure.

Related Documentation
---------------------

- **OMERO Integration Guide**: :doc:`../guides/omero_integration`
- **OMERO Backend Architecture**: :doc:`../architecture/omero_backend_system`
- **Integration Test Helpers**: ``tests/integration/helpers/fixture_utils.py``
- **Main Test File**: ``tests/integration/test_main.py``

