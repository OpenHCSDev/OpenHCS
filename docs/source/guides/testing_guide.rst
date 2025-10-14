.. _testing_guide:

======================
Testing Guide
======================

This guide covers how to run OpenHCS integration tests with different configurations, including visualizers (Napari/Fiji) and OMERO backend testing.

VSCode Test Discovery
=====================

VSCode is configured to discover **all test variants** including visualizers and OMERO tests. This allows you to run specific test combinations without memorizing command-line arguments.

Available Test Variants
-----------------------

The test menu will show combinations of:

- **Microscopes**: ``ImageXpress``, ``OperaPhenix``, ``OMERO``
- **Backends**: ``disk``, ``zarr``
- **Data Types**: ``3d`` (default), ``2d`` (if enabled)
- **Execution Modes**: ``multiprocessing`` (default), ``threading`` (if enabled)
- **ZMQ Modes**: ``direct`` (default), ``zmq`` (if enabled)
- **Visualizers**: ``none``, ``napari``, ``fiji``, ``napari+fiji``

Example test IDs you'll see::

    test_main[disk-ImageXpress-3d-multiprocessing-direct-none]
    test_main[disk-ImageXpress-3d-multiprocessing-direct-napari]
    test_main[disk-ImageXpress-3d-multiprocessing-direct-fiji]
    test_main[disk-ImageXpress-3d-multiprocessing-direct-napari+fiji]
    test_main[disk-OMERO-3d-multiprocessing-direct-none]
    test_main[zarr-OperaPhenix-3d-multiprocessing-direct-napari]

CI Test Configuration
=====================

**CI runs a subset of tests** to keep build times reasonable:

- **Microscopes**: ``ImageXpress``, ``OperaPhenix`` (OMERO excluded)
- **Backends**: ``disk``, ``zarr``
- **Data Types**: ``3d`` only
- **Execution Modes**: ``multiprocessing`` only
- **Visualizers**: ``none`` only (Napari/Fiji excluded)

This means **Napari, Fiji, and OMERO tests are VSCode-only** and won't run in CI.

Command-Line Testing
=====================

Basic Test Execution
--------------------

Run default tests (same as CI)::

    pytest tests/integration/test_main.py

Testing with Visualizers
-------------------------

**Legacy flags** (still supported)::

    pytest tests/integration/test_main.py --enable-napari
    pytest tests/integration/test_main.py --enable-fiji
    pytest tests/integration/test_main.py --enable-napari --enable-fiji

**New parametrized approach** (recommended)::

    # Test with Napari only
    pytest tests/integration/test_main.py --it-visualizers=napari

    # Test with Fiji only
    pytest tests/integration/test_main.py --it-visualizers=fiji

    # Test with both Napari and Fiji
    pytest tests/integration/test_main.py --it-visualizers=napari+fiji

    # Test with all visualizer combinations
    pytest tests/integration/test_main.py --it-visualizers=none,napari,fiji,napari+fiji

Testing with OMERO
-------------------

Ensure OMERO is running first::

    docker-compose up -d

Run OMERO tests::

    # Basic OMERO tests
    pytest tests/integration/test_main.py --it-microscopes=OMERO

    # OMERO tests with Napari
    pytest tests/integration/test_main.py --it-microscopes=OMERO --it-visualizers=napari

Testing Specific Combinations
------------------------------

::

    # ImageXpress + disk backend + Napari
    pytest tests/integration/test_main.py \
        --it-microscopes=ImageXpress \
        --it-backends=disk \
        --it-visualizers=napari

    # All microscopes + zarr backend + Fiji
    pytest tests/integration/test_main.py \
        --it-microscopes=ImageXpress,OperaPhenix,OMERO \
        --it-backends=zarr \
        --it-visualizers=fiji

    # Full coverage (all combinations)
    pytest tests/integration/test_main.py \
        --it-microscopes=all \
        --it-backends=all \
        --it-dims=all \
        --it-exec-mode=all \
        --it-visualizers=all

Test Parameters Reference
==========================

``--it-microscopes``
--------------------

- **Default**: ``ImageXpress,OperaPhenix``
- **Options**: ``ImageXpress``, ``OperaPhenix``, ``OMERO``, ``all``
- **Example**: ``--it-microscopes=ImageXpress,OMERO``

``--it-backends``
-----------------

- **Default**: ``disk,zarr``
- **Options**: ``disk``, ``zarr``, ``all``
- **Example**: ``--it-backends=disk``

``--it-dims``
-------------

- **Default**: ``3d``
- **Options**: ``2d``, ``3d``, ``all``
- **Example**: ``--it-dims=all``

``--it-exec-mode``
------------------

- **Default**: ``multiprocessing``
- **Options**: ``threading``, ``multiprocessing``, ``all``
- **Example**: ``--it-exec-mode=all``

``--it-zmq-mode``
-----------------

- **Default**: ``direct``
- **Options**: ``direct``, ``zmq``, ``all``
- **Example**: ``--it-zmq-mode=zmq``

``--it-visualizers``
--------------------

- **Default**: ``none``
- **Options**: ``none``, ``napari``, ``fiji``, ``napari+fiji``, ``all``
- **Example**: ``--it-visualizers=napari,fiji``

Environment Variables
=====================

You can set defaults using environment variables::

    export IT_MICROSCOPES="ImageXpress,OMERO"
    export IT_BACKENDS="disk"
    export IT_VISUALIZERS="napari"
    pytest tests/integration/test_main.py

Available environment variables:

- ``IT_MICROSCOPES``
- ``IT_BACKENDS``
- ``IT_DIMS``
- ``IT_EXEC_MODE``
- ``IT_ZMQ_MODE``
- ``IT_VISUALIZERS``

VSCode Configuration
====================

The ``.vscode/settings.json`` file configures test discovery:

.. code-block:: json

    {
        "python.testing.pytestArgs": [
            "tests",
            "--it-microscopes=ImageXpress,OperaPhenix,OMERO",
            "--it-backends=disk,zarr",
            "--it-exec-mode=multiprocessing",
            "--it-dims=3d",
            "--it-zmq-mode=direct",
            "--it-visualizers=none,napari,fiji,napari+fiji"
        ]
    }

**To customize VSCode test discovery**, edit this file to include/exclude specific test variants.

Tips and Best Practices
========================

1. **Use VSCode test menu** for quick access to specific test combinations
2. **Use command-line** for custom combinations not in VSCode menu
3. **OMERO tests require OMERO server** - start with ``docker-compose up -d``
4. **Visualizer tests are interactive** - they open viewer windows
5. **CI only runs fast tests** - Napari/Fiji/OMERO are VSCode-only
6. **Legacy flags still work** - ``--enable-napari`` and ``--enable-fiji`` are supported

Troubleshooting
===============

OMERO tests skipped
-------------------

**Error**::

    OMERO server not available - skipping OMERO tests

**Solution**: Start OMERO with ``docker-compose up -d``

Napari/Fiji tests not showing in VSCode
----------------------------------------

**Solution**: Reload VSCode window or refresh test discovery

Too many test variants in VSCode
---------------------------------

**Solution**: Edit ``.vscode/settings.json`` to reduce ``--it-visualizers`` options

CI running visualizer tests
----------------------------

**Solution**: CI configuration explicitly excludes visualizers - check ``.github/workflows/integration-tests.yml``

See Also
========

- :doc:`napari_viewer_management` - Napari viewer lifecycle and configuration
- :doc:`fiji_viewer_management` - Fiji viewer lifecycle and configuration
- :doc:`omero_integration` - OMERO backend integration guide

