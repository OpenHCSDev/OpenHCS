Welcome to OpenHCS Documentation
=================================

OpenHCS is a bioimage analysis platform for high-content screening datasets. It provides unified access to Python image processing libraries with automatic GPU acceleration and memory management for large-scale microscopy data analysis.

Overview
--------

OpenHCS addresses the computational challenges of high-content screening by providing:

- **Unified interface** to major Python image processing libraries (scikit-image, CuCIM, pyclesperanto)
- **Automatic GPU acceleration** with seamless memory type conversion
- **Scalable processing** for datasets ranging from single images to 100GB+ experiments
- **Microscope format compatibility** supporting multiple vendor platforms

Quick Start
-----------

.. code-block:: bash

    # Install OpenHCS
    pip install openhcs

    # Launch interactive interface
    openhcs-tui

For complete installation and basic examples, see :doc:`getting_started/getting_started`.

Core Capabilities
-----------------

**Library Integration**
  Seamless access to scikit-image, CuCIM, and pyclesperanto through unified 3D array interface

**GPU Acceleration**
  Automatic memory type conversion between NumPy, CuPy, PyTorch, and pyclesperanto arrays

**Scalable Processing**
  Parallel execution across wells and sites with intelligent memory management

**Format Compatibility**
  Support for multiple microscope platforms including ImageXpress and Opera Phenix

**Storage Flexibility**
  Virtual file system with memory, disk, and compressed Zarr backends

**Analysis Functions**
  Specialized tools for cell counting, neurite tracing, and morphological analysis

Documentation Structure
======================

**New to OpenHCS?** Follow this learning path:

1. **Getting Started**: :doc:`getting_started/getting_started` - Installation and basic examples
2. **Core Concepts**: :doc:`concepts/index` - Understanding pipelines, steps, and data organization
3. **Function Library**: :doc:`concepts/function_library` - Available processing functions and backends
4. **User Guide**: :doc:`user_guide/index` - Detailed usage patterns and workflows
5. **Integration Guides**: :doc:`guides/index` - System integration and advanced topics

**API Reference**: :doc:`api/index` - Class documentation and technical reference

.. toctree::
   :maxdepth: 2
   :caption: Getting Started

   getting_started/getting_started

.. toctree::
   :maxdepth: 2
   :caption: Core Concepts

   concepts/index

.. toctree::
   :maxdepth: 2
   :caption: User Guide

   user_guide/index

.. toctree::
   :maxdepth: 2
   :caption: Integration Guides

   guides/index

.. toctree::
   :maxdepth: 2
   :caption: API Reference

   api/index

.. toctree::
   :maxdepth: 2
   :caption: Architecture Reference

   architecture/index

.. toctree::
   :maxdepth: 2
   :caption: Development

   development/index

.. toctree::
   :maxdepth: 2
   :caption: Appendices

   appendices/index

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
