objectstate
===========

**Generic lazy dataclass configuration framework with dual-axis inheritance**

Overview
--------

``objectstate`` is a Python framework for managing hierarchical configuration using lazy dataclasses with dual-axis inheritance. It provides a clean, type-safe way to handle configuration across different contexts (global, pipeline, step) without manual parameter passing.

Key Features
------------

* **Lazy Dataclass Factory**: Dynamically create dataclasses with lazy field resolution
* **Dual-Axis Inheritance**:

  * X-Axis: Context hierarchy (Step → Pipeline → Global)
  * Y-Axis: Sibling inheritance within same context

* **Contextvars-Based**: Uses Python's ``contextvars`` for clean context management
* **UI Integration**: Placeholder text generation for configuration forms
* **Thread-Safe**: Thread-local global configuration storage
* **100% Generic**: No application-specific dependencies
* **Pure Stdlib**: No external dependencies

Installation
------------

.. code-block:: bash

   pip install objectstate

Quick Example
-------------

.. code-block:: python

   from dataclasses import dataclass
   from objectstate import (
       set_base_config_type,
       LazyDataclassFactory,
       config_context,
   )

   # Define your base configuration
   @dataclass
   class GlobalConfig:
       output_dir: str = "/tmp"
       num_workers: int = 4
       debug: bool = False

   # Initialize framework
   set_base_config_type(GlobalConfig)

   # Create lazy version
   LazyGlobalConfig = LazyDataclassFactory.make_lazy_simple(GlobalConfig)

   # Use with context
   global_cfg = GlobalConfig(output_dir="/data", num_workers=8)

   with config_context(global_cfg):
       lazy_cfg = LazyGlobalConfig()
       print(lazy_cfg.output_dir)  # "/data" (resolved from context)
       print(lazy_cfg.debug)       # False (inherited from defaults)

Why objectstate?
----------------

Before (Manual parameter passing)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   def process_step(data, output_dir, num_workers, debug, ...):
       # Pass 20+ parameters through every function
       result = sub_process(data, output_dir, num_workers, debug, ...)
       return result

   def sub_process(data, output_dir, num_workers, debug, ...):
       # Repeat parameter declarations everywhere
       ...

After (objectstate)
~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   @dataclass
   class StepConfig:
       output_dir: str = None
       num_workers: int = None
       debug: bool = None

   def process_step(data, config: LazyStepConfig):
       # Config fields resolve automatically from context
       print(config.output_dir)  # Resolved from context hierarchy
       result = sub_process(data, config)
       return result

Requirements
------------

* Python 3.10+
* No external dependencies (pure stdlib)

Contents
--------

.. toctree::
   :maxdepth: 2
   :caption: User Guide

   quickstart
   architecture
   state_management
   undo_redo
   examples/index

.. toctree::
   :maxdepth: 2
   :caption: API Reference

   api/modules

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`
