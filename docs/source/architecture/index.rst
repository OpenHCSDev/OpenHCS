======================
Architecture Reference
======================

Technical documentation of OpenHCS's architecture for developers who need to understand internal implementation details.

**Prerequisites**: :doc:`../concepts/index` | **Integration**: :doc:`../guides/index`

Core System Architecture
========================

Fundamental systems that define OpenHCS architecture.

.. toctree::
   :maxdepth: 1

   function_pattern_system
   function_registry_system
   pipeline_compilation_system
   special_io_system
   analysis_consolidation_system
   experimental_analysis_system
   dict_pattern_case_study

Configuration Systems
=====================

Lazy configuration, resolution, and field path detection.

.. toctree::
   :maxdepth: 1

   configuration_system_architecture
   lazy_class_system
   configuration_resolution
   orchestrator_configuration_management
   field_path_detection
   component_configuration_framework

Storage and Memory
==================

File management, memory types, and backend systems.

.. toctree::
   :maxdepth: 1

   storage_and_memory_system
   memory_type_system

System Integration
==================

How OpenHCS components work together and integrate with external systems.

.. toctree::
   :maxdepth: 1

   system_integration
   microscope_handler_integration
   ezstitcher_to_openhcs_evolution

Component Systems
================

Component validation, integration, and processing.

.. toctree::
   :maxdepth: 1

   component_validation_system
   component_system_integration
   component_processor_metaprogramming

Advanced Processing
==================

GPU management, multiprocessing, and performance optimization.

.. toctree::
   :maxdepth: 1

   multiprocessing_coordination_system
   gpu_resource_management
   compilation_system_detailed
   concurrency_model

Metaprogramming and Parsing
===========================

Dynamic code generation and parser systems.

.. toctree::
   :maxdepth: 1

   parser_metaprogramming_system
   pattern_detection_system

User Interface Systems
======================

TUI architecture and UI development patterns.

.. toctree::
   :maxdepth: 1

   tui_system
   code_ui_interconversion
   service-layer-architecture

Development Tools
=================

Practical tools for OpenHCS development workflows.

.. toctree::
   :maxdepth: 1

   step-editor-generalization

Quick Start Paths
==================

**New to OpenHCS?** Start with :doc:`function_pattern_system` → :doc:`configuration_system_architecture` → :doc:`storage_and_memory_system`

**Configuration Systems?** Focus on :doc:`lazy_class_system` → :doc:`configuration_resolution` → :doc:`field_path_detection`

**System Integration?** Jump to :doc:`system_integration` → :doc:`special_io_system` → :doc:`microscope_handler_integration`

**Performance Optimization?** Focus on :doc:`gpu_resource_management` → :doc:`compilation_system_detailed` → :doc:`multiprocessing_coordination_system`

**UI Development?** Begin with :doc:`tui_system` → :doc:`code_ui_interconversion` → :doc:`service-layer-architecture`
