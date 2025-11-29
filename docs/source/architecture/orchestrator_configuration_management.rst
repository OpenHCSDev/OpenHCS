Orchestrator Configuration Management
=====================================

**Pipeline-specific configuration with automatic context management and sibling inheritance preservation.**

*Status: STABLE*
*Module: openhcs.core.orchestrator.orchestrator*

The Problem: Configuration Synchronization Complexity
------------------------------------------------------

Pipelines need to override global configuration defaults (e.g., use a specific GPU, different memory backend) without affecting other pipelines. This requires synchronizing pipeline-specific config to thread-local context so that steps can access it. Without automatic synchronization, developers must manually call sync methods scattered throughout the code, leading to bugs where config changes aren't propagated. Additionally, serialization needs fully-resolved config (no None values), while UI operations need inheritance-preserving config (None values indicate "use parent default").

The Solution: Automatic Context Sync with Dual-Mode Access
-----------------------------------------------------------

The PipelineOrchestrator implements automatic synchronization: whenever pipeline config changes, it immediately updates thread-local context. Additionally, it provides dual-mode configuration access: one mode preserves None values for inheritance, another resolves all values for serialization. This eliminates manual sync calls and provides the right config format for each use case.

Overview
--------

The PipelineOrchestrator implements sophisticated configuration management that bridges the gap between global application defaults and pipeline-specific overrides. This system ensures that configuration changes are automatically synchronized to thread-local context while preserving the None values necessary for sibling inheritance.

The orchestrator provides three key configuration management capabilities:

1. **Automatic Context Synchronization** - Pipeline config changes automatically sync to thread-local storage
2. **Dual-Mode Configuration Access** - Support for both inheritance-preserving and serialization-ready config access
3. **Explicit Context Management** - Context managers for scoped configuration operations

Auto-Sync Configuration Pattern
-------------------------------

The orchestrator uses a property/setter pattern to automatically synchronize pipeline configuration changes to thread-local context, eliminating the need for manual synchronization calls.

.. literalinclude:: ../../../openhcs/core/orchestrator/orchestrator.py
   :language: python
   :pyobject: PipelineOrchestrator.pipeline_config
   :caption: Auto-sync property pattern from openhcs/core/orchestrator/orchestrator.py

**Benefits:**

- **Eliminates Manual Sync Calls** - No more scattered ``apply_pipeline_config()`` calls
- **Fail-Loud Behavior** - Immediate errors if context setup fails
- **Thread Safety** - Proper synchronization control during updates

Configuration Access Patterns
-----------------------------

The orchestrator provides unified configuration access with explicit control over inheritance behavior.

Dual-Mode Configuration Access
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../../../openhcs/core/orchestrator/orchestrator.py
   :language: python
   :pyobject: PipelineOrchestrator.get_effective_config
   :caption: Unified configuration access from openhcs/core/orchestrator/orchestrator.py

**Usage Patterns:**

.. code-block:: python

   # For UI operations (preserves sibling inheritance)
   ui_config = orchestrator.get_effective_config(for_serialization=False)
   
   # For compilation/storage (resolves all values)
   storage_config = orchestrator.get_effective_config(for_serialization=True)

Pure Function Configuration Merging
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Configuration merging is implemented as a pure function following OpenHCS stateless architecture principles:

.. literalinclude:: ../../../openhcs/core/orchestrator/orchestrator.py
   :language: python
   :pyobject: _create_merged_config
   :caption: Pure function for configuration merging from openhcs/core/orchestrator/orchestrator.py

**Design Principles:**

- **Stateless Function** - No side effects, explicit dependencies
- **Fail-Loud Behavior** - No defensive programming with getattr fallbacks
- **Code Reuse** - Eliminates duplication between methods

Context Manager Pattern
-----------------------

The orchestrator provides explicit context managers for operations requiring specific configuration contexts.

Scoped Configuration Context
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../../../openhcs/core/orchestrator/orchestrator.py
   :language: python
   :pyobject: PipelineOrchestrator.config_context
   :caption: Context manager for scoped operations from openhcs/core/orchestrator/orchestrator.py

**Usage Examples:**

.. code-block:: python

   # UI operations requiring sibling inheritance
   with orchestrator.config_context(for_serialization=False):
       editor = StepEditorWindow(step_data, orchestrator=orchestrator)
   
   # Compilation operations requiring resolved values
   with orchestrator.config_context(for_serialization=True):
       compiled_context = compile_pipeline_step(step, context)

Configuration Inheritance Preservation
--------------------------------------

The system carefully preserves None values in configuration objects to maintain sibling inheritance chains.

Merged vs Resolved Configuration
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Merged Configuration (for_serialization=False):**

- Preserves None values from pipeline config
- Enables sibling inheritance (materialization_defaults → path_planning)
- Used for UI operations and step editing

**Resolved Configuration (for_serialization=True):**

- Resolves all None values to concrete values
- Suitable for serialization and storage
- Used for compilation and pickling operations

**Critical Implementation Detail:**

.. code-block:: python

   # ✅ CORRECT: Preserves None values for sibling inheritance
   merged_config = _create_merged_config(pipeline_config, global_config)
   
   # ❌ INCORRECT: Resolves None values, breaking inheritance
   resolved_config = pipeline_config.to_base_config()

Integration with Lazy Configuration System
------------------------------------------

The orchestrator configuration management integrates seamlessly with the lazy configuration system documented in :doc:`dynamic_dataclass_factory`.

Thread-Local Context Flow
~~~~~~~~~~~~~~~~~~~~~~~~~

1. **Pipeline Config Assignment** - Auto-sync triggers when ``orchestrator.pipeline_config`` is set
2. **Merged Config Creation** - Pure function creates config preserving None values
3. **Thread-Local Update** - Merged config becomes active context for lazy resolution
4. **Sibling Inheritance** - Lazy configs resolve using preserved None values

**Resolution Chain:**

.. code-block:: python

   # Step-level lazy config resolution chain:
   
   # 1. Check step's explicit value
   step_value = step.materialization_config.output_dir_suffix
   if step_value is not None:
       return step_value
   
   # 2. Resolve from orchestrator context (merged config with None preservation)
   orchestrator_context = get_current_global_config(GlobalPipelineConfig)
   orchestrator_value = orchestrator_context.materialization_defaults.output_dir_suffix
   if orchestrator_value is not None:
       return orchestrator_value
   
   # 3. Sibling inheritance (materialization_defaults → path_planning)
   sibling_value = orchestrator_context.path_planning.output_dir_suffix
   return sibling_value

Benefits and Design Rationale
-----------------------------

**Architectural Benefits:**

- **Eliminates Code Duplication** - Single pure function for config merging
- **Explicit Dependencies** - Clear parameter-based function contracts
- **Fail-Loud Behavior** - Immediate errors instead of silent degradation
- **Stateless Design** - Pure functions with no hidden state

**User Experience Benefits:**

- **Automatic Synchronization** - No manual context management required
- **Preserved User Edits** - Sibling inheritance maintains user intentions
- **Explicit Scoping** - Context managers make dependencies clear

See Also
--------

- :doc:`dynamic_dataclass_factory` - Lazy configuration system that orchestrator integrates with
- :doc:`context_system` - Thread-local context management patterns
- :doc:`configuration_framework` - Configuration framework overview
