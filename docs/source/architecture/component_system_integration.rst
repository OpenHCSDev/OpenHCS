Component System Integration
============================

Overview
--------

OpenHCS subsystems consume component information through standardized interfaces driven by component configuration. This eliminates hardcoded assumptions about component names and enables consistent behavior across orchestrator, compiler, pattern discovery, UI, and cache systems.

.. code-block:: python

   # All subsystems use the same component interfaces
   from openhcs.constants import AllComponents, VariableComponents, GroupBy, MULTIPROCESSING_AXIS

   # Orchestrator caches all components
   orchestrator.cache_component_keys(list(AllComponents))

   # Compiler partitions by multiprocessing axis
   axis_values = orchestrator.get_component_keys(MULTIPROCESSING_AXIS)

   # UI populates with user-selectable components
   component_selector.populate_options(list(VariableComponents))

Component configuration serves as the single source of truth for dimensional structure across all subsystems.

Lazy Export System
------------------

Component enums are created dynamically when first accessed to avoid circular imports and reflect current configuration.

.. code-block:: python

   # openhcs/constants/constants.py
   def __getattr__(name):
       """Lazy enum creation."""
       if name in ('AllComponents', 'VariableComponents', 'GroupBy'):
           all_components, vc, gb = _create_enums()
           globals()['AllComponents'] = all_components
           globals()['VariableComponents'] = vc
           globals()['GroupBy'] = gb
           return globals()[name]
       raise AttributeError(f"module '{__name__}' has no attribute '{name}'")

This ensures enums reflect the current component configuration and are created only when needed.

Orchestrator Integration
-----------------------

The orchestrator uses AllComponents for caching and provides component keys to all subsystems.

.. code-block:: python

   # Orchestrator caches all components for fast access
   orchestrator.cache_component_keys(list(AllComponents))

   # Subsystems request component keys generically
   axis_values = orchestrator.get_component_keys(MULTIPROCESSING_AXIS)
   available_channels = orchestrator.get_component_keys(VariableComponents.CHANNEL)

This provides consistent component key resolution across all subsystems.

Compiler Integration
-------------------

The compiler uses MULTIPROCESSING_AXIS for dynamic task partitioning.

.. code-block:: python

   # Compiler partitions tasks by multiprocessing axis
   from openhcs.constants import MULTIPROCESSING_AXIS

   axis_name = MULTIPROCESSING_AXIS.value
   filter_kwargs = {f"{axis_name}_filter": axis_values[:5]}
   compiled_contexts = PipelineCompiler.compile_pipelines(
       orchestrator, pipeline_definition, **filter_kwargs
   )

This enables the same compilation logic to work with any multiprocessing axis.

UI Integration
--------------

UI components populate dynamically with user-selectable components.

.. code-block:: python

   # UI populates with user-selectable components
   component_options = list(VariableComponents)
   groupby_options = list(GroupBy)

   # Component selection dialog uses current group_by
   available_components = orchestrator.get_component_keys(self.current_group_by)

   # Dynamic component type handling
   component_type = self.current_group_by.value
   display_name = self._get_component_display_name(selected_component)

This ensures UI components adapt to the available component structure dynamically.

**Common Gotchas**:

- Don't use ``GroupBy.NONE`` with dict patterns - validation will fail
- Component keys are cached on initialization - call ``clear_component_cache()`` if input directory changes
- Dict pattern keys must match actual component values, not enum names
