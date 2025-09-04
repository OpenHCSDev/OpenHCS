Context Management System
=========================

**Generic thread-local storage for global configuration context management.**

*Status: STABLE*
*Module: openhcs.core.context.global_config*

Overview
--------

Configuration systems require thread-safe context management to support concurrent processing while maintaining configuration isolation. The context management system provides generic thread-local storage that supports multiple global configuration types with automatic context switching.

.. code-block:: python

   # Generic context management for any configuration type
   set_current_global_config(GlobalPipelineConfig, config_instance)
   current_config = get_current_global_config(GlobalPipelineConfig)
   
   # Thread-safe isolation - each thread maintains separate context
   # Supports future extension to multiple global config types

This eliminates hardcoded context management while providing thread-safe configuration access for concurrent pipeline processing.

Generic Thread-Local Storage
-----------------------------

The system uses type-based context storage that automatically handles thread isolation without requiring explicit thread management.

.. literalinclude:: ../../../openhcs/core/context/global_config.py
   :language: python
   :lines: 13-26
   :caption: Generic thread-local storage for any global config type

The type-based approach enables multiple global configuration types to coexist while maintaining thread isolation automatically.

Context-Aware Operations
------------------------

The system provides decorators for operations that require active configuration context, ensuring proper context availability.

.. literalinclude:: ../../../openhcs/core/context/global_config.py
   :language: python
   :lines: 29-42
   :caption: Decorator to ensure config context is available for UI operations

This prevents context-dependent operations from executing without proper configuration setup.

Integration with Lazy Resolution
--------------------------------

The context management system integrates seamlessly with lazy configuration resolution to provide automatic field value lookup.

.. code-block:: python

   # Lazy field resolution uses context management automatically
   class LazyConfigResolver:
       def _resolve_field_value(self, field_name: str) -> Any:
           # Automatic context lookup through generic context management
           current_config = get_current_global_config(self._global_config_type)
           if current_config and hasattr(current_config, field_name):
               return getattr(current_config, field_name)
           return None

This enables lazy dataclasses to resolve field values from the current thread-local context without explicit context passing.

Orchestrator Context Management
------------------------------

The orchestrator automatically manages configuration context for pipeline execution with proper context switching.

.. code-block:: python

   class PipelineOrchestrator:
       def apply_pipeline_config(self, pipeline_config):
           """Apply pipeline configuration with automatic context management."""
           # Create merged configuration preserving None values
           effective_config = _create_merged_config(pipeline_config, self.global_config)
           
           # Set thread-local context for lazy resolution
           set_current_global_config(GlobalPipelineConfig, effective_config)
           
           # All subsequent operations use this context automatically
           logger.debug("Set thread-local context for pipeline execution")

This ensures that all pipeline operations have access to the correct configuration context without manual context passing.

Future Extensibility
--------------------

The generic design supports multiple global configuration domains simultaneously, enabling OpenHCS to expand into new functional areas.

Creating New Global Configuration Domains
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The system enables creation of entirely new global configuration domains using the same @auto_create_decorator pattern:

.. code-block:: python

   # Create new global configuration domain
   @auto_create_decorator
   @dataclass(frozen=True)
   class GlobalAnalysisConfig:
       default_statistical_method: str = "robust"
       confidence_interval: float = 0.95
       parallel_analysis: bool = True

   # Automatically generates @global_analysis_config decorator
   # Any dataclass can now inherit these fields:
   @global_analysis_config
   @dataclass(frozen=True)
   class ExperimentAnalysisConfig:
       experiment_id: str = "exp001"
       # Inherits default_statistical_method, confidence_interval, parallel_analysis

Multi-Domain Context Isolation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Each global configuration domain maintains independent thread-local context:

.. code-block:: python

   # Independent context management for different domains
   set_current_global_config(GlobalPipelineConfig, pipeline_config)
   set_current_global_config(GlobalAnalysisConfig, analysis_config)
   set_current_global_config(GlobalVisualizationConfig, viz_config)

   # Each domain maintains separate thread-local context
   pipeline_context = get_current_global_config(GlobalPipelineConfig)
   analysis_context = get_current_global_config(GlobalAnalysisConfig)
   viz_context = get_current_global_config(GlobalVisualizationConfig)

   # No cross-domain interference - each operates independently

The type-based approach enables multiple configuration domains to coexist with independent context management.

Thread Safety Guarantees
------------------------

The system provides automatic thread isolation without requiring explicit synchronization in user code.

.. code-block:: python

   # Thread A
   set_current_global_config(GlobalPipelineConfig, config_a)
   
   # Thread B (concurrent execution)
   set_current_global_config(GlobalPipelineConfig, config_b)
   
   # Each thread sees only its own configuration
   # No cross-thread interference or synchronization required

This enables concurrent pipeline processing with independent configuration contexts, supporting the multiprocessing orchestration system.

Context Synchronization Patterns
--------------------------------
Thread-local context must stay synchronized with UI state during parameter operations.

Form State vs Context State
~~~~~~~~~~~~~~~~~~~~~~~~~~~
Forms maintain internal parameter state separate from thread-local context, requiring explicit synchronization.

:py:attr:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.parameters` stores internal form state, while :py:class:`~openhcs.core.context.global_config._global_config_contexts` maintains thread-local context. These two states can diverge during form operations, requiring careful synchronization to prevent placeholder resolution bugs.

Reset-Specific Context Updates
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Reset operations require immediate context updates to prevent placeholder resolution bugs.

:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.reset_parameter` uses :py:func:`~dataclasses.replace` and :py:func:`~openhcs.core.context.global_config.set_current_global_config` to update context when fields are reset to None. This ensures that subsequent placeholder generation resolves against the correct context instead of stale values.

Context Update Triggers
~~~~~~~~~~~~~~~~~~~~~~
Context updates occur during specific lifecycle events, not continuous synchronization.

**Save Operations:**
Configuration save operations update context using :py:func:`~openhcs.core.context.global_config.set_current_global_config` with orchestrator effective config.

**Reset Operations:**
Field reset operations update context using :py:func:`~dataclasses.replace` to set reset fields to None in the current context.

Context Isolation Patterns
--------------------------
Different UI contexts require different thread-local context configurations.

Step Editor Context Isolation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Step editors show step configurations with isolated context that reflects their parent pipeline configuration without affecting other UI components.

:py:meth:`~openhcs.core.lazy_config.LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy` creates step-specific lazy configs with custom context providers. The `context_provider` parameter allows step editors to resolve against their parent pipeline config instead of the global thread-local context. This enables step forms to show "Pipeline default: X" values that reflect their specific pipeline's configuration, even when multiple pipelines are open simultaneously.

**Step Context Provider Pattern:**
Step editors pass a lambda that returns their parent pipeline config: `lambda: parent_pipeline_config`. This creates a resolution chain where step fields resolve against their specific pipeline, then fall back to global defaults, without interfering with other UI components that use different context providers.

Pipeline Editor Context
~~~~~~~~~~~~~~~~~~~~~~~
Pipeline editors (plate manager style) handle pipeline-level configuration editing using standard thread-local context resolution. :py:meth:`~openhcs.core.orchestrator.orchestrator.PipelineOrchestrator.apply_pipeline_config` sets up pipeline editing context with merged config using :py:func:`~openhcs.core.orchestrator.orchestrator._create_merged_config`.

Pipeline Config Editing Context
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Pipeline config editing (accessed from plate manager) uses thread-local context with the current pipeline configuration. This allows pipeline-specific forms to show proper inheritance from global config while maintaining isolation from other pipeline configurations.

Global Config Editing Context
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Global config editing (accessed from main window) uses :py:func:`~openhcs.core.context.global_config.set_current_global_config` with the new global config instance directly. Since this is the top-level configuration, fields show static defaults rather than resolving against higher-level context.
