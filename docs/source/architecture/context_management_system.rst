Context Management System
=========================

**Dual-axis context discovery with frame injection and automatic context hierarchy resolution.**

*Status: STABLE - Dual-Axis Implementation*
*Module: openhcs.core.dual_axis_resolver_recursive*

Overview
--------

Configuration systems require sophisticated context management to support hierarchical resolution patterns while maintaining proper inheritance chains. The context management system uses frame injection and stack introspection to automatically discover context hierarchy without explicit parameter passing.

The system operates on the principle that configuration resolution should be transparent to consuming code - functions and methods should not need to explicitly pass context objects around, yet the resolution system should still have access to the appropriate context for making inheritance decisions. This is achieved through a frame injection mechanism that temporarily places context objects into the call stack where they can be discovered through systematic introspection.

.. code-block:: python

   # Automatic context discovery through stack introspection
   context_hierarchy = ContextDiscovery.discover_context(target_type)
   # Returns: [step_context, orchestrator_context, global_context]

   # Frame injection for context provision
   ContextInjector.inject_context(orchestrator, "orchestrator")
   # Injects: frame.f_locals["__orchestrator_context__"] = orchestrator

   # Automatic cleanup in finally blocks
   # No explicit context management required

The :py:class:`~openhcs.core.dual_axis_resolver_recursive.ContextDiscovery` class implements the discovery algorithm, while :py:class:`~openhcs.core.lazy_config.ContextInjector` provides the injection mechanism. This eliminates explicit context passing while providing sophisticated context hierarchy resolution for dual-axis inheritance patterns.

Frame Injection System
----------------------

The system uses frame injection to provide context without explicit parameter passing. This mechanism works by temporarily placing context objects into the local variable namespace of call stack frames, where they can be discovered by the resolution system through systematic stack traversal.

Context Injection Mechanism
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The frame injection mechanism operates by manipulating the ``f_locals`` dictionary of call stack frames. When a context needs to be provided, the system injects a specially-named variable into the caller's frame, following a consistent naming pattern that the discovery system can recognize.

.. code-block:: python

   # Frame injection for context provision
   class ContextInjector:
       @staticmethod
       def inject_context(context_obj: Any, context_type: str = "step") -> None:
           """Inject context into call stack for dual-axis resolution."""
           import inspect
           frame = inspect.currentframe().f_back  # Get caller's frame
           context_var_name = f"__{context_type}_context__"
           frame.f_locals[context_var_name] = context_obj

   # Automatic cleanup with context managers
   @staticmethod
   def with_context(context_obj: Any, context_type: str = "step"):
       """Context manager for temporary context injection."""
       @contextmanager
       def _context_manager():
           frame = inspect.currentframe().f_back.f_back
           context_var_name = f"__{context_type}_context__"
           frame.f_locals[context_var_name] = context_obj
           try:
               yield
           finally:
               if context_var_name in frame.f_locals:
                   del frame.f_locals[context_var_name]
       return _context_manager()

The :py:meth:`~openhcs.core.lazy_config.ContextInjector.inject_context` method provides direct injection, while :py:meth:`~openhcs.core.lazy_config.ContextInjector.with_context` offers a context manager pattern for automatic cleanup. The naming convention uses double underscores to avoid conflicts with normal variables while making the injected contexts easily identifiable.

Context Discovery System
~~~~~~~~~~~~~~~~~~~~~~~~

The system automatically discovers injected contexts through stack introspection. This discovery process reverses the injection mechanism by systematically examining each frame in the call stack for variables that match the expected naming pattern.

The discovery algorithm works by walking up the Python call stack frame by frame, examining the local variables in each frame for specially-named context variables. This approach allows the system to find contexts that were injected at any level of the call hierarchy.

.. code-block:: python

   # Automatic context discovery
   class ContextDiscovery:
       @staticmethod
       def discover_context(target_type: type = None) -> Optional[Any]:
           """Walk call stack to find objects that can provide resolution context."""

           # Walk up the call stack
           frame = inspect.currentframe()
           while frame:
               # Look for injected context variables
               context = ContextDiscovery._find_injected_context(frame, target_type)
               if context:
                   return context
               frame = frame.f_back

           return None

       @staticmethod
       def _find_injected_context(frame: Any, target_type: type = None) -> Optional[Any]:
           """Find any injected context in frame locals using generic pattern."""
           for var_name, var_value in frame.f_locals.items():
               # Generic pattern: __*_context__ (e.g., __step_context__, __orchestrator_context__)
               if var_name.startswith('__') and var_name.endswith('_context__'):
                   if ContextDiscovery._is_context_provider(var_value, target_type):
                       return var_value
           return None

The ``discover_context`` method implements the core discovery loop: starting from the current frame, it walks up the call stack using ``frame.f_back`` until it finds a context or reaches the top. The ``_find_injected_context`` helper examines each frame's local variables, looking for names that match the injection pattern (``__*_context__``). The ``_is_context_provider`` method validates that the found object can actually provide the needed context type.

Integration with Dual-Axis Resolution
-------------------------------------

The context management system integrates with the dual-axis resolver to provide sophisticated inheritance patterns.

Recursive Context Hierarchy
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The system builds complete context hierarchies by discovering multiple context types in priority order. This hierarchy forms the X-axis of the dual-axis resolution system, ensuring that more specific contexts take precedence over general ones.

.. code-block:: python

   # Context hierarchy discovery for dual-axis resolution
   def _discover_context_hierarchy(self, target_type: Type) -> List[Any]:
       """Discover full context hierarchy from most specific to least specific."""
       hierarchy = []

       # Use context discovery to find the most specific context
       most_specific_context = ContextDiscovery.discover_context(target_type)
       if most_specific_context:
           hierarchy.append(most_specific_context)

           # Try to find parent contexts
           parent_context = self._find_parent_context(most_specific_context, target_type)
           while parent_context and parent_context not in hierarchy:
               hierarchy.append(parent_context)
               parent_context = self._find_parent_context(parent_context, target_type)

       return hierarchy  # [step_context, orchestrator_context, global_context]

This method builds the context hierarchy by first finding the most specific context available through stack introspection, then recursively discovering parent contexts. The ``_find_parent_context`` method examines the current context to determine what its parent context should be (e.g., a step context's parent is the orchestrator context). The loop continues until no more parent contexts can be found, creating a complete hierarchy from specific to general.

This enables automatic context hierarchy resolution without explicit context management code, forming the X-axis traversal order for dual-axis resolution.

Orchestrator Context Management
------------------------------

The orchestrator automatically provides context for dual-axis resolution through frame injection and context discovery.

Orchestrator as Context Provider
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   class PipelineOrchestrator(ContextProvider):
       """Orchestrator provides context for step-level configuration resolution."""

       _context_type = "orchestrator"  # Automatic context registration

       def __init__(self, ...):
           # Orchestrator automatically registers as context provider
           super().__init__()

           # Apply global config inheritance to pipeline config
           self._apply_global_config_inheritance()

       def _apply_global_config_inheritance(self):
           """Merge global config values into pipeline config for proper inheritance."""
           if self.pipeline_config and self.global_config:
               # Create merged config that inherits None values from global config
               merged_config = self._merge_configs(self.pipeline_config, self.global_config)
               self.pipeline_config = merged_config

Context Injection During Compilation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   # Orchestrator context is automatically injected during lazy config resolution
   def resolve_lazy_configurations_for_serialization(resolved_data):
       """Resolve lazy configs with automatic context injection."""

       # Detect if this is a context provider (orchestrator, step, etc.)
       context_type = _detect_context_type(resolved_data)
       if context_type:
           # Inject context into call stack
           import inspect
           frame = inspect.currentframe()
           context_var_name = f"__{context_type}_context__"
           frame.f_locals[context_var_name] = resolved_data

           try:
               # Process with injected context - dual-axis resolver will find it
               return _process_with_context(resolved_data)
           finally:
               # Clean up injected context
               if context_var_name in frame.f_locals:
                   del frame.f_locals[context_var_name]

This ensures that compilation uses the same context hierarchy as UI operations, maintaining consistency between placeholder resolution and actual execution.

Frame Injection Safety
---------------------

The frame injection system is designed for OpenHCS's single-threaded compilation model with proper cleanup guarantees.

Memory Management
~~~~~~~~~~~~~~~~~

Frame injection includes comprehensive cleanup to prevent memory leaks:

.. code-block:: python

   # Automatic cleanup in finally blocks
   def resolve_lazy_configurations_for_serialization(resolved_data):
       context_var_name = f"__{context_type}_context__"
       frame.f_locals[context_var_name] = resolved_data

       try:
           # Process with injected context
           return _process_with_context(resolved_data)
       finally:
           # Guaranteed cleanup even on exceptions
           if context_var_name in frame.f_locals:
               del frame.f_locals[context_var_name]
           del frame  # Remove local reference

Exception Safety
~~~~~~~~~~~~~~~~

The system ensures proper cleanup even when exceptions occur during resolution:

.. code-block:: python

   # Exception-safe context management
   @contextmanager
   def with_context(context_obj: Any, context_type: str = "step"):
       frame = inspect.currentframe().f_back.f_back
       context_var_name = f"__{context_type}_context__"
       frame.f_locals[context_var_name] = context_obj
       try:
           yield
       finally:
           # Always runs, even on exceptions
           if context_var_name in frame.f_locals:
               del frame.f_locals[context_var_name]

Single-Threaded Safety
~~~~~~~~~~~~~~~~~~~~~~

Frame injection is safe for OpenHCS because:

1. **Compilation is single-threaded** - No concurrent access to frame locals
2. **UI operations are single-threaded** - Qt main thread or TUI main thread
3. **Worker processes use resolved configs** - No lazy resolution in workers
4. **Proper cleanup** - Finally blocks ensure cleanup even on exceptions

The frame injection approach works correctly for OpenHCS's architecture while providing sophisticated context hierarchy resolution.

UI Integration Patterns
-----------------------
Different UI contexts use different context injection patterns for dual-axis resolution.

Step Editor Context Injection
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Step editors inject orchestrator context to enable proper step-level inheritance:

.. code-block:: python

   # Step editor context injection pattern
   def create_step_editor(orchestrator, step_config_type):
       """Create step editor with orchestrator context injection."""

       # Inject orchestrator context for dual-axis resolution
       ContextInjector.inject_context(orchestrator, "orchestrator")

       try:
           # Create lazy config - will resolve through:
           # step context → orchestrator context → global context
           LazyStepConfig = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
               base_class=step_config_type,
               global_config_type=GlobalPipelineConfig,
               field_path="step_materialization_config"
           )

           return LazyStepConfig()

       finally:
           # Context cleanup handled automatically by resolver
           pass

Pipeline Editor Context
~~~~~~~~~~~~~~~~~~~~~~~
Pipeline editors use global context without orchestrator injection:

.. code-block:: python

   # Pipeline editor context pattern
   def create_pipeline_editor(global_config):
       """Create pipeline editor with global context only."""

       # Set global context (no orchestrator injection needed)
       set_current_global_config(GlobalPipelineConfig, global_config)

       # Pipeline configs resolve directly against global defaults
       LazyPipelineConfig = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
           base_class=PipelineConfig,
           global_config_type=GlobalPipelineConfig,
           field_path=None  # Root config
       )

       return LazyPipelineConfig()

Global Config Editor Context
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Global config editors show static defaults with no context injection:

.. code-block:: python

   # Global config editor pattern
   def create_global_config_editor():
       """Create global config editor with static defaults."""

       # No context injection - uses static class defaults only
       LazyGlobalConfig = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
           base_class=GlobalPipelineConfig,
           global_config_type=GlobalPipelineConfig,
           field_path=None
       )

       return LazyGlobalConfig()

Migration from Thread-Local to Frame Injection
----------------------------------------------
The context management system is transitioning from thread-local storage to frame injection for better consistency.

**Current State**: Mixed usage of thread-local context and frame injection
**Target State**: Unified frame injection with dual-axis resolution
**Benefits**: Perfect consistency between UI and compilation resolution

See Also
--------
- :doc:`configuration_system_architecture` - Dual-axis resolution system
- :doc:`placeholder_resolution_system` - UI placeholder generation using context discovery
- :doc:`lazy_class_system` - Lazy dataclass system that uses context management
