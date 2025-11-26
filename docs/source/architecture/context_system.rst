Context Management System
=========================

Configuration resolution requires tracking which configs are active at any point during execution. OpenHCS uses Python's ``contextvars`` for clean context stacking without frame introspection.

.. code-block:: python

   from openhcs.config_framework import config_context

   # For objects implementing ScopedObject interface
   with config_context(global_config, context_provider=orchestrator):
       with config_context(pipeline_config, context_provider=orchestrator):
           # Both configs available for resolution
           # Scope information automatically derived via build_scope_id()
           lazy_instance.field_name  # Resolves through both contexts

The ``config_context()`` manager extracts dataclass fields and merges them into the context stack, enabling lazy resolution without explicit parameter passing. Objects implementing the ``ScopedObject`` interface can provide their own scope identification via the ``build_scope_id()`` method.

Context Stacking
----------------

Contexts stack via ``contextvars.ContextVar``:

.. code-block:: python

   # openhcs/config_framework/context_manager.py
   _config_context_base: ContextVar[Optional[Dict[str, Any]]] = ContextVar(
       'config_context_base',
       default=None
   )

   @contextmanager
   def config_context(obj, context_provider=None):
       """Stack a configuration context.

       Args:
           obj: Configuration object to add to context
           context_provider: Object implementing ScopedObject interface or ScopeProvider
                           for automatic scope derivation
       """
       # Extract all dataclass fields from obj
       new_configs = extract_all_configs(obj)

       # Derive scope if obj implements ScopedObject
       scope_id = None
       if isinstance(obj, ScopedObject) and context_provider is not None:
           scope_id = obj.build_scope_id(context_provider)
       elif isinstance(context_provider, ScopeProvider):
           scope_id = context_provider.scope_id

       # Get current context
       current = _config_context_base.get()

       # Merge with current context
       merged = merge_configs(current, new_configs) if current else new_configs

       # Set scope information in ContextVars
       scope_token = current_scope_id.set(scope_id)

       # Set new context
       token = _config_context_base.set(merged)
       try:
           yield
       finally:
           _config_context_base.reset(token)
           current_scope_id.reset(scope_token)

Each ``with config_context()`` block adds configs to the stack. On exit, the context is automatically restored.

Context Extraction
-----------------

The system extracts all dataclass fields from the provided object:

.. code-block:: python

   def extract_all_configs(context_obj) -> Dict[str, Any]:
       """Extract all dataclass configs from an object."""
       configs = {}
       
       # Extract dataclass fields
       if is_dataclass(context_obj):
           for field in fields(context_obj):
               value = getattr(context_obj, field.name)
               if is_dataclass(value):
                   # Store by type name
                   configs[type(value).__name__] = value
       
       return configs

This flattens nested configs into a single dictionary keyed by type name.

Global Config Context
--------------------

Global config uses thread-local storage for stability:

.. code-block:: python

   # Thread-local storage for global config
   _global_config_storage: Dict[Type, threading.local] = {}
   
   def ensure_global_config_context(config_type: Type, config_instance: Any):
       """Establish global config as base context."""
       # Store in thread-local
       set_current_global_config(config_type, config_instance)
       
       # Also inject into contextvars base
       with config_context(config_instance):
           # Global context now available

This hybrid approach uses thread-local for the global base and contextvars for dynamic stacking.

Resolution Integration
---------------------

The dual-axis resolver receives the merged context:

.. code-block:: python

   def resolve_field_inheritance(obj, field_name, available_configs):
       """Resolve field through dual-axis algorithm.
       
       available_configs: Merged context from config_context() stack
       """
       # Walk MRO
       for mro_class in type(obj).__mro__:
           # Check if this MRO class has a config instance in context
           for config_name, config_instance in available_configs.items():
               if type(config_instance) == mro_class:
                   value = object.__getattribute__(config_instance, field_name)
                   if value is not None:
                       return value
       return None

The ``available_configs`` dict contains all configs from the context stack, flattened and ready for MRO traversal.

ScopedObject Interface
----------------------

Objects that need scope identification implement the ``ScopedObject`` ABC:

.. code-block:: python

   from openhcs.config_framework import ScopedObject

   class GlobalPipelineConfig(ScopedObject):
       """Global configuration with no scope (None)."""

       def build_scope_id(self, context_provider) -> Optional[str]:
           return None  # Global scope

   class PipelineConfig(GlobalPipelineConfig):
       """Plate-level configuration with plate path as scope."""

       def build_scope_id(self, context_provider) -> str:
           return str(context_provider.plate_path)

   class FunctionStep(ScopedObject):
       """Step-level configuration with plate::step scope."""

       def build_scope_id(self, context_provider) -> str:
           return f"{context_provider.plate_path}::{self.token}"

``FunctionStep`` is a scoped object with lazy config attributes (e.g., ``step_well_filter_config``), enabling sibling inheritance between nested configs. See :doc:`sibling_inheritance_system` for details on how scoped objects work with the parent overlay pattern.

For UI code that only has scope strings (not full objects), use ``ScopeProvider``:

.. code-block:: python

   from openhcs.config_framework import ScopeProvider

   # UI code with only scope string
   scope_provider = ScopeProvider(scope_id="/plate_001::step_6")
   with config_context(step_config, context_provider=scope_provider):
       # Scope is provided without needing full orchestrator object
       pass

GlobalConfigBase Virtual Base Class
------------------------------------

The ``GlobalConfigBase`` virtual base class uses a custom metaclass to enable ``isinstance()`` checks without requiring inheritance:

.. code-block:: python

   from openhcs.config_framework import GlobalConfigBase, is_global_config_instance

   # GlobalPipelineConfig is detected as a global config
   isinstance(GlobalPipelineConfig(), GlobalConfigBase)  # True

   # Helper functions for type checking
   is_global_config_instance(config)  # True for GlobalPipelineConfig instances
   is_global_config_type(GlobalPipelineConfig)  # True

This enables generic code that works with any global config type without hardcoding class names.

Usage Pattern
------------

From ``tests/integration/test_main.py``:

.. code-block:: python

   # Establish global context
   global_config = GlobalPipelineConfig(num_workers=4)
   ensure_global_config_context(GlobalPipelineConfig, global_config)

   # Create pipeline config
   pipeline_config = PipelineConfig(
       path_planning_config=LazyPathPlanningConfig(output_dir_suffix="_custom")
   )

   # Stack contexts with scope information
   with config_context(pipeline_config, context_provider=orchestrator):
       # Both global and pipeline configs available
       # Scope automatically derived via pipeline_config.build_scope_id(orchestrator)
       # Lazy fields resolve through merged context with scope priority
       orchestrator = Orchestrator(pipeline_config)

The orchestrator and all lazy configs inside it can resolve fields through both ``global_config`` and ``pipeline_config`` contexts.

Context Cleanup
--------------

Contextvars automatically handle cleanup:

.. code-block:: python

   with config_context(pipeline_config):
       # Context active
       pass
   # Context automatically restored to previous state

No manual cleanup needed - Python's context manager protocol handles it.
