Configuration System Architecture
=================================

Overview
--------

Traditional configuration systems suffer from the "lost edits" problem - user modifications get overwritten by defaults when switching contexts. OpenHCS solves this through lazy dataclasses that resolve values from different sources based on editing context.

.. code-block:: python

   @dataclass(frozen=True)
   class StepMaterializationConfig:
       num_workers: Optional[int] = None  # Lazy: resolves from pipeline → global
       gpu_enabled: Optional[bool] = None  # Lazy: resolves from pipeline → global

   # Context-aware resolution
   step_config.num_workers  # Shows pipeline value if set, else global value
   pipeline_config.num_workers  # Shows global value if not overridden

This enables hierarchical configuration flow (Global → Pipeline → Step) while preserving user edits at each level.

Lazy Resolution System
---------------------

Configuration values resolve dynamically based on the current editing context and hierarchy.

.. code-block:: python

   # Resolution hierarchy: User-set → Thread-local → Constructor defaults

   class LazyConfigResolver:
       def resolve_field(self, field_name: str, context: str) -> Any:
           # 1. Check if user explicitly set this field
           if hasattr(self, field_name) and getattr(self, field_name) is not None:
               return getattr(self, field_name)

           # 2. Check thread-local context (current global config)
           if context_value := self._get_from_context(field_name):
               return context_value

           # 3. Fall back to constructor default
           return self._get_constructor_default(field_name)

This ensures user edits are preserved while providing appropriate defaults for each editing context.

Configuration Structure
-----------------------

OpenHCS uses immutable dataclasses that compose together to form the configuration hierarchy.

.. code-block:: python

   @dataclass(frozen=True)
   class GlobalPipelineConfig:
       """Root configuration object."""
       vfs_config: VFSConfig = field(default_factory=VFSConfig)
       path_planning_config: PathPlanningConfig = field(default_factory=PathPlanningConfig)
       zarr_config: ZarrConfig = field(default_factory=ZarrConfig)
       num_workers: int = 4
       microscope: str = "ImageXpress"

       num_workers: Optional[int] = None  # Lazy: resolves from pipeline → global
       save_intermediate: Optional[bool] = None  # Lazy: resolves from pipeline → global

Thread-Local Context System
----------------------------

Configuration contexts are stored per-thread to avoid parameter passing while maintaining isolation.

.. code-block:: python

   # Type-keyed thread-local storage
   _global_config_contexts: Dict[Type, threading.local] = {}

   def set_current_global_config(config_type: Type, config_instance: Any) -> None:
       """Set current global config for any dataclass type."""
       if config_type not in _global_config_contexts:
           _global_config_contexts[config_type] = threading.local()
       _global_config_contexts[config_type].value = config_instance

This provides isolated configuration contexts per thread without parameter passing.

Lazy Dataclass Factory
-----------------------

The LazyDataclassFactory generates runtime dataclasses with context-aware field resolution.

.. code-block:: python

   # Create lazy config for editing
   LazyStepConfig = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
       base_class=StepMaterializationConfig,
       global_config_type=GlobalPipelineConfig,
       field_path="materialization_defaults",
       lazy_class_name="LazyStepMaterializationConfig"
   )

   # Field resolution: user-set → thread-local → static defaults
   config = LazyStepConfig()
   config.num_workers  # Resolves from context if None, else uses user value

This enables context-aware configuration editing where the same field shows different values based on editing scope.

Field Path Detection
--------------------

The system automatically discovers configuration relationships through type introspection.

.. code-block:: python

   @staticmethod
   def find_field_path_for_type(parent_type: Type, child_type: Type) -> Optional[str]:
       """Find field path for child_type within parent_type structure."""
       # Direct field matching
       for field in dataclasses.fields(parent_type):
           if field.type == child_type:
               return field.name

       # Recursive search in nested dataclasses
       for field in dataclasses.fields(parent_type):
           if dataclasses.is_dataclass(field.type):
               nested_path = find_field_path_for_type(field.type, child_type)
               if nested_path:
                   return f"{field.name}.{nested_path}"
       return None

This eliminates hardcoded field mappings and adapts automatically to configuration structure changes.

Integration Examples
-------------------

The configuration system integrates with other OpenHCS subsystems.

.. code-block:: python

   # Component system integration
   from openhcs.core.components.framework import ComponentConfiguration
   from openhcs.constants import get_openhcs_config

   component_config = get_openhcs_config()
   validator = GenericValidator(component_config)

   # UI framework integration
   def create_config_editor(dataclass_type: Type, current_config: Any):
       set_current_global_config(GlobalPipelineConfig, current_config)
       return LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
           base_class=dataclass_type,
           global_config_type=GlobalPipelineConfig,
           field_path=FieldPathDetector.find_field_path_for_type(
               GlobalPipelineConfig, dataclass_type
           )
       )()

**Common Gotchas**:

- Thread-local contexts are isolated per thread - don't share between threads
- Lazy dataclasses must be created after setting thread-local context
- Field path detection requires proper type annotations on dataclass fields
