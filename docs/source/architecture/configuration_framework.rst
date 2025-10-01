Configuration Framework
=======================

Traditional configuration systems lose user edits when switching contexts because they can't distinguish between "use parent default" and "I specifically want this value". OpenHCS solves this through lazy dataclass resolution with dual-axis inheritance.

.. code-block:: python

   @auto_create_decorator
   @dataclass(frozen=True)
   class GlobalPipelineConfig:
       num_workers: int = 1
       
   # Decorator automatically creates PipelineConfig with None defaults:
   # class PipelineConfig:
   #     num_workers: int | None = None  # Inherits from GlobalPipelineConfig

The ``@auto_create_decorator`` generates lazy dataclasses where ``None`` means "inherit from parent context" and explicit values mean "use this specific value". This preserves user intent across context switches.

Dual-Axis Resolution
--------------------

Resolution combines context flattening (X-axis) with MRO traversal (Y-axis):

.. code-block:: python

   # X-axis: Context hierarchy flattened into available_configs dict
   with config_context(global_config):           # GlobalPipelineConfig
       with config_context(pipeline_config):     # PipelineConfig  
           with config_context(step_config):     # StepMaterializationConfig
               # All three merged into available_configs dict
               
   # Y-axis: MRO determines priority
   # StepMaterializationConfig.__mro__ = [StepMaterializationConfig, StepWellFilterConfig, 
   #                                       PathPlanningConfig, WellFilterConfig, ...]
   # Walk MRO, check available_configs for each type, return first concrete value

This enables sophisticated inheritance patterns without hardcoded priority functions - Python's MRO IS the priority.

Configuration Hierarchy
-----------------------

OpenHCS has two configuration levels with automatic lazy generation:

.. code-block:: python

   # Level 1: GlobalPipelineConfig (application-wide defaults)
   @auto_create_decorator
   @dataclass(frozen=True)
   class GlobalPipelineConfig:
       num_workers: int = 1
       
   # Level 2: PipelineConfig (auto-generated with None defaults)
   # Automatically created by decorator

The decorator system eliminates boilerplate - you only define ``GlobalPipelineConfig`` with concrete defaults, and ``PipelineConfig`` is generated automatically with ``None`` defaults for inheritance.

Nested Configuration Pattern
----------------------------

Nested configurations use the ``@global_pipeline_config`` decorator to inject fields into both ``GlobalPipelineConfig`` and ``PipelineConfig``:

.. code-block:: python

   @global_pipeline_config
   @dataclass(frozen=True)
   class PathPlanningConfig(WellFilterConfig):
       output_dir_suffix: str = ""
       sub_dir: str = ""

Nested configs inherit through both their own MRO and the parent config hierarchy.

Sibling Inheritance via MRO
---------------------------

Multiple inheritance enables sibling field inheritance:

.. code-block:: python

   @global_pipeline_config
   @dataclass(frozen=True)
   class WellFilterConfig:
       well_filter: Optional[Union[List[str], str, int]] = None

   @global_pipeline_config
   @dataclass(frozen=True)
   class PathPlanningConfig(WellFilterConfig):
       output_dir_suffix: str = ""
       sub_dir: str = ""

   @global_pipeline_config
   @dataclass(frozen=True)
   class StepWellFilterConfig(WellFilterConfig):
       well_filter: Optional[Union[List[str], str, int]] = 1  # Override default

   @global_pipeline_config
   @dataclass(frozen=True)
   class StepMaterializationConfig(StepWellFilterConfig, PathPlanningConfig):
       backend: MaterializationBackend = MaterializationBackend.AUTO
       # Inherits well_filter from StepWellFilterConfig (comes first in MRO)
       # Inherits output_dir_suffix, sub_dir from PathPlanningConfig

The MRO for ``StepMaterializationConfig`` is:

.. code-block:: python

   StepMaterializationConfig.__mro__ = (
       StepMaterializationConfig,
       StepWellFilterConfig,
       PathPlanningConfig,
       WellFilterConfig,
       object
   )

When resolving ``well_filter`` field with all values set to ``None``:

1. Check ``StepMaterializationConfig`` - no override (inherits)
2. Check ``StepWellFilterConfig`` - has ``well_filter = 1`` → **use this**
3. Never reaches ``PathPlanningConfig`` or ``WellFilterConfig``

This is pure Python MRO - no custom priority logic needed.

Real-World Usage
---------------

From ``tests/integration/test_main.py``:

.. code-block:: python

   # Create global config with concrete values
   global_config = GlobalPipelineConfig(
       num_workers=4,
       path_planning_config=PathPlanningConfig(
           sub_dir="processed",
           output_dir_suffix="_output"
       )
   )
   
   # Establish global context
   ensure_global_config_context(GlobalPipelineConfig, global_config)
   
   # Create pipeline config with lazy configs for inheritance
   pipeline_config = PipelineConfig(
       path_planning_config=LazyPathPlanningConfig(
           output_dir_suffix="_custom"  # Override global
           # sub_dir=None (implicit) - inherits "processed" from global
       )
   )

The lazy configs resolve through dual-axis algorithm: check ``PipelineConfig`` context first, then ``GlobalPipelineConfig`` context, walking MRO at each level.

Framework Modules
----------------

The framework is extracted to ``openhcs.config_framework`` for reuse:

**lazy_factory.py**
  Generates lazy dataclasses with ``__getattribute__`` interception

**dual_axis_resolver.py**
  Pure MRO-based resolution - no priority functions

**context_manager.py**
  Contextvars-based context stacking via ``config_context()``

**placeholder.py**
  UI placeholder generation showing inherited values

**global_config.py**
  Thread-local storage for global configuration

**config.py**
  Framework initialization - ``set_base_config_type(GlobalPipelineConfig)``

Backward compatibility shims at old paths (``openhcs.core.lazy_config``, etc.) re-export from framework.
