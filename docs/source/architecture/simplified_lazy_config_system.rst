Simplified Lazy Configuration System
====================================

**Contextvars-based lazy dataclass resolution with clean separation of concerns.**

*Status: STABLE - Simplified Implementation*
*Module: openhcs.core.lazy_config*

Overview
--------

The OpenHCS lazy configuration system has been simplified to use Python's built-in ``contextvars`` module for explicit context management, eliminating complex field path detection and frame injection mechanisms while maintaining full functionality.

**Key Improvements:**

- **Explicit Context Management**: Uses ``contextvars`` instead of complex frame injection
- **Simplified Factory**: Single ``make_lazy_simple()`` method replaces complex hierarchy providers
- **Clean Separation**: Inheritance logic centralized in resolver, not scattered across services
- **Better Performance**: No complex path detection or composition analysis needed
- **Easier Maintenance**: Significantly fewer interdependencies between files

Architecture
------------

Contextvars-Based Context Management
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The new system uses Python's ``contextvars`` module for explicit context scoping:

.. code-block:: python

   from openhcs.core.context.contextvars_context import config_context, current_temp_global
   
   # Explicit context management
   with config_context(orchestrator.pipeline_config):
       # All lazy resolution happens within this context
       resolved_value = lazy_instance.some_field

**Benefits:**

- **Explicit**: Context boundaries are clearly defined
- **Thread-safe**: Built-in thread isolation
- **Predictable**: No complex stack introspection
- **Fast**: Direct context variable access

Simplified Lazy Factory
~~~~~~~~~~~~~~~~~~~~~~~

The ``LazyDataclassFactory`` now has a single, simple factory method:

.. code-block:: python

   # New simplified factory
   lazy_class = LazyDataclassFactory.make_lazy_simple(
       base_class=PathPlanningConfig,
       lazy_class_name="LazyPathPlanningConfig"
   )

**Removed Complexity:**

- No more ``make_lazy_with_field_level_auto_hierarchy()``
- No complex hierarchy providers
- No field path detection
- No composition analysis

Clean Separation of Concerns
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Before (Mixed Concerns):**

- Placeholder service contained inheritance logic
- Field path detection scattered across multiple files
- Complex interdependencies between services

**After (Clean Separation):**

- **Resolver**: Contains ALL inheritance logic (``dual_axis_resolver_recursive.py``)
- **Placeholder Service**: Pure consumer, just creates instances and accesses fields
- **Factory**: Simple dataclass generation using contextvars

Cross-Dataclass Inheritance
---------------------------

The system maintains sophisticated inheritance patterns through the dual-axis resolver:

.. code-block:: python

   # StepMaterializationConfig inherits from both:
   # - StepWellFilterConfig (for well_filter field)
   # - PathPlanningConfig (for output_dir_suffix field)
   
   # Resolution happens automatically through contextvars
   with config_context(pipeline_config):
       materialization_config = LazyStepMaterializationConfig()
       # Inherits well_filter from StepWellFilterConfig
       # Inherits output_dir_suffix from PathPlanningConfig

**Key Features:**

- **Cross-dataclass inheritance**: Fields inherit from sibling configs
- **Context-scoped resolution**: Different values in different contexts
- **Static override detection**: Concrete values take precedence
- **Placeholder generation**: UI shows inherited values

Migration from Old System
-------------------------

**Removed Files:**

- ``openhcs/core/field_path_detection.py`` (387 lines)
- ``openhcs/core/composition_detection.py`` (350+ lines)

**Simplified Files:**

- ``openhcs/core/lazy_placeholder.py`` (363 → 8 lines, now just redirects)
- ``openhcs/core/lazy_config.py`` (removed complex factory methods)

**Updated Imports:**

.. code-block:: python

   # Old (removed)
   from openhcs.core.field_path_detection import FieldPathDetector
   from openhcs.core.lazy_placeholder import _has_concrete_field_override
   
   # New (simplified)
   from openhcs.core.dual_axis_resolver_recursive import _has_concrete_field_override
   from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService

Usage Examples
--------------

Creating Lazy Configs
~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   # Simple factory usage
   lazy_config_class = LazyDataclassFactory.make_lazy_simple(
       base_class=StepMaterializationConfig
   )
   
   # Use within context
   with config_context(pipeline_config):
       lazy_instance = lazy_config_class()
       # Fields resolve automatically through contextvars

Placeholder Generation
~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   # Simplified placeholder service
   with config_context(pipeline_config):
       placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
           LazyStepMaterializationConfig,
           "output_dir_suffix"
       )
       # Returns: "Pipeline default: _outputs"

Benefits of Simplification
--------------------------

**Code Reduction:**

- **~1000+ lines removed** across deprecated files
- **Simpler architecture** with fewer moving parts
- **Better performance** without complex discovery mechanisms

**Maintainability:**

- **Single source of truth** for inheritance logic (resolver)
- **Clear separation** between services and resolution
- **Easier debugging** with explicit context management

**Reliability:**

- **No frame injection** eliminates stack manipulation risks
- **Explicit context** prevents context discovery failures
- **Thread-safe** through built-in contextvars isolation

The simplified system maintains all the sophisticated inheritance capabilities of the original while being much easier to understand, maintain, and debug.
