Dynamic Dataclass Factory System
================================

**Runtime dataclass generation with method binding and resolution chains.**

*Status: STABLE*
*Module: openhcs.core.lazy_config*

Overview
--------
Traditional dataclasses have fixed behavior at definition time, but lazy configuration requires runtime behavior customization based on context. The dynamic factory system generates dataclasses with custom resolution methods and configurable fallback chains.

:py:meth:`~openhcs.core.lazy_config.LazyDataclassFactory._create_lazy_dataclass_unified` works like a dataclass compiler. It takes a regular dataclass definition and generates a new class with the same fields and interface, but replaces the field access behavior. Instead of returning stored values, field access triggers custom resolution logic that can look up values from thread-local context, parent configurations, or static defaults.

This enables the same dataclass interface with different resolution behavior for different contexts - step editors resolve against pipeline config, pipeline configs resolve against global config, and global configs use static defaults.

LazyDataclassFactory Architecture
---------------------------------
The factory uses a unified creation pattern with declarative configuration.

Core Factory Method
~~~~~~~~~~~~~~~~~~
:py:meth:`~openhcs.core.lazy_config.LazyDataclassFactory._create_lazy_dataclass_unified` orchestrates the entire generation process. It first introspects the base dataclass to understand its fields, creates a resolution configuration that defines where to look for values, uses :py:func:`~dataclasses.make_dataclass` to generate a new class with the same fields, then attaches custom methods that implement the lazy resolution behavior.

Method Binding System
~~~~~~~~~~~~~~~~~~~~
:py:class:`~openhcs.core.lazy_config.LazyMethodBindings` acts like a method factory. It creates the actual functions that get attached to generated classes - `_resolve_field_value()` for looking up field values, `__getattribute__()` for intercepting field access, and `to_base_config()` for converting back to concrete values. These methods are created as closures that capture the resolution configuration, then attached to the class using :py:func:`setattr`.

Resolution Chain Configuration
------------------------------
The factory configures fallback chains for different resolution strategies.

Fallback Chain Creation
~~~~~~~~~~~~~~~~~~~~~~
:py:class:`~openhcs.core.lazy_config.ResolutionConfig` defines the lookup order for field values. It creates a chain of functions that are tried in sequence: first the instance provider (thread-local context or custom context provider), then static field extractor (base class defaults). Each function in the chain takes a field name and returns either a value or None. The resolution system tries each function until one returns a non-None value.

Field-Level Auto-Hierarchy
~~~~~~~~~~~~~~~~~~~~~~~~~~
:py:meth:`~openhcs.core.lazy_config.LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy` automates the complex setup for hierarchical configs. It uses :py:func:`~openhcs.core.field_path_detection.find_field_path_for_type` to automatically discover where each config type should live in the global config hierarchy (like finding that `StepMaterializationConfig` maps to `materialization_defaults`), then creates the appropriate context provider that resolves against that specific field path.

Recursive Lazy Dataclass Creation
---------------------------------
The factory automatically creates lazy versions of nested dataclasses.

:py:meth:`~openhcs.core.lazy_config.LazyDataclassFactory._introspect_dataclass_fields` examines each field of the base dataclass. When it finds a field whose type is itself a dataclass, it recursively calls the factory to create a lazy version of that nested type. This creates a tree of lazy dataclasses where each level can have its own resolution behavior while maintaining the original nested structure.

Type Registry Integration
------------------------
Generated classes are automatically registered for type mapping.

:py:func:`~openhcs.core.lazy_config.register_lazy_type_mapping` maintains a bidirectional mapping between lazy classes and their base classes. This allows the system to recognize that `LazyPipelineConfig` instances should be treated as `PipelineConfig` for type checking purposes, and enables conversion functions to automatically find the right base type when serializing lazy configs back to concrete values.

UI Context Integration
---------------------
The factory creates different lazy dataclass variants for different UI contexts.

Step Editor Integration
~~~~~~~~~~~~~~~~~~~~~~
Step editors require lazy dataclasses that resolve against their parent pipeline configuration. The factory creates step-specific lazy configs with custom context providers that isolate step configuration from other UI components while maintaining proper inheritance from pipeline settings.

Pipeline Editor Integration
~~~~~~~~~~~~~~~~~~~~~~~~~~
Pipeline editors (plate manager style) use lazy dataclasses that resolve against thread-local context. The factory creates pipeline-level lazy configs that inherit from global configuration while allowing pipeline-specific overrides.

Pipeline Config Integration
~~~~~~~~~~~~~~~~~~~~~~~~~~
Pipeline config editing (accessed from plate manager) uses lazy dataclasses that resolve against the current pipeline's thread-local context. This enables proper inheritance display while maintaining isolation between different pipeline configurations.

Global Config Integration
~~~~~~~~~~~~~~~~~~~~~~~~
Global config editing (accessed from main window) uses lazy dataclasses that show static defaults since there's no higher-level context to resolve against. The factory creates global-level lazy configs that display base class default values.

Context Provider Patterns
-------------------------
The factory supports different context provider patterns for different UI scenarios.

Thread-Local Context Provider
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Standard pattern for pipeline and global config editing where resolution uses the current thread-local context stored in :py:class:`~openhcs.core.context.global_config._global_config_contexts`.

Custom Context Provider
~~~~~~~~~~~~~~~~~~~~~~
Pattern for step editors where resolution uses a custom lambda function that returns the parent pipeline configuration. This enables step-level isolation while maintaining proper inheritance chains.

Static Context Provider
~~~~~~~~~~~~~~~~~~~~~~
Pattern for global config editing where resolution falls back to static defaults without any dynamic context lookup.

See Also
--------
- :doc:`context_system` - Thread-local context system for lazy resolution
- :doc:`configuration_framework` - Configuration framework overview
- :doc:`orchestrator_configuration_management` - Orchestrator configuration patterns
