Configuration Resolution System
===============================

**Enhanced dual-axis resolution with thread-local context management and hierarchical value resolution for lazy configurations.**

*Status: STABLE - Enhanced with Dual-Axis Resolver*
*Module: openhcs.core.config, openhcs.core.dual_axis_resolver_recursive*

Overview
--------

Lazy dataclasses need to resolve values from different sources based on execution context without explicit parameter passing. OpenHCS uses an enhanced dual-axis resolution system that combines thread-local storage with sophisticated context discovery and inheritance chain traversal to provide isolated configuration contexts per thread.

The basic usage pattern is demonstrated in :pyobject:`openhcs.core.lazy_config` where lazy dataclasses automatically resolve values based on the current thread's configuration context.

This enables context-aware resolution where the same lazy config shows different values based on the current thread's configuration context.

Thread-Local Context System
----------------------------

Generic thread-local storage for configuration contexts. Different operations require different resolution behavior - global editing shows defaults, pipeline editing shows resolved values.

Generic Storage
~~~~~~~~~~~~~~~

Works with any configuration type via type-keyed storage.

Thread-local storage is implemented in :pyobject:`openhcs.core.config` using generic type-keyed storage that works with any configuration type.

Usage Pattern
~~~~~~~~~~~~~

Usage patterns are demonstrated in :pyobject:`openhcs.core.pipeline_config` showing how thread-local context enables context-aware resolution.

Configuration Resolution Hierarchy
-----------------------------------

Enhanced Dual-Axis Resolution Authority (2024 Update)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Configuration resolution now follows an enhanced dual-axis hierarchy that combines context discovery with inheritance chain traversal:

**X-Axis (Context Hierarchy)**:
1. **Step context** - Most specific context (highest priority)
2. **Orchestrator context** - Intermediate context
3. **Global context** - Thread-local global config instance
4. **Static defaults** - Dataclass field defaults (lowest priority)

**Y-Axis (Inheritance Chain)**:
- For each context level, the system searches through the class inheritance hierarchy using Python's Method Resolution Order (MRO)
- Static overrides in subclasses block inheritance from parent classes for specific fields
- Field-specific inheritance blocking ensures predictable resolution behavior

The enhanced resolution algorithm uses :pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver` to implement depth-first context exhaustion, ensuring each context level is fully explored through inheritance chains before moving to the next context level.

Context-Driven Behavior
~~~~~~~~~~~~~~~~~~~~~~~

Context resolution patterns are implemented in :pyobject:`openhcs.core.config` with support for different editing contexts and resolution behaviors.

Field Path Resolution
---------------------

Explicit Path Navigation
~~~~~~~~~~~~~~~~~~~~~~~~

Eliminates algorithmic field name conversion bugs:

.. code-block:: python

    # Dot-separated paths for nested field access
    LazyStepMaterializationConfig = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
        base_class=StepMaterializationConfig,
        global_config_type=GlobalPipelineConfig,
        field_path="materialization_defaults",  # Explicit path
        lazy_class_name="LazyStepMaterializationConfig"
    )

Automatic Field Path Detection
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The enhanced dual-axis resolver uses sophisticated field path detection to discover inheritance relationships automatically. The :pyobject:`openhcs.core.field_path_detection.FieldPathDetector` provides automatic discovery of field relationships within configuration hierarchies.

Automatic field path discovery is implemented in :pyobject:`openhcs.core.field_path_detection.FieldPathDetector` which automatically discovers inheritance relationships within configuration hierarchies.

UI Context Scoping Patterns
---------------------------

Three UI context types with different resolution behavior.

Context Types
~~~~~~~~~~~~~

**1. Global Config Editing**

Shows actual default values.

Global config editor setup is handled by :pyobject:`openhcs.core.lazy_config` which shows actual default values since there's no higher-level context to resolve against.

**2. Pipeline Config Editing**

Shows orchestrator values with global fallback.

.. code-block:: python

    # Pipeline editor setup
    orchestrator_config = orchestrator.get_effective_config(for_serialization=False)
    set_current_global_config(GlobalPipelineConfig, orchestrator_config)

    # Lazy resolution from orchestrator config, None values use global defaults

The enhanced orchestrator integration uses :pyobject:`openhcs.core.orchestrator.orchestrator.PipelineOrchestrator.config_context` for proper context injection. See :doc:`orchestrator_configuration_management` for detailed orchestrator configuration patterns.

**3. Step Config Editing (Scoped)**

Temporary context for step editing with orchestrator→global fallback.

Context managers for step editing are implemented in :pyobject:`openhcs.core.config` providing temporary context with orchestrator→global fallback and proper cleanup.

Context Manager Pattern
~~~~~~~~~~~~~~~~~~~~~~~

Ensures proper context isolation and cleanup.

Step editor usage patterns are demonstrated in :pyobject:`openhcs.core.lazy_config` showing proper context isolation and cleanup with safe nesting support.

Context managers provide isolation, cleanup, and safe nesting.

Enhanced Resolution Hierarchy (2024 Update)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Step editor resolution now uses the enhanced dual-axis resolver with depth-first context exhaustion:

**Dual-Axis Resolution Chain:**

1. **X-Axis (Context Hierarchy)**: Step context → Orchestrator context → Global context
2. **Y-Axis (Inheritance Chain)**: Target type → Parent types in MRO order
3. **Static Override Detection**: Field-specific blocking for concrete overrides

The :pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver` implements this enhanced algorithm, ensuring each context level is fully exhausted through inheritance chain traversal before moving to the next context level.

**Key Enhancement**: The system now uses :pyobject:`openhcs.core.orchestrator.orchestrator.PipelineOrchestrator.config_context` for dynamic context injection, while thread-local storage serves as the final fallback for global configuration defaults.

Enhanced Context Discovery Requirement
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The enhanced system combines multiple context mechanisms for comprehensive resolution. Frame injection handles dynamic contexts (orchestrator, step), while thread-local storage provides the global configuration fallback:

**Context Resolution Hierarchy**:

1. **Frame Injection**: :pyobject:`openhcs.core.orchestrator.orchestrator.PipelineOrchestrator.config_context` for dynamic orchestrator contexts
2. **Context Discovery**: :pyobject:`openhcs.core.dual_axis_resolver_recursive.ContextDiscovery` for automatic step context detection
3. **Thread-Local Fallback**: :pyobject:`openhcs.core.context.global_config.get_current_global_config` for global configuration defaults

**Key Benefits**:

- **Dynamic Contexts**: Frame injection handles orchestrator and step-specific contexts
- **Global Defaults**: Thread-local storage provides reliable fallback for global configuration
- **Clean APIs**: No explicit parameter passing required
- **Proper Isolation**: Each mechanism serves its appropriate role in the resolution hierarchy

Lazy dataclasses require thread-local for resolution, enhanced with dual-axis resolver integration:

Lazy resolution implementation is provided by :pyobject:`openhcs.core.lazy_config` with enhanced dual-axis resolver integration for sophisticated inheritance patterns.

Enhanced Dual-Axis Resolution Integration
------------------------------------------

The configuration resolution system has been enhanced with the dual-axis resolver to provide more sophisticated inheritance patterns and context discovery.

Context Discovery and Frame Injection
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The enhanced system uses frame injection for automatic context discovery, eliminating the need for explicit parameter passing. The :pyobject:`openhcs.core.orchestrator.orchestrator.PipelineOrchestrator.config_context` method provides enhanced context injection with multi-frame support and proper cleanup mechanisms.

Recursive Field Resolution
~~~~~~~~~~~~~~~~~~~~~~~~~~

The :pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver._resolve_field_recursive` implements enhanced recursive field resolution with depth-first context exhaustion. This algorithm ensures that each context level is fully exhausted through inheritance chain traversal before moving to the next context level, providing more predictable and consistent resolution behavior.

Advanced Thread Safety Patterns
-------------------------------

The UI refactor introduced sophisticated thread safety mechanisms that go beyond basic thread-local storage.

Multi-Threaded Safety Guarantees
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The system provides strong isolation guarantees across different execution contexts:

.. code-block:: python

    # Thread isolation example
    import threading

    def worker_thread_1():
        # Thread 1: UI editing context
        set_current_global_config(GlobalPipelineConfig, ui_config)
        step_config = LazyStepMaterializationConfig()
        value1 = step_config.output_dir_suffix  # Resolves from ui_config

    def worker_thread_2():
        # Thread 2: Compilation context
        set_current_global_config(GlobalPipelineConfig, compilation_config)
        step_config = LazyStepMaterializationConfig()
        value2 = step_config.output_dir_suffix  # Resolves from compilation_config

    # Both threads operate independently with different resolution contexts
    threading.Thread(target=worker_thread_1).start()
    threading.Thread(target=worker_thread_2).start()

**Thread Safety Implementation:**

Thread safety implementation is provided by :pyobject:`openhcs.core.config` with strong isolation guarantees across different execution contexts.

Context Provider Mechanisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Advanced context resolution using custom context providers for specialized scenarios:

Advanced context resolution using custom context providers is implemented in :pyobject:`openhcs.core.lazy_config` with flexible resolution patterns for specialized scenarios.

Context Cleanup and Lifecycle Management
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Proper context lifecycle management prevents memory leaks and ensures clean state transitions:

Context lifecycle management is implemented in :pyobject:`openhcs.pyqt_gui.widgets.pipeline_editor.LazyConfigContext` with proper cleanup and safe context switching to prevent memory leaks and ensure clean state transitions.

Integration with Lazy Dataclass Resolution
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Thread-local contexts integrate seamlessly with the lazy dataclass resolution system:

Integration with lazy dataclass resolution is provided by :pyobject:`openhcs.core.lazy_config` with seamless thread-local context integration and field-level provider patterns.

Debugging Context Resolution
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The system provides debugging capabilities for troubleshooting context resolution issues:

.. code-block:: python

    def debug_context_resolution(config_type=GlobalPipelineConfig):
        """Debug current thread-local context state."""
        context = _global_config_contexts.get(config_type)

        if context is None:
            print(f"❌ No context registered for {config_type.__name__}")
            return

        if not hasattr(context, 'value'):
            print(f"❌ No value set in context for {config_type.__name__}")
            return

        current_config = context.value
        print(f"✅ Active context for {config_type.__name__}:")
        print(f"   Thread: {threading.current_thread().name}")
        print(f"   Config type: {type(current_config).__name__}")

        # Show key configuration values
        if hasattr(current_config, 'materialization_defaults'):
            mat_config = current_config.materialization_defaults
            print(f"   materialization_defaults.output_dir_suffix: {mat_config.output_dir_suffix}")

**Context Resolution Tracing:**

.. code-block:: python

    def traced_get_current_global_config(config_type):
        """Traced version for debugging context access."""
        result = get_current_global_config(config_type)

        if result:
            print(f"🔍 Thread-local access: {config_type.__name__}")
            print(f"   Thread: {threading.current_thread().name}")
        else:
            print(f"❌ No thread-local context for {config_type.__name__}")

        return result

Benefits
--------

**Core Resolution Benefits:**
- **Thread Safety**: Each thread has isolated configuration context
- **Explicit Resolution**: Clear hierarchy eliminates ambiguous behavior
- **Type Safety**: Generic storage maintains type information
- **Fail-Loud**: Configuration errors surface immediately
- **Context Awareness**: Behavior adapts to editing context
- **Clean API**: No parameter threading through function calls

**Enhanced Dual-Axis Resolution Benefits (2024):**
- **Depth-First Context Exhaustion**: Each context level is fully explored before moving up the hierarchy
- **Field-Specific Static Overrides**: Static overrides block inheritance only for specific fields, not entire classes
- **Enhanced Context Discovery**: Automatic context discovery through frame injection with multi-frame support
- **Compiler-Grade Consistency**: Placeholder resolution uses the same algorithm as compilation
- **Sophisticated Inheritance**: Supports complex inheritance patterns with predictable resolution order
- **Frame Injection Safety**: Proper cleanup and safety limits prevent memory leaks and infinite loops

**System Integration Benefits:**
- **UI Operation Scoping**: Enables sophisticated context switching for different editing modes
- **Lazy Loading Foundation**: Provides the ambient context necessary for clean lazy resolution
- **Context Isolation**: Different operations can have different configuration contexts
- **Testability**: Easy to set up test contexts without complex mocking
- **Multi-Threaded Safety**: Strong isolation guarantees across execution contexts
- **Custom Context Providers**: Flexible resolution for specialized scenarios
- **Lifecycle Management**: Proper context cleanup prevents memory leaks
- **Debug Support**: Comprehensive debugging and tracing capabilities

See Also
--------

- :doc:`configuration_system_architecture` - Enhanced dual-axis resolution system architecture
- :doc:`placeholder_resolution_system` - Compiler-grade placeholder resolution using dual-axis resolver
- :doc:`lazy_class_system` - Dynamic dataclass generation that uses thread-local contexts
- :doc:`step-editor-generalization` - Step editors that rely on context-aware resolution
- :doc:`orchestrator_configuration_management` - Orchestrator integration with enhanced context injection
- :doc:`service-layer-architecture` - Service layer patterns for context management
