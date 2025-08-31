Configuration Resolution System
===============================

**Thread-local context management and hierarchical value resolution for lazy configurations.**

*Status: STABLE*
*Module: openhcs.core.config*

Overview
--------

Lazy dataclasses need to resolve values from different sources based on execution context without explicit parameter passing. OpenHCS uses thread-local storage to provide isolated configuration contexts per thread.

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 467-469
   :caption: Basic usage example from openhcs/core/lazy_config.py

This enables context-aware resolution where the same lazy config shows different values based on the current thread's configuration context.

Thread-Local Context System
----------------------------

Generic thread-local storage for configuration contexts. Different operations require different resolution behavior - global editing shows defaults, pipeline editing shows resolved values.

Generic Storage
~~~~~~~~~~~~~~~

Works with any configuration type via type-keyed storage.

.. literalinclude:: ../../../openhcs/core/config.py
   :language: python
   :lines: 242-249
   :caption: Thread-local storage implementation from openhcs/core/config.py

Usage Pattern
~~~~~~~~~~~~~

.. literalinclude:: ../../../openhcs/core/pipeline_config.py
   :language: python
   :lines: 113-118
   :caption: Usage pattern from openhcs/core/pipeline_config.py

Configuration Resolution Hierarchy
-----------------------------------

Resolution Authority
~~~~~~~~~~~~~~~~~~~~

Configuration resolution follows a clear hierarchy:

1. **User-set values** - Explicit user input (highest priority)
2. **Thread-local context** - Current global config instance  
3. **Static defaults** - Dataclass field defaults (lowest priority)

Context-Driven Behavior
~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../../../openhcs/core/config.py
   :language: python
   :lines: 385-410
   :caption: Context resolution patterns from openhcs/core/config.py

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

.. literalinclude:: ../../../openhcs/core/field_path_detection.py
   :language: python
   :lines: 15-35
   :caption: Automatic field path discovery from openhcs/core/field_path_detection.py

UI Context Scoping Patterns
---------------------------

Three UI context types with different resolution behavior.

Context Types
~~~~~~~~~~~~~

**1. Global Config Editing**

Shows actual default values.

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 523-535
   :caption: Global config editor setup from openhcs/core/lazy_config.py

**2. Pipeline Config Editing**

Shows orchestrator values with global fallback.

.. code-block:: python

    # Pipeline editor setup
    orchestrator_config = orchestrator.get_effective_config(for_serialization=False)
    set_current_global_config(GlobalPipelineConfig, orchestrator_config)

    # Lazy resolution from orchestrator config, None values use global defaults

See :doc:`orchestrator_configuration_management` for detailed orchestrator configuration patterns.

**3. Step Config Editing (Scoped)**

Temporary context for step editing with orchestrator→global fallback.

.. literalinclude:: ../../../openhcs/core/config.py
   :language: python
   :lines: 42-60
   :caption: Context manager from openhcs/core/config.py

Context Manager Pattern
~~~~~~~~~~~~~~~~~~~~~~~

Ensures proper context isolation and cleanup.

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 571-582
   :caption: Step editor usage from openhcs/core/lazy_config.py

Context managers provide isolation, cleanup, and safe nesting.

Resolution Hierarchy
~~~~~~~~~~~~~~~~~~~~

Step editor resolution chain:

.. code-block:: python

    # Step's LazyStepMaterializationConfig resolution chain:

    # 1. Check step's materialization_config (user-set values)
    step_value = step.materialization_config.backend
    if step_value is not None:
        return step_value

    # 2. Resolve from orchestrator's materialization_defaults (thread-local)
    orchestrator_config = get_current_global_config(GlobalPipelineConfig)
    orchestrator_value = orchestrator_config.materialization_defaults.backend
    if orchestrator_value is not None:
        return orchestrator_value

    # 3. Fall back to global defaults
    global_default = GlobalPipelineConfig().materialization_defaults.backend
    return global_default

Example: Global=DISK, Orchestrator=None, Step=None → Result: DISK

Thread-Local Requirement
~~~~~~~~~~~~~~~~~~~~~~~~~

Thread-local storage eliminates parameter threading. Without it, every function needs explicit context parameters:

.. code-block:: python

    # Without thread-local (parameter threading nightmare):
    def create_step_form(step, orchestrator_config, global_config, editing_mode):
        return ParameterFormManager(
            step.parameters, orchestrator_config, global_config, editing_mode
        )

    def create_parameter_widget(param, orchestrator_config, global_config, editing_mode):
        placeholder = get_placeholder(param, orchestrator_config, global_config, editing_mode)
        return widget

    def get_placeholder(param, orchestrator_config, global_config, editing_mode):
        # Every function needs all context parameters
        pass

With thread-local, context is ambient:

.. code-block:: python

    def create_step_form(step):
        return ParameterFormManager(step.parameters)  # Context is ambient

    def get_placeholder(param):
        config = get_current_global_config(GlobalPipelineConfig)
        return resolve_from_context(param, config)

Lazy dataclasses require thread-local for resolution:

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 159-162
   :caption: Lazy resolution implementation from openhcs/core/lazy_config.py

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

.. literalinclude:: ../../../openhcs/core/config.py
   :language: python
   :lines: 242-254
   :caption: Thread safety implementation from openhcs/core/config.py

Context Provider Mechanisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Advanced context resolution using custom context providers for specialized scenarios:

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 320-344
   :caption: Advanced context resolution using custom context providers from openhcs/core/lazy_config.py

**Context Provider Pattern:**

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 349-354
   :caption: Context provider pattern from openhcs/core/lazy_config.py

Context Cleanup and Lifecycle Management
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Proper context lifecycle management prevents memory leaks and ensures clean state transitions:

.. literalinclude:: ../../../openhcs/pyqt_gui/widgets/pipeline_editor.py
   :language: python
   :lines: 830-869
   :caption: LazyConfigContext class from openhcs/pyqt_gui/widgets/pipeline_editor.py

**Usage Pattern:**

.. literalinclude:: ../../../openhcs/pyqt_gui/widgets/pipeline_editor.py
   :language: python
   :lines: 364-374
   :caption: Safe context switching from openhcs/pyqt_gui/widgets/pipeline_editor.py

Integration with Lazy Dataclass Resolution
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Thread-local contexts integrate seamlessly with the lazy dataclass resolution system:

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 349-389
   :caption: Field level provider from openhcs/core/lazy_config.py

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

- **Thread Safety**: Each thread has isolated configuration context
- **Explicit Resolution**: Clear hierarchy eliminates ambiguous behavior
- **Type Safety**: Generic storage maintains type information
- **Fail-Loud**: Configuration errors surface immediately
- **Context Awareness**: Behavior adapts to editing context
- **Clean API**: No parameter threading through function calls
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

- :doc:`lazy-class-system` - Dynamic dataclass generation that uses thread-local contexts
- :doc:`step-editor-generalization` - Step editors that rely on context-aware resolution
- :doc:`service-layer-architecture` - Service layer patterns for context management
- :doc:`../development/ui-patterns` - UI patterns that leverage configuration resolution
