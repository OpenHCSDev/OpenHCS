Lazy Configuration System
=========================

**Dynamic dataclass generation with field-level hierarchy resolution and sibling inheritance.**

*Status: STABLE*
*Module: openhcs.core.lazy_config*

Overview
--------

Traditional configuration systems suffer from the "lost edits" problem - user modifications get overwritten by defaults when switching contexts. OpenHCS solves this through lazy dataclasses that resolve values from different sources based on editing context.

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 301-315
   :caption: Entry point for creating lazy dataclasses with custom resolution logic.

The system generates runtime dataclasses with custom resolution logic that preserves user edits while providing appropriate defaults. This enables hierarchical configuration flow (Global → Pipeline → Step) with sophisticated sibling inheritance patterns.

LazyDataclassFactory
--------------------

The LazyDataclassFactory generates runtime dataclasses with custom resolution logic. It takes a regular dataclass and creates a new class with the same interface but lazy field resolution behavior.

.. literalinclude:: ../../../openhcs/core/pipeline_config.py
   :language: python
   :lines: 113-118
   :caption: Real example from openhcs/core/pipeline_config.py

The factory pattern enables different resolution strategies for different use cases while preserving the original dataclass interface.

Field-Level Auto-Hierarchy Resolution
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The primary factory method uses automatic field path discovery with sophisticated sibling inheritance:

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 319-326
   :caption: Method signature from openhcs/core/lazy_config.py

**Nested Configuration Example**

For nested configurations, the auto-hierarchy constructor automatically discovers field paths:

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 589-600
   :caption: Automatic lazy config generation from openhcs/core/lazy_config.py

Key Differences Between Constructors
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Thread-Local vs Auto-Hierarchy:**

.. list-table::
   :header-rows: 1
   :widths: 30 35 35

   * - Aspect
     - Thread-Local
     - Auto-Hierarchy
   * - **Resolution Strategy**
     - Simple field path navigation
     - Field-level inheritance discovery
   * - **Use Case**
     - Main config classes (PipelineConfig)
     - Nested configs (LazyStepMaterializationConfig)
   * - **Hierarchy Support**
     - Basic recursive resolution
     - Sophisticated sibling inheritance
   * - **Context Provider**
     - Thread-local only
     - Supports custom context providers
   * - **Field Path Detection**
     - Manual explicit paths
     - Automatic introspection
   * - **Current Usage**
     - Root PipelineConfig creation
     - All auto-generated lazy configs

**When to Use Which:**

- **Thread-Local**: For root configuration classes that resolve directly from thread-local storage
- **Auto-Hierarchy**: For nested configurations that need sophisticated inheritance relationships

Dynamic Class Generation
~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 277-294
   :caption: Dynamic class generation from openhcs/core/lazy_config.py

Resolution Mechanisms
---------------------

Field Value Resolution
~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 159-162
   :caption: Field resolution from openhcs/core/lazy_config.py

Recursive Resolution
~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 221-230
   :caption: Automatic nested lazy dataclass creation logic.

Structure Preservation
----------------------

User Value Tracking
~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 544-559
   :caption: Rebuild lazy config to reference new global config while preserving field states.

Safe Instance Handling
~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 133-153
   :caption: Get raw field value bypassing lazy property getters.

Lifecycle Management
--------------------

Instantiation Pattern
~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 156-188
   :caption: Declarative method bindings that enable lazy field resolution on access.

Thread-Local Integration
~~~~~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../../../openhcs/core/config.py
   :language: python
   :lines: 245-249
   :caption: Set current global config for any dataclass type in thread-local storage.

Advanced Inheritance Patterns
-----------------------------

The UI refactor introduced sophisticated inheritance mechanisms that enable complex configuration scenarios while maintaining simplicity for consuming code.

Multi-Level Resolution Chains
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

OpenHCS implements a hierarchical resolution system where configuration values flow through multiple levels:

**Resolution Hierarchy:**

1. **Step Level**: Individual step configuration (highest priority for user edits)
2. **Orchestrator Level**: Pipeline-specific configuration
3. **Global Level**: Application-wide defaults (lowest priority)

.. code-block:: python

    # Example: output_dir_suffix resolution chain
    # 1. Step level (None) → 2. Pipeline level ("_custom") → 3. Global level ("_openhcs")

    step_config = LazyStepMaterializationConfig()  # All None values
    step_config.output_dir_suffix  # Resolves to "_custom" from pipeline level

**Real-World Resolution Example:**

.. code-block:: python

    # Global configuration (application defaults)
    global_config = GlobalPipelineConfig(
        path_planning=PathPlanningConfig(output_dir_suffix="_openhcs"),
        materialization_defaults=StepMaterializationConfig(output_dir_suffix="_openhcs")
    )

    # Pipeline configuration (user overrides)
    pipeline_config = PipelineConfig(
        path_planning=LazyPathPlanningConfig(output_dir_suffix="_pipeline_custom"),
        materialization_defaults=LazyStepMaterializationConfig()  # None values
    )

    # Step configuration (inherits from pipeline)
    step_config = LazyStepMaterializationConfig()

    # Resolution chain:
    # step_config.output_dir_suffix (None)
    # → pipeline.materialization_defaults.output_dir_suffix (None)
    # → pipeline.path_planning.output_dir_suffix ("_pipeline_custom") ✅

Sibling Inheritance Mechanisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

One of the most sophisticated features is **sibling inheritance** - where fields can inherit from related configurations at the same hierarchy level.

**Sibling Inheritance Pattern:**

.. code-block:: python

    # StepMaterializationConfig inherits shared fields from PathPlanningConfig
    # when those fields are None in the materialization config

    class StepMaterializationConfig:
        output_dir_suffix: Optional[str] = None  # Can inherit from PathPlanningConfig
        sub_dir: Optional[str] = None            # Own field, no inheritance

    class PathPlanningConfig:
        output_dir_suffix: Optional[str] = "_openhcs"  # Shared field

**How Sibling Inheritance Works:**

1. **Field Classification**: Fields are classified as "inherited" (shared with siblings) or "own" (unique to this config)
2. **Hierarchy Building**: Resolution paths include both direct paths and sibling paths
3. **Context-Aware Resolution**: Uses current context (pipeline config) and global context separately

.. code-block:: python

    # Hierarchy paths for StepMaterializationConfig.output_dir_suffix:
    hierarchy_paths = [
        ('current', 'materialization_defaults'),  # Direct path
        ('current', 'path_planning'),             # Sibling inheritance ✅
        ('global', 'materialization_defaults'),   # Global direct
        ('global', 'path_planning')               # Global sibling
    ]

**Sibling Inheritance Example:**

.. code-block:: python

    # User sets path_planning.output_dir_suffix = "_custom"
    # materialization_defaults.output_dir_suffix = None (inherits from sibling)

    pipeline_config = PipelineConfig(
        path_planning=LazyPathPlanningConfig(output_dir_suffix="_custom"),
        materialization_defaults=LazyStepMaterializationConfig()  # None values
    )

    # Sibling inheritance in action:
    value = pipeline_config.materialization_defaults.output_dir_suffix
    # Result: "_custom" (inherited from sibling path_planning)

Context-Aware Resolution Patterns
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The system uses **context providers** to enable sophisticated resolution scenarios where the resolution context can be different from the global thread-local context.

**Context Provider Pattern:**

.. code-block:: python

    def create_context_aware_lazy_class(base_class, parent_instance):
        """Create lazy class that resolves from specific parent instance."""

        def context_provider():
            return parent_instance  # Use specific instance, not global context

        return LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
            base_class=base_class,
            global_config_type=GlobalPipelineConfig,
            field_path="materialization_defaults",
            context_provider=context_provider  # Custom context
        )

**Context Propagation in Nested Resolution:**

.. code-block:: python

    # Parent instance provides context for nested lazy classes
    def nested_context_provider():
        if parent_instance_provider:
            parent_instance = parent_instance_provider()
            if parent_instance:
                return parent_instance  # Use parent's context

        # Fall back to global config
        return get_current_global_config(global_config_type)

This enables scenarios where nested configurations resolve from their immediate parent rather than the global thread-local context, crucial for step editor functionality.

Preservation of User Edits
---------------------------

One of the most critical aspects of the lazy class system is preserving user edits while maintaining lazy resolution capabilities. This was a major source of bugs before the UI refactor.

Structure Preservation System
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The system uses a three-method preservation approach to handle the complex interaction between user edits and lazy resolution:

.. code-block:: python

    def _preserve_lazy_structure_if_needed(self, field_name: str, value: Any) -> Any:
        """Core preservation logic - maintains user intent vs lazy resolution."""

        # Mark as user-set to prevent lazy resolution override
        object.__setattr__(self, f'_{field_name}_user_set', True)
        object.__setattr__(self, f'_{field_name}', value)

        # Handle nested dataclass preservation
        if dataclasses.is_dataclass(value):
            return self._rebuild_nested_dataclass_instance(value, field_name)

        return value

    def _convert_to_lazy_dataclass(self, value: Any, field_type: Type) -> Any:
        """Safe conversion to lazy dataclass when needed."""
        if LazyDefaultPlaceholderService.has_lazy_resolution(field_type):
            # Already a lazy dataclass - preserve as-is
            return value
        else:
            # Convert to lazy version for proper inheritance
            return self._create_lazy_version(value, field_type)

    def _rebuild_nested_dataclass_instance(self, nested_values: Dict[str, Any],
                                         nested_type: Type, param_name: str) -> Any:
        """Recursive reconstruction of nested dataclass instances."""
        nested_type_is_lazy = LazyDefaultPlaceholderService.has_lazy_resolution(nested_type)

        if nested_type_is_lazy:
            # Lazy dataclass: preserve None values for lazy resolution
            # This maintains "lazy mixed" pattern - some concrete, some None
            return nested_type(**nested_values)
        else:
            # Non-lazy dataclass: filter out None values
            filtered_values = {k: v for k, v in nested_values.items() if v is not None}
            return nested_type(**filtered_values) if filtered_values else nested_type()

Mixed State Management
~~~~~~~~~~~~~~~~~~~~~~

A key innovation is **mixed state management** - the ability for a single dataclass instance to have some fields with concrete user values and other fields with None values that resolve lazily.

.. code-block:: python

    # Example: Mixed state in StepMaterializationConfig
    step_config = LazyStepMaterializationConfig(
        output_dir_suffix="_user_custom",  # Concrete user value
        sub_dir=None,                      # Lazy resolution from hierarchy
        force_disk_output=True             # Concrete user value
    )

    # Field access behavior:
    step_config.output_dir_suffix  # Returns "_user_custom" (user-set)
    step_config.sub_dir           # Resolves from pipeline → global hierarchy
    step_config.force_disk_output # Returns True (user-set)

**Why Mixed State Matters:**

1. **User Intent Preservation**: User edits are never lost, even when other fields change
2. **Selective Inheritance**: Users can override specific fields while inheriting others
3. **Context Sensitivity**: Same instance behaves differently based on resolution context

Recursive Reconstruction
~~~~~~~~~~~~~~~~~~~~~~~~

When nested dataclasses are modified, the system recursively rebuilds the entire structure while preserving user edits at every level:

.. code-block:: python

    def rebuild_lazy_config_with_new_global_reference(
        current_config: Any,
        new_global_config: Any,
        global_config_type: Type
    ) -> Any:
        """Rebuild entire config hierarchy with new global reference."""

        current_field_values = {}

        for field_obj in fields(type(current_config)):
            raw_value = _get_raw_field_value(current_config, field_obj.name)

            if raw_value is not None and hasattr(raw_value, '__dataclass_fields__'):
                # Nested dataclass - recursively rebuild
                rebuilt_nested_value = rebuild_lazy_config_with_new_global_reference(
                    raw_value, new_global_config, global_config_type
                )
                current_field_values[field_obj.name] = rebuilt_nested_value
            else:
                # Regular field - preserve as-is
                current_field_values[field_obj.name] = raw_value

        return type(current_config)(**current_field_values)

This ensures that when global configuration changes, all existing lazy instances are updated while preserving their user-set values.

Real-World Inheritance Examples
-------------------------------

These examples demonstrate the complex inheritance scenarios that the lazy class system handles in practice.

Example 1: Step Editor Configuration
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Scenario**: User editing a step's materialization configuration in the step editor.

.. code-block:: python

    # Global configuration (application defaults)
    global_config = GlobalPipelineConfig(
        path_planning=PathPlanningConfig(output_dir_suffix="_openhcs"),
        materialization_defaults=StepMaterializationConfig(
            output_dir_suffix="_openhcs",
            sub_dir="processed",
            force_disk_output=False
        )
    )

    # Pipeline configuration (user customizations)
    pipeline_config = PipelineConfig(
        path_planning=LazyPathPlanningConfig(output_dir_suffix="_pipeline_custom"),
        materialization_defaults=LazyStepMaterializationConfig()  # All None - inherits
    )

    # Step configuration (step-specific overrides)
    step_config = LazyStepMaterializationConfig(
        sub_dir="_step_specific"  # User override for this step only
    )

    # Resolution results:
    step_config.output_dir_suffix  # "_pipeline_custom" (from pipeline path_planning)
    step_config.sub_dir           # "_step_specific" (user override)
    step_config.force_disk_output # False (from global defaults)

**Resolution Chain Analysis:**

1. ``output_dir_suffix``: None (step) → None (pipeline materialization) → "_pipeline_custom" (pipeline path_planning) ✅
2. ``sub_dir``: "_step_specific" (step user override) ✅
3. ``force_disk_output``: None (step) → None (pipeline materialization) → False (global materialization) ✅

Example 2: Complex Sibling Inheritance
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Scenario**: Multiple configuration types sharing fields with different inheritance patterns.

.. code-block:: python

    # User sets path planning configuration
    pipeline_config = PipelineConfig(
        path_planning=LazyPathPlanningConfig(
            output_dir_suffix="_user_custom",
            input_dir_prefix="raw_",
            temp_dir_suffix="_temp"
        ),
        materialization_defaults=LazyStepMaterializationConfig(),  # Inherits from path_planning
        vfs=LazyVFSConfig()  # Also inherits shared fields
    )

    # Sibling inheritance results:
    # StepMaterializationConfig inherits output_dir_suffix from PathPlanningConfig
    pipeline_config.materialization_defaults.output_dir_suffix  # "_user_custom"

    # VFSConfig inherits different fields from PathPlanningConfig
    pipeline_config.vfs.temp_dir_suffix  # "_temp"

    # Non-shared fields resolve independently
    pipeline_config.materialization_defaults.sub_dir  # None → resolves from global
    pipeline_config.vfs.backend_type  # None → resolves from global

Example 3: Context-Aware Step Editor
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Scenario**: Step editor showing placeholders that reflect the actual inheritance chain.

.. code-block:: python

    # Set up pipeline context
    set_current_global_config(GlobalPipelineConfig, global_config)

    # Create step editor with context-aware lazy config
    def create_step_editor_config(pipeline_config):
        """Create step config that resolves from pipeline context."""

        def context_provider():
            return pipeline_config  # Use pipeline as resolution context

        return LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
            base_class=StepMaterializationConfig,
            global_config_type=GlobalPipelineConfig,
            field_path="materialization_defaults",
            context_provider=context_provider
        )

    # Step editor configuration
    StepEditorConfig = create_step_editor_config(pipeline_config)
    step_editor_config = StepEditorConfig()

    # UI placeholder text generation:
    # "Pipeline default: _user_custom" (shows actual pipeline value)
    placeholder_text = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        StepEditorConfig, "output_dir_suffix", placeholder_prefix="Pipeline default"
    )

Example 4: Mixed State Preservation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Scenario**: User makes partial edits to a configuration, system preserves user intent.

.. code-block:: python

    # Initial state: all lazy resolution
    config = LazyStepMaterializationConfig()

    # User edits one field
    config = config.replace(output_dir_suffix="_user_override")

    # System state after edit:
    # - output_dir_suffix: "_user_override" (concrete user value)
    # - sub_dir: None (still lazy, resolves from hierarchy)
    # - force_disk_output: None (still lazy, resolves from hierarchy)

    # Global config changes
    new_global = GlobalPipelineConfig(
        materialization_defaults=StepMaterializationConfig(
            output_dir_suffix="_new_global",
            sub_dir="updated",
            force_disk_output=True
        )
    )

    # After global config update:
    config.output_dir_suffix  # "_user_override" (preserved user edit)
    config.sub_dir           # "updated" (new global value)
    config.force_disk_output # True (new global value)

Example 5: Compiler Context Resolution
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Scenario**: Pipeline compilation with different resolution context than UI.

.. code-block:: python

    # UI context: Uses pipeline config with None values (enables sibling inheritance)
    ui_context = pipeline_config  # Has None values in materialization_defaults

    # Compiler context: Uses resolved effective config
    effective_config = pipeline_config.to_base_config()  # All values resolved

    # Different resolution results:

    # UI resolution (correct):
    with LazyConfigContext(ui_context):
        step_config = LazyStepMaterializationConfig()
        ui_value = step_config.output_dir_suffix  # "_pipeline_custom" (from path_planning)

    # Compiler resolution (was broken, now fixed):
    with LazyConfigContext(ui_context):  # Use unresolved context, not effective
        step_config = LazyStepMaterializationConfig()
        compiler_value = step_config.output_dir_suffix  # "_pipeline_custom" (same as UI)

This example shows how the context-aware resolution system ensures consistency between UI and compilation phases.

Benefits
--------

- **Lazy Resolution**: Values computed only when accessed
- **Context Awareness**: Automatic thread-local context integration
- **Structure Preservation**: User edits preserved across operations
- **Type Safety**: Generated classes maintain original type contracts
- **Recursive Support**: Automatic nested lazy dataclass creation
- **Multi-Level Hierarchy**: Step → Pipeline → Global resolution chains
- **Sibling Inheritance**: Cross-configuration field inheritance
- **Context Propagation**: Flexible resolution context management

See Also
--------

- :doc:`configuration-resolution` - Thread-local context management and resolution patterns
- :doc:`step-editor-generalization` - How step editors use lazy dataclass patterns
- :doc:`field-path-detection` - Automatic field path discovery for lazy config generation
- :doc:`service-layer-architecture` - Framework-agnostic business logic that works with lazy configs
- :doc:`../development/ui-patterns` - UI patterns that leverage lazy dataclass systems
