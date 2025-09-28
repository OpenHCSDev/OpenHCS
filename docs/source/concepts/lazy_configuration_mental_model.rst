Lazy Configuration Mental Model
===============================

**Understanding the "lost edits" problem and how lazy resolution preserves user intent**

*Target Audience: New users encountering OpenHCS configuration forms*
*Prerequisites: Basic understanding of configuration files and UI forms*

The Problem: Lost Edits in Traditional Systems
----------------------------------------------

Traditional configuration systems suffer from a fundamental problem that destroys user productivity: **user edits get overwritten when switching contexts**.

**Scenario**: You're configuring an image processing pipeline:

1. Set ``num_workers = 8`` for your specific pipeline
2. Switch to global settings to check GPU configuration  
3. Return to your pipeline configuration
4. **Your edit is gone** - ``num_workers`` shows the global default (4) instead of your value (8)

This happens because traditional systems don't distinguish between:
- **User intent**: "I specifically want this value"
- **Default inheritance**: "Use the parent context's value"

**Impact**: Users lose work, avoid configuration changes, or resort to external notes to track their edits.

The Solution: Lazy Resolution with Context Awareness
----------------------------------------------------

OpenHCS solves this through **lazy configuration resolution** - a mathematical approach that preserves user intent while providing intelligent defaults.

:py:func:`~openhcs.core.lazy_config.create_dataclass_for_editing` creates configurations that distinguish between user-set values and inherited defaults. When you explicitly set a value, it's marked as "user intent" and never overwritten. When you leave a field empty (None), it resolves from the appropriate context hierarchy.

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 574-587
   :caption: Creating editable configs with configurable value preservation

**Key Insight**: The ``preserve_values`` parameter controls whether existing user edits are maintained or reset to None for fresh inheritance.

Mental Model: Smart Defaults That Remember
------------------------------------------

Think of lazy configurations as **smart defaults that remember your intent**:

**None Values (Inheritance Mode)**:
  "I want to inherit from parent context - show me what that would be"

**Explicit Values (User Intent Mode)**:  
  "I specifically want this value - don't change it when context changes"

**Context Switching**:
  Preserves your explicit choices while updating inherited placeholders

This enables the mathematical hierarchy: **Global → Pipeline → Step**, where each level can override specific fields while inheriting others.

How Lazy Resolution Works
-------------------------

:py:meth:`~openhcs.core.lazy_config.LazyDataclassFactory.make_lazy_simple` creates dataclasses with custom field resolution behavior using the new simplified contextvars system. Instead of storing static values, fields resolve dynamically based on the current context.

**Resolution Chain**:

1. **User-set value**: If you explicitly set a field, use that value
2. **Thread-local context**: Check current pipeline/global configuration  
3. **Static defaults**: Fall back to base class defaults

.. code-block:: python
   :caption: Simplified lazy factory with contextvars

   # New simplified factory method
   lazy_class = LazyDataclassFactory.make_lazy_simple(
       base_class=StepMaterializationConfig,
       lazy_class_name="LazyStepMaterializationConfig"
   )

   # Use within explicit context
   with config_context(pipeline_config):
       lazy_instance = lazy_class()
       # Fields resolve through contextvars system

**Mathematical Foundation**: This implements a **context-dependent function** where the same field can resolve to different values based on the current mathematical environment (thread-local context).

Visual Representation in UI Forms
---------------------------------

The lazy configuration system manifests visually through **placeholder text** that shows inheritance relationships:

**Empty Field (None value)**:
  Shows ``"Pipeline default: 4"`` - indicating inheritance from pipeline context

**User-Set Field (Explicit value)**:
  Shows ``8`` with no placeholder - indicating user intent

:py:meth:`~openhcs.core.lazy_placeholder.LazyDefaultPlaceholderService.get_lazy_resolved_placeholder` generates these dynamic placeholders by temporarily resolving the field against current context.

**UI Behavior**:
- Placeholders update when parent contexts change
- User values remain stable during context changes  
- Clear visual distinction between inherited and explicit values

Thread-Local Context Management
-------------------------------

:py:func:`~openhcs.core.context.global_config.get_current_global_config` provides the mathematical environment for lazy resolution. This thread-local storage ensures that different UI components can have different resolution contexts without parameter passing.

**Context Hierarchy**:
- **Global Config**: Base mathematical environment
- **Pipeline Config**: Inherits from global, adds pipeline-specific values
- **Step Config**: Inherits from pipeline, adds step-specific values

**Thread Safety**: Each UI thread maintains its own context stack, preventing interference between different editing sessions.

Practical Usage Patterns
------------------------

**Pattern 1: Selective Override**
```python
# Pipeline config inherits most values from global
pipeline_config.num_workers = None      # Inherits from global (4)
pipeline_config.gpu_enabled = True      # Override for this pipeline
pipeline_config.output_format = None    # Inherits from global ("tiff")
```

**Pattern 2: Context-Aware Editing**
```python
# Step config inherits from pipeline context
step_config.num_workers = 8            # Override for this step only
step_config.gpu_enabled = None         # Inherits from pipeline (True)
```

**Pattern 3: Preservation During Context Switching**
```python
# User edits preserved when switching between configurations
with pipeline_context:
    step_config.num_workers = 8        # User intent preserved
    
with different_pipeline_context:
    # step_config.num_workers still equals 8 (user intent)
    # But placeholders for None fields update to new context
```

Benefits for Users
------------------

**Productivity**: Never lose configuration edits when switching contexts

**Clarity**: Visual distinction between inherited and explicit values

**Flexibility**: Override specific fields while inheriting others

**Predictability**: Same configuration behaves consistently across contexts

**Mathematical Correctness**: Configuration relationships reflect actual inheritance hierarchies

Common Patterns and Anti-Patterns
---------------------------------

**✅ Correct Usage**:
- Set fields to None when you want inheritance
- Set explicit values when you want to override
- Use context switching to see inheritance relationships

**❌ Anti-Patterns**:
- Manually copying values between configuration levels
- Avoiding configuration changes due to fear of losing edits
- Using external tools to track configuration state

**Debugging Tip**: If placeholders show unexpected values, check the thread-local context using debug output from :py:func:`~openhcs.core.context.global_config.get_current_global_config`.

Integration with OpenHCS Architecture
-------------------------------------

The lazy configuration system integrates with every part of OpenHCS that handles user preferences:

- **UI Forms**: Parameter form managers use lazy configs for all editing
- **Pipeline Compilation**: Lazy configs resolve to concrete values during execution
- **Serialization**: Only user-set values are saved, preserving inheritance relationships
- **Context Management**: Thread-local storage provides mathematical environment

This creates a **mathematically coherent** system where configuration relationships are preserved throughout the entire application lifecycle.

Next Steps
----------

- **For Basic Usage**: See :doc:`inheritance_and_placeholders` to understand the visual inheritance system
- **For Advanced Usage**: See :doc:`configuration_as_mathematics` to understand the mathematical foundations
- **For Debugging**: See :doc:`debugging_complex_systems` for troubleshooting configuration issues
