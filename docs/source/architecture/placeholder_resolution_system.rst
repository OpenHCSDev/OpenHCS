Placeholder Resolution System
============================

**Dynamic placeholder text generation for lazy dataclass fields using dual-axis resolution.**

*Status: STABLE - Uses Dual-Axis Resolver*
*Module: openhcs.core.lazy_placeholder*

Overview
--------
UI forms need to show meaningful placeholder text when fields are None, but traditional systems show static defaults that don't reflect actual runtime context. The placeholder resolution system generates dynamic placeholder text by using the same dual-axis resolution system that the compiler uses.

The system works by creating temporary instances of lazy dataclasses and asking them to resolve specific field values using the current context. This approach ensures that placeholder text accurately reflects what would happen during actual pipeline execution, eliminating the common problem where UI displays differ from runtime behavior.

**Current Implementation**: The placeholder system has been enhanced to achieve "compiler-grade" resolution by using the same dual-axis resolver as the compilation system. The :pyobject:`openhcs.core.lazy_placeholder.LazyDefaultPlaceholderService` now orchestrates this process with proper orchestrator context injection, ensuring perfect consistency between UI placeholders and compilation behavior.

**Compiler-Grade Resolution (2024 Update)**: The placeholder system now uses the same :pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver` as the compiler, with proper context injection to match compilation behavior exactly. This eliminates the previous inconsistencies between UI display and runtime behavior.

This enables placeholders like "Pipeline default: 4" that reflect the actual inheritance chains used during compilation, providing users with accurate information about what values their configurations will actually use.

LazyDefaultPlaceholderService
-----------------------------
The service provides context-aware placeholder generation using the same dual-axis resolution system as the compiler. This service acts as the bridge between UI components that need placeholder text and the sophisticated resolution logic that determines what values fields would actually resolve to during compilation.

Enhanced Resolution Logic (2024 Update)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The service now achieves "compiler-grade" resolution by using the same :pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver` as the compilation system. The :pyobject:`openhcs.core.lazy_placeholder.LazyDefaultPlaceholderService.get_lazy_resolved_placeholder` method now accepts an optional orchestrator parameter for proper context injection, ensuring perfect consistency with compilation behavior.

.. code-block:: python

   # Enhanced placeholder resolution with orchestrator context
   def get_lazy_resolved_placeholder(self, lazy_class, field_name, orchestrator=None):
       """Generate placeholder using compiler-grade dual-axis resolution."""

       # Use orchestrator context if provided (for step editors)
       if orchestrator:
           with orchestrator.config_context(for_serialization=False):
               lazy_instance = lazy_class()
               resolved_value = getattr(lazy_instance, field_name)
               return f"{self.placeholder_prefix}: {resolved_value}" if resolved_value is not None else None

       # Standard resolution for pipeline/global editors
       lazy_instance = lazy_class()
       resolved_value = getattr(lazy_instance, field_name)
       return f"{self.placeholder_prefix}: {resolved_value}" if resolved_value is not None else None

**Key Enhancement**: The service now uses the orchestrator's :pyobject:`openhcs.core.orchestrator.orchestrator.PipelineOrchestrator.config_context` method for proper context injection, ensuring that placeholder resolution follows the exact same inheritance chains as compilation.

Context Integration
~~~~~~~~~~~~~~~~~~~
The service now integrates with the enhanced context discovery system, using the same context injection mechanisms as the compiler. This ensures that placeholders accurately reflect the resolution behavior that will occur during actual pipeline execution.

**Enhanced Approach**: Uses :pyobject:`openhcs.core.orchestrator.orchestrator.PipelineOrchestrator.config_context` for proper context injection and :pyobject:`openhcs.core.dual_axis_resolver_recursive.ContextDiscovery` for automatic context discovery, matching the compiler's behavior exactly.

Dual-Axis Resolution Integration
--------------------------------
The placeholder system now uses the same dual-axis resolver as the compiler, achieving perfect consistency between UI display and compilation behavior. This unification ensures that placeholder text accurately reflects what values will be used during actual pipeline execution.

Context Discovery for Placeholders
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Placeholder resolution now uses the same context discovery system as compilation. The key insight is that placeholder generation happens within the same context environment as field resolution during compilation, ensuring identical results.

.. code-block:: python

   # Current placeholder resolution approach (2024 implementation)
   def get_placeholder_with_compiler_grade_resolution(lazy_class, field_name, orchestrator=None):
       """Generate placeholder using compiler-grade dual-axis resolver with context injection."""

       # Use orchestrator context if provided (for step editors)
       if orchestrator:
           # Use the same context injection mechanism as the compiler
           with orchestrator.config_context(for_serialization=False):
               lazy_instance = lazy_class()
               resolved_value = getattr(lazy_instance, field_name)
               return f"Pipeline default: {resolved_value}" if resolved_value is not None else "No default"

       # Standard resolution for pipeline/global editors
       lazy_instance = lazy_class()
       resolved_value = getattr(lazy_instance, field_name)
       return f"Pipeline default: {resolved_value}" if resolved_value is not None else "No default"

This approach uses the orchestrator's :pyobject:`openhcs.core.orchestrator.orchestrator.PipelineOrchestrator.config_context` method for proper context injection, creates a lazy instance that will use dual-axis resolution, then accesses the field using the same property-based resolution as the compiler. The result becomes the placeholder text, ensuring perfect consistency.

**Compiler-Grade Resolution**: The placeholder system now achieves "compiler-grade" resolution by using the exact same context injection and field resolution mechanisms as the compilation system, eliminating any possibility of inconsistency between UI display and runtime behavior.

Inheritance Chain Consistency
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The unified system ensures that placeholder resolution follows the exact same inheritance chains as compilation. This mathematical consistency means that users can trust that placeholder text accurately represents what their configurations will actually do.

.. code-block:: python

   # X-axis: Context hierarchy (step → orchestrator → global)
   # Y-axis: Class inheritance (StepMaterializationConfig → StepWellFilterConfig → WellFilterConfig)

   # Placeholder resolution will use same dual-axis algorithm:
   # 1. Discover context hierarchy through stack introspection
   # 2. For each context level, try Y-axis inheritance
   # 3. Return first non-None value found
   # 4. Fallback to static class defaults

The algorithm shown here is identical to what the compiler uses: discover the context hierarchy through stack introspection (step 1), then for each context level, search through class inheritance patterns (step 2). The first concrete value found becomes the resolved value (step 3), with static class defaults as the final fallback (step 4).

This eliminates the current inconsistencies where placeholders might show different values than what the compiler actually resolves, providing users with accurate information about their configuration's behavior.

UI Context Hierarchy
--------------------
Different UI components use different context injection patterns for placeholder resolution.

Step Editor Context
~~~~~~~~~~~~~~~~~~~
Step editors inject orchestrator context to show step configurations that resolve against their parent pipeline configuration:

.. code-block:: python

   # Step editor placeholder resolution
   def create_step_editor_placeholders(orchestrator):
       """Create step editor with orchestrator context injection."""

       # Inject orchestrator context for dual-axis resolution
       ContextInjector.inject_context(orchestrator, "orchestrator")

       # Create lazy config that will resolve through:
       # step context → orchestrator context → global context
       lazy_config = LazyStepMaterializationConfig()

       # Placeholders will show actual inheritance chain values
       return lazy_config

Pipeline Editor Context
~~~~~~~~~~~~~~~~~~~~~~~
Pipeline editors use global context for pipeline-level configuration editing:

.. code-block:: python

   # Pipeline editor placeholder resolution
   def create_pipeline_editor_placeholders(global_config):
       """Create pipeline editor with global context."""

       # Set global context (no orchestrator context injection)
       set_current_global_config(GlobalPipelineConfig, global_config)

       # Pipeline configs resolve directly against global defaults
       lazy_config = LazyPipelineConfig()
       return lazy_config

Global Config Context
~~~~~~~~~~~~~~~~~~~~~
Global config editing shows static defaults since there's no higher-level context:

.. code-block:: python

   # Global config placeholder resolution
   def create_global_config_placeholders():
       """Create global config editor with no context injection."""

       # No context injection - uses static class defaults only
       lazy_config = LazyGlobalPipelineConfig()

       # Placeholders show base class default values
       return lazy_config

Migration Status
----------------
The placeholder resolution system has successfully completed its migration to compiler-grade dual-axis resolution.

**Completed Migration (2024)**: Placeholder resolution now uses the same dual-axis resolver as compilation with proper orchestrator context injection
**Current State**: Perfect consistency between UI placeholders and compilation resolution achieved
**Benefits**:
- Compiler-grade resolution accuracy
- Identical inheritance chain traversal as compilation
- Proper context injection using orchestrator patterns
- Elimination of UI/runtime behavior discrepancies

See Also
--------
- :doc:`configuration_system_architecture` - Dual-axis resolution system architecture
- :doc:`lazy_class_system` - Lazy dataclass system that powers placeholders
- :doc:`context_management_system` - Context discovery and injection patterns
