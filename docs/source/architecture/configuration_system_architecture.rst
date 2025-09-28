Configuration System Architecture
=================================

Overview
--------

Traditional configuration systems suffer from the "lost edits" problem where user modifications get overwritten by defaults when switching contexts. OpenHCS solves this through lazy dataclasses that resolve values using a sophisticated dual-axis resolution system.

The system treats configuration fields as mathematical variables that can resolve to different values depending on the current context and inheritance relationships. When a field has a ``None`` value, the system automatically searches through multiple sources to find the appropriate value, preserving user edits while providing intelligent defaults.

Configuration classes use Optional fields to indicate which values should participate in lazy resolution, while concrete values represent either user overrides or static class defaults. This design allows the same configuration class to behave differently depending on the context in which it's used.

The :pyobject:`openhcs.core.config.StepMaterializationConfig` dataclass demonstrates this pattern with Optional fields for lazy resolution and concrete values for static overrides. The dual-axis resolution system handles both scenarios automatically through the :pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver`.

In this example, ``well_filter`` is marked as Optional with a None default, signaling that it should resolve through the dual-axis system when accessed. The system will search through step context, then orchestrator context, then global context to find a concrete value. In contrast, ``sub_dir`` has a concrete string default, indicating this is a static override that should always use "checkpoints" regardless of context.

Consider a step materialization configuration where the ``well_filter`` field might inherit from the pipeline's well filter settings, while the ``sub_dir`` field uses a static override specific to materialization steps. The dual-axis resolver handles both scenarios automatically, ensuring that user intentions are preserved while maintaining logical inheritance patterns.

This enables hierarchical configuration flow from specific contexts (Step) through intermediate contexts (Pipeline/Orchestrator) to general contexts (Global), with sophisticated inheritance patterns that respect both user edits and class-level overrides.

Dual-Axis Resolution System
---------------------------

Configuration values resolve through a recursive dual-axis algorithm that combines context hierarchy discovery (X-axis) with class inheritance traversal (Y-axis). This mathematical approach ensures that field resolution follows predictable, debuggable patterns while supporting complex inheritance scenarios.

The **X-axis** represents the context hierarchy, moving from most specific (step-level context) through intermediate levels (orchestrator/pipeline context) to most general (global context). The **Y-axis** represents class inheritance relationships, following Python's Method Resolution Order (MRO) to find fields in parent classes.

**Enhanced Resolution Algorithm (2024 Update)**

The algorithm has been enhanced to provide more predictable inheritance behavior by ensuring each context level is fully exhausted before moving to the next level. This depth-first approach prevents premature context switching and ensures proper inheritance chain traversal.

The enhanced dual-axis resolution algorithm is implemented in :pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver.resolve_field` and :pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver._resolve_field_recursive`. The algorithm combines X-axis context hierarchy traversal (step → orchestrator → global) with Y-axis class inheritance MRO traversal, using depth-first context exhaustion to ensure predictable resolution behavior.

This enhanced algorithm ensures that each context level is fully exhausted through Y-axis inheritance before moving to the next context level. The depth-first approach provides more predictable resolution behavior and ensures that static overrides are properly respected within their context scope.

**Key Improvements:**

- **Depth-First Resolution**: Each context level is fully exhausted before moving up the hierarchy
- **Field-Specific Static Overrides**: Static overrides now block inheritance only for specific fields, not entire classes
- **Enhanced Context Search**: Only searches for exact target types, eliminating cross-type inheritance confusion
- **Direct Global Fallback**: New direct thread-local access method for more reliable global config fallback

:pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver` implements this enhanced algorithm with improved caching and more robust error handling. The :pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver.resolve_field` method now uses the recursive depth-first approach for more predictable inheritance behavior.

Configuration Structure
-----------------------

OpenHCS uses immutable dataclasses that compose together to form the configuration hierarchy.

Core Configuration Classes
~~~~~~~~~~~~~~~~~~~~~~~~~~

**GlobalPipelineConfig**: Top-level configuration containing all subsystem configurations

The :pyobject:`openhcs.core.config.GlobalPipelineConfig` serves as the root configuration object with core execution settings, storage configurations, and subsystem configurations for analysis consolidation, plate metadata, and function registry behavior.

**AnalysisConsolidationConfig**: Controls automatic analysis result consolidation

The :pyobject:`openhcs.core.config.AnalysisConsolidationConfig` manages automatic consolidation of analysis results with MetaXpress-style output formatting and configurable file patterns.

**PlateMetadataConfig**: MetaXpress-compatible plate metadata

The :pyobject:`openhcs.core.config.PlateMetadataConfig` provides MetaXpress-compatible plate metadata fields for analysis consolidation and HCS viewing compatibility.

Context Discovery System
------------------------

Configuration contexts are discovered automatically through stack introspection, eliminating the need for explicit parameter passing. The system uses an enhanced frame injection mechanism where context objects are temporarily placed into the call stack's local variables, allowing the resolver to find them through systematic stack traversal.

**Enhanced Frame Injection (2024 Update)**

The frame injection system has been significantly enhanced to provide more reliable context discovery with proper cleanup and safety mechanisms. The new implementation injects context into multiple frames to ensure discovery reliability and includes comprehensive error handling.

The enhanced frame injection system is implemented in :pyobject:`openhcs.core.orchestrator.orchestrator.PipelineOrchestrator.config_context` with multi-frame support and proper cleanup mechanisms. Context discovery is handled by :pyobject:`openhcs.core.dual_axis_resolver_recursive.ContextDiscovery.discover_context` with safety limits and comprehensive error handling.

**Key Enhancements:**

- **Multi-Frame Injection**: Context is injected into multiple frames to ensure reliable discovery
- **Safety Limits**: Frame traversal is limited to prevent infinite loops
- **Proper Cleanup**: Context variables are properly cleaned up after use
- **Enhanced Error Handling**: Null checks and frame validation prevent crashes
- **Injected Context Priority**: Explicitly injected contexts take priority over discovered contexts

The enhanced injection process uses ``inspect.currentframe()`` to walk up the call stack and inject the context variable into multiple frames. This ensures that the context discovery process can find the context even if the call stack structure varies. The discovery process includes safety limits and proper null checking to prevent infinite loops or crashes.

The :pyobject:`openhcs.core.orchestrator.orchestrator.PipelineOrchestrator` now provides enhanced context injection through its :pyobject:`openhcs.core.orchestrator.orchestrator.PipelineOrchestrator.config_context` method, while :pyobject:`openhcs.core.dual_axis_resolver_recursive.ContextDiscovery` implements the enhanced discovery algorithm with safety mechanisms.

This approach provides robust automatic context discovery without requiring explicit parameter threading through function calls, making the configuration system transparent to consuming code while maintaining sophisticated resolution capabilities and preventing common failure modes.

Lazy Dataclass Factory
-----------------------

The LazyDataclassFactory generates runtime dataclasses with dual-axis field resolution. This factory pattern creates new classes that maintain the same interface as the original dataclass but replace field access with sophisticated resolution logic that can traverse context hierarchies and class inheritance patterns.

The factory works by creating a new class dynamically at runtime that has the same fields and interface as the original dataclass, but replaces simple field access with property methods that delegate to the dual-axis resolver. This allows existing code to continue using familiar dataclass patterns while gaining sophisticated inheritance capabilities.

The :pyobject:`openhcs.core.lazy_config.LazyDataclassFactory.make_lazy_simple` method creates lazy configurations with contextvars-based resolution. These lazy configs resolve field values through the new simplified context system and class inheritance patterns, enabling sophisticated configuration inheritance while maintaining the familiar dataclass interface.

This example shows the factory creating a lazy version of ``StepMaterializationConfig``. The ``base_class`` parameter specifies the original dataclass to wrap, while ``global_config_type`` indicates what type of global configuration this should resolve against. The ``field_path`` tells the system where to find instances of this config type within the global configuration structure. When ``config.well_filter`` is accessed, it triggers the dual-axis resolution process instead of returning a simple field value.

The :pyobject:`openhcs.core.lazy_config.LazyDataclassFactory` creates these runtime classes by examining the original dataclass structure and generating property methods that delegate to the dual-axis resolver. The :pyobject:`openhcs.core.lazy_config.LazyDataclassFactory.make_lazy_simple` method is the primary entry point, using the new simplified contextvars system for field resolution.

This enables sophisticated inheritance patterns where fields can inherit from sibling configurations at the same hierarchy level, while maintaining the familiar dataclass interface that consuming code expects.

Context Hierarchy and Inheritance
---------------------------------

The dual-axis resolver combines context hierarchy discovery with sophisticated inheritance patterns.

Context Hierarchy (X-Axis)
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Contexts are discovered in priority order through stack introspection:

Context hierarchy discovery is implemented in :pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver._discover_context_hierarchy`, which builds the complete context hierarchy from most specific (step) to least specific (global) using recursive parent context discovery.

Class Inheritance (Y-Axis)
~~~~~~~~~~~~~~~~~~~~~~~~~~~

For each context level, the resolver searches through the class inheritance hierarchy:

Y-axis class inheritance traversal is handled by :pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver._resolve_at_context_level`, which searches through the class inheritance hierarchy using Python's MRO and :pyobject:`openhcs.core.field_path_detection.FieldPathDetector` for automatic field path discovery.

Static Override Detection
~~~~~~~~~~~~~~~~~~~~~~~~~

The system detects when subclasses override parent class defaults:

Static override detection is implemented in :pyobject:`openhcs.core.dual_axis_resolver_recursive.RecursiveContextualResolver._check_static_override`, which compares field defaults across the inheritance hierarchy to detect when subclasses override parent class defaults for specific fields.

This ensures that static class overrides (like `sub_dir = "checkpoints"`) take precedence over inherited values.

Integration Examples
-------------------

The dual-axis resolution system integrates with compilation and UI systems.

Compilation Integration
~~~~~~~~~~~~~~~~~~~~~~~

The compiler uses the same dual-axis resolver to ensure consistency between UI and execution:

**Compilation Integration**: The compiler uses the same dual-axis resolver with proper context injection to ensure consistency between UI and execution environments.

UI Integration
~~~~~~~~~~~~~~

UI components use the same resolver for placeholder generation:

**UI Integration**: UI components use the same resolver for placeholder generation, ensuring perfect consistency between UI placeholders and compilation resolution through :pyobject:`openhcs.core.lazy_placeholder.LazyDefaultPlaceholderService`.

**Key Benefits**:

- **Consistency**: UI placeholders match compilation resolution exactly
- **Automatic Context Discovery**: No explicit parameter threading required
- **Sophisticated Inheritance**: Supports sibling inheritance and static overrides
- **Frame Injection Safety**: Proper cleanup prevents memory leaks
- **Single-Threaded Safety**: Frame injection works correctly in OpenHCS's single-threaded compilation model

Troubleshooting Resolution Issues
---------------------------------

Troubleshooting Resolution Issues
---------------------------------

**Context Discovery Failures**: When lazy configs resolve to static defaults instead of inheriting from context, check that context injection is happening properly and context variables follow the naming pattern ``__*_context__``.

**Inheritance Chain Issues**: When fields don't inherit from sibling configurations, verify that the dual-axis resolver is properly resolving cross-dataclass inheritance using the new contextvars system.

**Static Override Problems**: When static overrides don't take precedence, ensure that :pyobject:`openhcs.core.dual_axis_resolver_recursive._has_concrete_field_override` is detecting field-level differences correctly.

The dual-axis resolution system provides comprehensive debugging capabilities through its resolver methods to help identify and resolve inheritance behavior issues.
