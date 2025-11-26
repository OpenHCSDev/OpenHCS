========================================
Reactive UI Performance Optimizations
========================================

Overview
========

OpenHCS implements a sophisticated reactive UI system where configuration changes in one window automatically update placeholders and visual feedback in all other open windows. This document describes the performance optimizations implemented to achieve real-time responsiveness (<16ms incremental updates for 60 FPS) while maintaining architectural correctness.

.. contents:: Table of Contents
   :local:
   :depth: 2

Background: The Reactive UI System
===================================

Architecture
------------

The reactive UI system operates on two axes:

**X-Axis: Context Hierarchy**
   - GlobalPipelineConfig → PipelineConfig → FunctionStep
   - Each level can inherit values from parent levels
   - Changes propagate down the hierarchy

**Y-Axis: MRO Inheritance**
   - Config types inherit from base types via Python's Method Resolution Order (MRO)
   - Example: ``StepMaterializationConfig`` inherits from ``WellFilterConfig``
   - Changes to base types affect all derived types

Key Components
--------------

**LiveContextSnapshot**
   Captures the current state of all active form managers, including:
   
   - ``values``: Global configuration values (e.g., from GlobalPipelineConfig editor)
   - ``scoped_values``: Plate/step-specific values (e.g., from PipelineConfig or step editors)
   - ``token``: Incremental counter for cache invalidation

**Token-Based Cache Invalidation**
   - ``_live_context_token_counter`` increments on every configuration change
   - All caches are keyed by ``(cache_key, token)``
   - Token increment invalidates all caches globally in O(1)

**Cross-Window Signals**
   - ``parameter_changed``: Emitted when a parameter changes (parent config name for nested fields)
   - ``context_value_changed``: Emitted with full field path (e.g., ``"PipelineConfig.well_filter_config.well_filter"``)

Performance Challenge
=====================

The original implementation had O(n_managers × n_steps) complexity on every keystroke, causing noticeable lag when multiple windows were open. The goal was to achieve <16ms incremental updates (60 FPS) while maintaining correct cross-window reactivity.

Phase 1-ALT: Type-Based Caching
================================

Problem
-------

The original fast-path check iterated through all active form managers on every change, checking if any manager had emitted values. This was O(n_managers) per check, and with multiple windows open, this became expensive.

Solution
--------

Implemented a type-based cache that tracks which config types have unsaved changes:

.. code-block:: python

   # Class-level cache in ParameterFormManager
   _configs_with_unsaved_changes: Dict[Type, Set[str]] = {}
   
   # Maps config type → set of changed field names
   # Example: {WellFilterConfig: {"well_filter", "well_filter_mode"}}

When a parameter changes, the config type is marked in the cache. When checking for unsaved changes, we first check if the config type is in the cache (O(1) lookup) before doing expensive field resolution.

Implementation Details
----------------------

**Cache Structure**

Located in ``openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py``:

.. code-block:: python

   class ParameterFormManager:
       # Type-based cache for unsaved changes detection
       _configs_with_unsaved_changes: Dict[Type, Set[str]] = {}
       MAX_CONFIG_TYPE_CACHE_ENTRIES = 50

**Marking Config Types**

When ``context_value_changed`` is emitted, ``_mark_config_type_with_unsaved_changes()`` extracts the config type and field name from the full field path:

.. code-block:: python

   def _mark_config_type_with_unsaved_changes(self, param_name: str, value: Any):
       # Extract config attribute and field name
       # Example: "well_filter_config.well_filter" → config_attr="well_filter_config", field_name="well_filter"
       config_attr = param_name.split('.')[0] if '.' in param_name else param_name
       config = getattr(self.object_instance, config_attr, None)

       if config is not None and dataclasses.is_dataclass(config):
           config_type = type(config)  # e.g., WellFilterConfig
           field_name = param_name.split('.')[-1]  # e.g., "well_filter"

           # Mark the directly edited type
           if config_type not in type(self)._configs_with_unsaved_changes:
               type(self)._configs_with_unsaved_changes[config_type] = set()
           type(self)._configs_with_unsaved_changes[config_type].add(field_name)

**Fast-Path Check**

In ``openhcs/pyqt_gui/widgets/config_preview_formatters.py``, the fast-path check uses the cache:

.. code-block:: python

   def check_step_has_unsaved_changes(step, ...):
       # Fast-path: Check if any step config type is in the cache
       for config_attr, config in step_configs.items():
           config_type = type(config)
           if config_type in ParameterFormManager._configs_with_unsaved_changes:
               # Type has unsaved changes, proceed to full check
               has_any_relevant_changes = True
               break

       if not has_any_relevant_changes:
           # No relevant changes, skip expensive field resolution
           return False

**Cache Clearing**

The cache is cleared when a form manager is closed:

.. code-block:: python

   def unregister_from_cross_window_updates(self):
       # Clear this manager's config types from the cache
       type(self)._configs_with_unsaved_changes.clear()

Performance Impact
------------------

- **Before**: O(n_managers) iteration on every change
- **After**: O(1) cache lookup
- **Typical speedup**: 10-100x for fast-path checks with multiple windows open

MRO Inheritance Cache
=====================

Problem
-------

The type-based cache only tracked directly edited config types. When editing a nested field like ``GlobalPipelineConfig.well_filter_config.well_filter``, the cache would mark ``WellFilterConfig`` with field name ``"well_filter"``. However, step configs like ``StepMaterializationConfig`` inherit from ``WellFilterConfig`` via MRO, so they should also be marked as having unsaved changes.

Without MRO awareness, the following scenarios failed:

1. **Editing GlobalPipelineConfig while step editor open**: Step wouldn't flash because ``StepMaterializationConfig`` wasn't in the cache
2. **Editing GlobalPipelineConfig while PipelineConfig editor open**: Plate list items wouldn't flash

Solution
--------

Built an MRO inheritance cache at startup that maps ``(parent_type, field_name) → set of child types that inherit this field``:

.. code-block:: python

   # Class-level cache in ParameterFormManager
   _mro_inheritance_cache: Dict[Tuple[Type, str], Set[Type]] = {}

   # Example entry:
   # (WellFilterConfig, "well_filter") → {StepMaterializationConfig, StepWellFilterConfig, PathPlanningConfig, ...}

When marking a config type with unsaved changes, we also look up all child types in the MRO cache and mark them too.

Implementation Details
----------------------

**Building the Cache**

Located in ``openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py``:

.. code-block:: python

   @classmethod
   def _build_mro_inheritance_cache(cls):
       """Build cache of which config types can inherit from which other types via MRO."""
       from openhcs.config_framework.cache_warming import _extract_all_dataclass_types
       from openhcs.core.config import GlobalPipelineConfig
       import dataclasses

       # Introspect all config types in the hierarchy (generic, no hardcoding)
       all_config_types = _extract_all_dataclass_types(GlobalPipelineConfig)

       # For each config type, build reverse mapping: (parent_type, field_name) → child_types
       for child_type in all_config_types:
           for field in dataclasses.fields(child_type):
               field_name = field.name

               # Check which types in the MRO have this field
               for mro_class in child_type.__mro__:
                   if not dataclasses.is_dataclass(mro_class):
                       continue
                   if mro_class == child_type:
                       continue

                   # Check if this MRO class has the same field
                   mro_fields = dataclasses.fields(mro_class)
                   if any(f.name == field_name for f in mro_fields):
                       cache_key = (mro_class, field_name)
                       if cache_key not in cls._mro_inheritance_cache:
                           cls._mro_inheritance_cache[cache_key] = set()
                       cls._mro_inheritance_cache[cache_key].add(child_type)

The cache is built once at GUI startup via ``prewarm_config_analysis_cache()`` in ``openhcs/config_framework/cache_warming.py``.

**Using the Cache**

When marking config types, we look up affected child types and mark BOTH base types AND lazy types:

.. code-block:: python

   def _mark_config_type_with_unsaved_changes(self, param_name: str, value: Any):
       # ... extract config_type and field_name ...

       # CRITICAL: If value is a nested config, mark ALL fields within it
       # This ensures MRO cache lookups work correctly
       fields_to_mark = []
       if dataclasses.is_dataclass(config):
           for field in dataclasses.fields(config):
               fields_to_mark.append(field.name)
       else:
           fields_to_mark.append(field_name)

       for field_to_mark in fields_to_mark:
           # Mark the directly edited type
           type(self)._configs_with_unsaved_changes[config_type].add(field_to_mark)

           # CRITICAL: MRO cache uses base types, not lazy types - convert if needed
           from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
           cache_lookup_type = get_base_type_for_lazy(config_type)
           cache_key = (cache_lookup_type, field_to_mark)
           affected_types = type(self)._mro_inheritance_cache.get(cache_key, set())

           # CRITICAL: Mark BOTH base types AND lazy types
           # The MRO cache returns base types, but steps use lazy types
           from openhcs.config_framework.lazy_factory import get_lazy_type_for_base
           for affected_type in affected_types:
               # Mark the base type
               type(self)._configs_with_unsaved_changes[affected_type].add(field_to_mark)

               # Also mark the lazy version (O(1) reverse lookup)
               lazy_type = get_lazy_type_for_base(affected_type)
               if lazy_type is not None:
                   type(self)._configs_with_unsaved_changes[lazy_type].add(field_to_mark)

**Lazy Type Registry**

The lazy type registry provides bidirectional mapping between base types and lazy types:

.. code-block:: python

   # In openhcs/config_framework/lazy_factory.py
   _lazy_type_registry: Dict[Type, Type] = {}  # lazy → base
   _base_to_lazy_registry: Dict[Type, Type] = {}  # base → lazy (reverse)

   def register_lazy_type_mapping(lazy_type: Type, base_type: Type):
       _lazy_type_registry[lazy_type] = base_type
       _base_to_lazy_registry[base_type] = lazy_type

   def get_base_type_for_lazy(lazy_type: Type) -> Optional[Type]:
       return _lazy_type_registry.get(lazy_type)

   def get_lazy_type_for_base(base_type: Type) -> Optional[Type]:
       return _base_to_lazy_registry.get(base_type)

This enables O(1) reverse lookup when marking lazy types, avoiding O(n) linear search through the registry.

Performance Impact
------------------

- **Cache building**: O(n_types × n_fields × n_mro_depth) at startup (typically <10ms)
- **Cache lookup**: O(1) dict access
- **Lazy type reverse lookup**: O(1) dict access (was O(n) linear search)
- **Memory overhead**: Minimal (typically <100 cache entries + reverse registry)

Context Manager Fixes
=====================

Problem
-------

The context manager had several critical bugs that broke unsaved changes detection and MRO inheritance:

1. **Lazy type information lost during merging**: When merging ``PipelineConfig`` into ``GlobalPipelineConfig``, lazy types (e.g., ``LazyWellFilterConfig``) were converted to base types (e.g., ``WellFilterConfig``), breaking type-based cache lookups
2. **Outer context configs lost during nesting**: When contexts were nested (``GlobalPipelineConfig`` → ``PipelineConfig``), configs from the outer context were lost, breaking MRO inheritance
3. **Infinite recursion in MRO resolution**: Using ``getattr()`` in MRO resolution triggered lazy resolution, causing infinite recursion

Solution
--------

**Preserve Lazy Types**

Extract configs from the ORIGINAL object BEFORE merging to preserve lazy type information:

.. code-block:: python

   def config_context(obj, mask_with_none: bool = False):
       # CRITICAL: Extract configs from ORIGINAL object FIRST (before merging)
       # Use bypass_lazy_resolution=True to get raw values
       original_extracted = {}
       if obj is not None:
           original_extracted = extract_all_configs(obj, bypass_lazy_resolution=True)

       # ... perform merging ...

       # Extract configs from merged config
       extracted = extract_all_configs(merged_config)

       # CRITICAL: Original configs ALWAYS override merged configs to preserve lazy types
       for config_name, config_instance in original_extracted.items():
           extracted[config_name] = config_instance

**Merge with Parent Context**

Preserve configs from outer contexts while allowing inner contexts to override:

.. code-block:: python

   # CRITICAL: Merge with parent context's extracted configs instead of replacing
   parent_extracted = current_extracted_configs.get()
   if parent_extracted:
       # Start with parent's configs
       merged_extracted = dict(parent_extracted)
       # Override with current context's configs (inner context takes precedence)
       merged_extracted.update(extracted)
       extracted = merged_extracted

**Avoid Infinite Recursion**

Always use ``object.__getattribute__()`` in MRO resolution to bypass lazy resolution:

.. code-block:: python

   def resolve_field_inheritance(obj, field_name, available_configs):
       # ... MRO traversal ...
       for mro_class in obj_type.__mro__:
           for config_name, config_instance in available_configs.items():
               if type(config_instance) == mro_class:
                   # CRITICAL: Use object.__getattribute__() to avoid infinite recursion
                   field_value = object.__getattribute__(config_instance, field_name)
                   if field_value is not None:
                       return field_value

**Prioritize Lazy Types in MRO Resolution**

When both lazy and base types are available, prioritize lazy types:

.. code-block:: python

   # First pass: Look for exact type match OR lazy type match (prioritize lazy)
   lazy_match = None
   base_match = None

   for config_name, config_instance in available_configs.items():
       instance_type = type(config_instance)
       if instance_type == mro_class:
           if instance_type.__name__.startswith('Lazy'):
               lazy_match = config_instance
           else:
               base_match = config_instance

   # Prioritize lazy match over base match
   matched_instance = lazy_match if lazy_match is not None else base_match

Performance Impact
------------------

- **Lazy type preservation**: Ensures type-based cache lookups work correctly
- **Context merging**: O(n_configs) merge operation per context nesting level
- **MRO resolution**: No performance impact (same O(n_mro) traversal, just using ``object.__getattribute__()``)

Recent Incremental Optimizations (2025-11)
------------------------------------------

- **LiveContextResolver caching**: Merged-context cache keys now use context ids + token (no live_context hashing), reducing overhead on every resolve.
- **Per-token preview caches**: PipelineEditor and PlateManager cache attribute resolutions per token during a refresh to avoid repeated resolver calls for the same object.
- **Scoped batch resolution**: CrossWindowPreviewMixin batches only preview-enabled fields, prefers scoped live values when available, and reuses batched results across comparisons.
- **Unsaved markers guarded**: Fast-path skips now require both an empty unsaved cache and no active editors with emitted values, preserving accuracy while keeping the fast path.

Signal Architecture Fix
=======================

Problem
-------

The initial implementation connected ``context_value_changed`` to the marking function and disconnected ``parameter_changed`` from ``_emit_cross_window_change()``. This broke the signal chain because:

1. ``parameter_changed`` is emitted when a parameter changes
2. ``_emit_cross_window_change()`` is connected to ``parameter_changed``
3. ``_emit_cross_window_change()`` emits ``context_value_changed``

By disconnecting step 2, ``context_value_changed`` was never emitted, so no cross-window updates occurred.

Additionally, ``parameter_changed`` only emits the parent config name for nested changes (e.g., ``"well_filter_config"``), losing information about which specific field changed (e.g., ``"well_filter"``). This caused MRO cache lookups to fail because the cache has entries like ``(WellFilterConfig, "well_filter")``, not ``(WellFilterConfig, "well_filter_config")``.

Solution
--------

Connect **both** signals:

.. code-block:: python

   # Connect parameter_changed to emit cross-window context changes
   # This triggers _emit_cross_window_change which emits context_value_changed
   self.parameter_changed.connect(self._emit_cross_window_change)

   # ALSO connect context_value_changed to mark config types (uses full field paths)
   # context_value_changed has the full field path (e.g., "PipelineConfig.well_filter_config.well_filter")
   # instead of just the parent config name (e.g., "well_filter_config")
   self.context_value_changed.connect(
       lambda field_path, value, obj, ctx: self._mark_config_type_with_unsaved_changes(
           '.'.join(field_path.split('.')[1:]), value  # Remove type name from path
       )
   )

This ensures:

1. ``parameter_changed`` → ``_emit_cross_window_change()`` → ``context_value_changed`` (signal chain intact)
2. ``context_value_changed`` → marking function with full field path (accurate MRO cache lookups)

Files Modified
--------------

- ``openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py``: Signal connections (lines 824-837)
- ``openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py``: ``_mark_config_type_with_unsaved_changes()`` (lines 3753-3820)
- ``openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py``: ``_build_mro_inheritance_cache()`` (lines 299-365)
- ``openhcs/config_framework/cache_warming.py``: MRO cache building call (lines 154-162)
- ``openhcs/core/config_cache.py``: Cache warming at startup (lines 98-107, 239-248)
- ``openhcs/pyqt_gui/widgets/config_preview_formatters.py``: Fast-path type-based cache check (lines 407-450)

Results
=======

The optimizations achieve the target performance:

- **Incremental updates**: <16ms (60 FPS) with multiple windows open
- **Cache building**: <10ms at startup
- **Memory overhead**: Minimal (<100 cache entries)
- **Correctness**: All cross-window reactivity scenarios work correctly

Scoped Override Fix
===================

Problem
-------

The scoped override logic in ``check_config_has_unsaved_changes()`` was incorrectly returning ``False`` when it detected a scoped manager with changes. This prevented unsaved changes detection from working when editing ``PipelineConfig`` or step configs.

The original logic was:

.. code-block:: python

   # WRONG: Returns False when scoped override detected
   if has_scoped_override:
       return False  # This breaks unsaved changes detection!

   if not has_form_manager_with_changes:
       return False

This was designed to prevent global changes from triggering flash when a scoped override exists, but it also prevented scoped changes from being detected.

Solution
--------

The fix is to proceed to full field resolution when EITHER scoped override OR global changes are detected:

.. code-block:: python

   # CORRECT: Only skip if there are NO changes at all
   if not has_form_manager_with_changes and not has_scoped_override:
       return False  # No changes at all - skip

   # Proceed to full check for either scoped or global changes

This ensures that:

1. **Scoped changes are detected**: When editing ``PipelineConfig.well_filter_config``, the scoped manager is detected and we proceed to full check
2. **Global changes are detected**: When editing ``GlobalPipelineConfig.well_filter_config`` with no scoped override, we proceed to full check
3. **No false positives**: When there are no changes at all, we skip the expensive field resolution

Performance Impact
------------------

- **Correctness**: Fixes regression where scoped changes weren't detected
- **Performance**: No impact (same full check is performed, just with correct logic)

Bugs Fixed
----------

1. **Editing GlobalPipelineConfig.well_filter_config.well_filter while step editor open**: Step now flashes correctly
2. **Editing GlobalPipelineConfig while PipelineConfig editor open**: Plate list items now flash correctly
3. **Early return bug**: Removed early return when ``live_context_snapshot=None`` that was breaking flash detection
4. **Scoped override regression**: Fixed scoped override logic to detect scoped changes correctly
5. **Lazy type cache misses**: Fixed MRO cache lookups to convert lazy types to base types before lookup
6. **Missing lazy type marking**: Fixed to mark both base types AND lazy types when marking unsaved changes
7. **Context merging losing outer configs**: Fixed to merge with parent context instead of replacing
8. **Infinite recursion in MRO resolution**: Fixed to use ``object.__getattribute__()`` instead of ``getattr()``

File Locations
==============

Key implementation files:

**Type-Based Caching and MRO Inheritance**

- ``openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py``:

  - Signal connections (lines 824-837)
  - ``_mark_config_type_with_unsaved_changes()`` (lines 3800-3860)
  - ``_build_mro_inheritance_cache()`` (lines 299-365)
  - ``collect_live_context()`` scoped manager filtering (lines 415-450)

- ``openhcs/pyqt_gui/widgets/config_preview_formatters.py``:

  - ``check_config_has_unsaved_changes()`` type-based cache check (lines 183-198)
  - ``check_config_has_unsaved_changes()`` scoped override fix (lines 294-310)
  - ``check_step_has_unsaved_changes()`` fast-path type-based cache check (lines 450-520)

**Lazy Type Registry**

- ``openhcs/config_framework/lazy_factory.py``:

  - Lazy type registries (lines 18-46)
  - ``register_lazy_type_mapping()`` (lines 33-35)
  - ``get_base_type_for_lazy()`` (lines 38-40)
  - ``get_lazy_type_for_base()`` (lines 43-45)

**Context Manager Fixes**

- ``openhcs/config_framework/context_manager.py``:

  - Context stack tracking (lines 38-40)
  - ``config_context()`` lazy type preservation (lines 123-132)
  - ``config_context()`` parent context merging (lines 201-219)
  - ``extract_all_configs()`` bypass lazy resolution (lines 506-570)

- ``openhcs/config_framework/dual_axis_resolver.py``:

  - ``resolve_field_inheritance()`` infinite recursion fix (lines 268-273)
  - ``resolve_field_inheritance()`` lazy type prioritization (lines 278-318)

**Cache Warming**

- ``openhcs/config_framework/cache_warming.py``: MRO cache building call (lines 154-162)
- ``openhcs/core/config_cache.py``: Cache warming at startup (lines 98-107, 239-248)

Batch Context Snapshot Optimization (2025-11)
==============================================

Problem
-------

When a user edits a configuration field, multiple UI components (PlateManager, PipelineEditor) need to:

1. Compute a **live context snapshot** (current form values across all windows)
2. Compute a **saved context snapshot** (what would the values be without active form managers)
3. Compare live vs saved to detect unsaved changes

Previously, each listener independently computed both snapshots, resulting in:

- **Duplicate work**: Same expensive snapshot computation done 2× per batch
- **800ms gap**: PlateManager and PipelineEditor flash animations were desynchronized
- **Cache thrashing**: Token increments on every keystroke invalidated per-token caches

Solution
--------

Pre-compute both snapshots ONCE in the coordinator, share with all listeners:

.. code-block:: python

   # In _execute_coordinated_updates (parameter_form_manager.py)
   ParameterFormManager._batch_live_context_snapshot = (
       ParameterFormManager._collect_live_context_from_other_windows()
   )
   ParameterFormManager._batch_saved_context_snapshot = (
       ParameterFormManager._collect_live_context_without_forms()
   )

   # Listeners access via class method
   live_snapshot, saved_snapshot = ParameterFormManager.get_batch_snapshots()

**Fast-Path Bypass**: When ``saved_context_snapshot`` is provided (batch operation), both fast-paths in ``check_step_has_unsaved_changes`` are bypassed:

1. **Global fast-path**: Skipped when ``saved_context_snapshot is not None``
2. **Relevant changes fast-path**: Skipped when ``saved_context_snapshot is not None``

This ensures the actual live vs saved comparison occurs during batch operations.

Implementation Details
----------------------

**Class-Level Batch Snapshots** (``parameter_form_manager.py``):

.. code-block:: python

   class ParameterFormManager:
       _batch_live_context_snapshot: Optional[LiveContextSnapshot] = None
       _batch_saved_context_snapshot: Optional[LiveContextSnapshot] = None

       @classmethod
       def get_batch_snapshots(cls):
           return cls._batch_live_context_snapshot, cls._batch_saved_context_snapshot

**Listener Usage** (``pipeline_editor.py``, ``plate_manager.py``):

.. code-block:: python

   def _process_pending_preview_updates(self):
       live_snapshot, saved_snapshot = ParameterFormManager.get_batch_snapshots()
       # Use batch snapshots if available, otherwise compute fresh
       if live_snapshot is None:
           live_snapshot = ParameterFormManager._collect_live_context_from_other_windows()

**Fast-Path Bypass** (``config_preview_formatters.py``):

.. code-block:: python

   # Skip type-based cache fast-path when batch snapshot provided
   if cache_disabled or saved_context_snapshot is not None:
       has_any_relevant_changes = True  # Force full resolution

Performance Impact
------------------

- **Before**: ~800ms gap between PlateManager and PipelineEditor updates
- **After**: Both components flash simultaneously (same batch execution)
- **Snapshot computation**: Done 1× instead of 2× per batch

Future Optimizations
====================

Potential future optimizations (not yet implemented):

1. **Incremental context updates**: Only update changed fields instead of rebuilding entire context
2. **Block immediate emission during typing**: Similar to Reset button behavior
3. **Batch-level unsaved status cache**: Cache unsaved status per batch instead of per-keystroke token

See Also
========

- :doc:`cross_window_update_optimization` - Original cross-window update system
- :doc:`parameter_form_lifecycle` - Parameter form manager lifecycle
- :doc:`configuration_framework` - Lazy configuration framework
- :doc:`scope_visual_feedback_system` - Visual feedback system

