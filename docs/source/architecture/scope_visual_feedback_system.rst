====================================
Scope-Based Visual Feedback System
====================================

*Module: openhcs.pyqt_gui.widgets.shared.scope_visual_config, scope_color_utils, list_item_flash_animation, widget_flash_animation*  
*Status: STABLE*

---

Overview
========

The scope-based visual feedback system provides immediate visual indication of configuration changes and hierarchical relationships across the GUI. The system uses perceptually distinct colors to differentiate orchestrators (plates) and applies layered borders with tints and patterns to distinguish steps within each orchestrator's pipeline.

**Key Features**:

- **Flash animations** trigger when resolved configuration values change (not just raw values)
- **Scope-based coloring** using perceptually distinct palettes for orchestrators
- **Layered borders** with tints and patterns for visual step differentiation
- **WCAG AA compliance** for accessibility (4.5:1 contrast ratio)
- **Dual tracking system** separates flash detection from label updates

Problem Context
===============

Traditional GUI systems flash on every field change, creating false positives when overridden step configs change but their resolved values don't. For example, if ``step.well_filter=3`` stays 3 even when ``pipeline.well_filter`` changes from 4 to 5, the step shouldn't flash because its effective value didn't change.

The scope-based visual feedback system solves this by comparing resolved values (after inheritance resolution) rather than raw field values.

Flash Detection Internals
==========================

This section documents the internal mechanisms of flash detection to aid maintenance and future refactoring.

LiveContextSnapshot Structure
------------------------------

The ``LiveContextSnapshot`` is the core data structure for flash detection. It captures the state of all active form managers at a point in time:

.. code-block:: python

   @dataclass
   class LiveContextSnapshot:
       """Snapshot of live context values from all active form managers.

       Structure:
       - values: Dict[Type, Dict[str, Any]]
           Global context values keyed by type (e.g., PipelineConfig, GlobalPipelineConfig)
           Example: {PipelineConfig: {'well_filter_config': LazyWellFilterConfig(...)}}

       - scoped_values: Dict[str, Dict[Type, Dict[str, Any]]]
           Scoped context values keyed by scope_id (e.g., plate_path)
           Example: {'/home/user/plate': {PipelineConfig: {'well_filter_config': ...}}}

       - token: int
           Monotonically increasing counter for cache invalidation
       """
       values: Dict[Type, Dict[str, Any]]
       scoped_values: Dict[str, Dict[Type, Dict[str, Any]]]
       token: int

**When to use which context:**

- **Global context** (``values``): Used for GlobalPipelineConfig and other global state
- **Scoped context** (``scoped_values``): Used for plate-specific PipelineConfig and step-specific values
- **Scope ID format**: Plate scope = ``"/path/to/plate"``, Step scope = ``"/path/to/plate::step_0"``

**Critical insight**: When resolving values for flash detection, you must extract the correct scope from ``scoped_values`` based on the object being checked. For steps, use the step's scope_id; for plates, use the plate's scope_id.

.. code-block:: python

   # Extract scoped context for a specific plate
   scope_id = "/home/user/plate"
   if scope_id and live_context_snapshot:
       scoped_values = live_context_snapshot.scoped_values.get(scope_id, {})
       pipeline_config_values = scoped_values.get(PipelineConfig, {})
       well_filter_config = pipeline_config_values.get('well_filter_config')

Canonical Root Aliasing System
-------------------------------

The mixin maintains a ``_preview_scope_aliases`` dict that maps lowercase canonical root names to their original type names. This is necessary because:

1. **Form managers send uppercase type names**: ``"PipelineConfig.well_filter_config"``
2. **Mixin canonicalizes to lowercase**: ``"pipeline_config.well_filter_config"``
3. **Both formats must be handled**: Expansion logic checks ``first_part[0].isupper() or first_part in self._preview_scope_aliases.values()``

.. code-block:: python

   # In _canonicalize_root()
   self._preview_scope_aliases[root_name.lower()] = root_name
   # Maps: "pipelineconfig" -> "PipelineConfig"
   #       "pipeline_config" -> "PipelineConfig" (if explicitly set)

**Why this exists**: The form manager uses type names as field_id (e.g., ``type(config).__name__``), but the mixin needs to normalize these for consistent lookup. The aliasing system allows both ``"PipelineConfig"`` and ``"pipeline_config"`` to refer to the same root.

**Maintenance note**: This dual-format system is a source of complexity. Future refactoring should establish a single canonical format (preferably lowercase) used throughout the system.

Batch Resolution Performance
-----------------------------

Batch resolution is critical for performance when checking multiple fields. The problem:

**Naive approach (O(N) context setups)**:

.. code-block:: python

   for field in fields:
       # Each call builds context stack: GlobalPipelineConfig → PipelineConfig → Step
       before_value = resolver.resolve_config_attr(obj_before, field, ...)
       after_value = resolver.resolve_config_attr(obj_after, field, ...)
       if before_value != after_value:
           return True

**Batch approach (O(1) context setup)**:

.. code-block:: python

   # Build context stack ONCE
   before_attrs = resolver.resolve_all_config_attrs(obj_before, fields, ...)
   after_attrs = resolver.resolve_all_config_attrs(obj_after, fields, ...)

   # Compare all fields
   for field in fields:
       if before_attrs[field] != after_attrs[field]:
           return True

**Why context setup is expensive**:

1. Walk through inheritance hierarchy (GlobalPipelineConfig → PipelineConfig → Step)
2. For each level, extract all dataclass fields
3. Build merged context dict with proper override semantics
4. Cache the result keyed by (obj_id, token)

For 7 steps × 10 fields = 70 comparisons, batch resolution is ~50x faster.

**Methods**:

- ``resolve_all_lazy_attrs(obj, context_stack, live_ctx, token)``: Resolves ALL fields on a dataclass
- ``resolve_all_config_attrs(obj, field_names, context_stack, live_ctx, token)``: Resolves SPECIFIC fields (can be on non-dataclass objects like FunctionStep)

The Three Identifier Formats
-----------------------------

Flash detection handles three distinct identifier formats, each requiring different expansion logic:

**Format 1: Simple field name**

Example: ``"well_filter"``

Expansion: Find all dataclass attributes on the object that have this field.

.. code-block:: python

   # "well_filter" expands to:
   # - "well_filter_config.well_filter"
   # - "step_well_filter_config.well_filter"
   # - "fiji_streaming_config.well_filter"
   # - "napari_streaming_config.well_filter"
   # etc.

**Format 2: Nested field path**

Example: ``"well_filter_config.well_filter"``

Expansion: Find all dataclass attributes that have the nested field AND whose type inherits from the config's type.

.. code-block:: python

   # "well_filter_config.well_filter" expands to:
   # - "well_filter_config.well_filter" (original)
   # - "step_well_filter_config.well_filter" (StepWellFilterConfig inherits from WellFilterConfig)
   # - "fiji_streaming_config.well_filter" (FijiStreamingConfig inherits from WellFilterConfig)
   # etc.

**Format 3: Parent type path**

Example: ``"PipelineConfig.well_filter_config"`` or ``"pipeline_config.well_filter_config"``

Expansion: Find the field's type from live context, then find all dataclass attributes whose type inherits from that type, and expand to ALL nested fields.

.. code-block:: python

   # "PipelineConfig.well_filter_config" expands to:
   # 1. Look up well_filter_config in live context -> LazyWellFilterConfig
   # 2. Get all fields from LazyWellFilterConfig -> ['well_filter', 'well_filter_mode']
   # 3. Find all dataclass attrs that inherit from LazyWellFilterConfig:
   #    - step_well_filter_config (StepWellFilterConfig inherits from WellFilterConfig)
   #    - fiji_streaming_config (FijiStreamingConfig inherits from WellFilterConfig)
   # 4. Expand to all nested fields:
   #    - "step_well_filter_config.well_filter"
   #    - "step_well_filter_config.well_filter_mode"
   #    - "fiji_streaming_config.well_filter"
   #    - "fiji_streaming_config.well_filter_mode"
   # etc.

**Why Format 3 exists**: Window close events send ALL fields from the form manager, using the form's field_id as prefix. For PipelineConfig editor, field_id = ``"PipelineConfig"``, so fields are sent as ``"PipelineConfig.well_filter_config"``, ``"PipelineConfig.num_workers"``, etc.

**Detection logic**:

.. code-block:: python

   parts = identifier.split(".")
   if len(parts) == 2:
       first_part, second_part = parts
       # Check if first_part is a type name (uppercase) or canonical root (lowercase)
       is_type_or_root = first_part[0].isupper() or first_part in self._preview_scope_aliases.values()

       if is_type_or_root:
           # Format 3: Parent type path
           # Use live context to find field type and expand
       else:
           # Format 2: Nested field path
           # Use object introspection to expand

Architecture
============

Scope ID Format
---------------

Hierarchical scope identifiers enable targeted updates and visual styling:

.. code-block:: python

   # Orchestrator scope: plate path only
   orchestrator_scope = "/path/to/plate"
   
   # Step scope (cross-window updates): plate path + step token
   step_scope_update = "/path/to/plate::step_0"
   
   # Step scope (visual styling): plate path + step token + position
   step_scope_visual = "/path/to/plate::step_0@5"

**The @position suffix** enables independent step numbering per orchestrator, ensuring step 0 in orchestrator A gets different styling than step 0 in orchestrator B.

Dual Tracking System
--------------------

The CrossWindowPreviewMixin maintains two independent tracking mechanisms:

**1. _pending_changed_fields** - Tracks ALL field changes for flash detection

.. code-block:: python

   # Track which field changed (for flash logic - ALWAYS track, don't filter)
   for identifier in identifiers:
       self._pending_changed_fields.add(identifier)

**2. _pending_label_keys** - Tracks only registered preview fields for label updates

.. code-block:: python

   # Check if this change affects displayed text (for label updates)
   should_update_labels = self._should_process_preview_field(...)
   
   if should_update_labels:
       self._pending_label_keys.update(target_keys)

This decoupling ensures:

- Flash triggers on any resolved value change
- Labels update only for registered preview fields
- No false positives when non-preview fields change

Flash Detection Logic
---------------------

Flash detection compares resolved values (not raw values) using live context snapshots:

.. code-block:: python

   # 1. Capture live context snapshot BEFORE changes
   live_context_before = self._last_live_context_snapshot

   # 2. Capture live context snapshot AFTER changes
   live_context_after = self._collect_live_context()

   # 3. Get preview instances with merged live values
   step_before = self._get_step_preview_instance(step, live_context_before)
   step_after = self._get_step_preview_instance(step, live_context_after)

   # 4. Compare resolved values (not raw values)
   for field_path in changed_fields:
       before_value = getattr(step_before, field_path)
       after_value = getattr(step_after, field_path)

       if before_value != after_value:
           # Flash! Resolved value actually changed
           self._flash_step_item(step_index)

**Key insight**: Preview instances are fully resolved via ``dataclasses.replace()`` and lazy resolution, so comparing them compares actual effective values after inheritance.

**Identifier Expansion for Inheritance**

When checking if resolved values changed, the system expands field identifiers to include fields that inherit from the changed type. The expansion handles three formats:

1. **Simple field names** (e.g., ``"well_filter"``): Expands to all dataclass attributes that have this field
2. **Nested field paths** (e.g., ``"well_filter_config.well_filter"``): Expands to inherited dataclass attributes with the same nested field
3. **Parent type paths** (e.g., ``"PipelineConfig.well_filter_config"`` or ``"pipeline_config.well_filter_config"``): Expands to all dataclass attributes whose TYPE inherits from the field's type

.. code-block:: python

   def _expand_identifiers_for_inheritance(
       self, obj, changed_fields, live_context_snapshot
   ) -> Set[str]:
       """Expand field identifiers to include fields that inherit from changed types.

       Example 1: "well_filter" expands to:
       - "well_filter_config.well_filter"
       - "step_well_filter_config.well_filter"
       - "fiji_streaming_config.well_filter"
       - etc.

       Example 2: "PipelineConfig.well_filter_config" expands to:
       - "step_well_filter_config.well_filter"
       - "step_well_filter_config.well_filter_mode"
       - "fiji_streaming_config.well_filter"
       - "fiji_streaming_config.well_filter_mode"
       - etc. (all nested fields in all dataclasses that inherit from WellFilterConfig)
       """
       expanded = set()

       for identifier in changed_fields:
           parts = identifier.split(".")

           if len(parts) == 1:
               # Simple field - expand to all dataclass attributes that have this field
               for attr_name in dir(obj):
                   attr_value = getattr(obj, attr_name, None)
                   if is_dataclass(attr_value) and hasattr(attr_value, identifier):
                       expanded.add(f"{attr_name}.{identifier}")

           elif len(parts) == 2:
               first_part, second_part = parts

               # Check if first_part is a type name (uppercase) or canonical root (lowercase)
               is_type_or_root = first_part[0].isupper() or first_part in self._preview_scope_aliases.values()

               if is_type_or_root:
                   # Parent type format: "PipelineConfig.well_filter_config"
                   # Find the field's type from live context
                   field_type = None
                   field_value = None
                   if live_context_snapshot:
                       # Check both global and scoped values
                       all_values = dict(live_context_snapshot.values)
                       for scope_dict in live_context_snapshot.scoped_values.values():
                           all_values.update(scope_dict)

                       for type_key, values_dict in all_values.items():
                           if second_part in values_dict:
                               field_value = values_dict[second_part]
                               if is_dataclass(field_value):
                                   field_type = type(field_value)
                                   break

                   # Expand to ALL nested fields in ALL dataclasses that inherit from field_type
                   if field_type:
                       nested_field_names = [f.name for f in dataclass_fields(field_value)]
                       for attr_name in dir(obj):
                           attr_value = getattr(obj, attr_name, None)
                           if is_dataclass(attr_value):
                               attr_type = type(attr_value)
                               if issubclass(attr_type, field_type) or issubclass(field_type, attr_type):
                                   for nested_field in nested_field_names:
                                       expanded.add(f"{attr_name}.{nested_field}")
               else:
                   # Nested field format: "well_filter_config.well_filter"
                   # Expand to all dataclass attributes with the same nested field
                   config_field, nested_attr = parts
                   for attr_name in dir(obj):
                       attr_value = getattr(obj, attr_name, None)
                       if is_dataclass(attr_value) and hasattr(attr_value, nested_attr):
                           expanded.add(f"{attr_name}.{nested_attr}")

       return expanded

This ensures flash detection works correctly when inherited values change, even if the changed field identifier doesn't exactly match the inheriting field's path. The type-based expansion is critical for window close events where the form manager sends parent type paths like ``"PipelineConfig.well_filter_config"``.

**Window Close Snapshot Timing**

Window close events are special because they represent a REVERSION: the user edited values but didn't save, so the system reverts to the saved state. Flash detection must compare the edited values (what the user saw) against the reverted values (what the system now has).

**Why timing is critical**:

1. **Form manager adds live values to context**: When a config editor is open, its form manager registers with ``ParameterFormManager._active_form_managers`` and contributes its edited values to ``LiveContextSnapshot.values`` or ``LiveContextSnapshot.scoped_values``
2. **Unregistering removes those values**: When the form manager is removed from the registry, subsequent snapshots no longer include the edited values
3. **Before snapshot = with edited values**: This is what the user saw in the UI before closing
4. **After snapshot = without edited values**: This is the reverted state after closing without saving
5. **Comparing these detects the reversion**: Any field that differs between before/after snapshots had its value reverted

**The critical sequence**:

1. Window close signal received
2. **Before snapshot collected** (with form manager's edited values)
3. Form manager removed from registry
4. Token counter incremented (invalidates all caches)
5. **After snapshot collected** (without form manager, reverted to saved values)
6. External listeners notified with both snapshots via ``handle_window_close()``
7. Remaining windows refreshed

**Why deferred notification is necessary**:

The form manager uses ``QTimer.singleShot(0)`` to defer listener notification until after the current call stack completes. This ensures:

1. The form manager is fully unregistered before collecting the "after" snapshot
2. The token counter has been incremented, invalidating all caches
3. The "after" snapshot truly reflects the reverted state without any lingering form manager values

.. code-block:: python

   def unregister_from_cross_window_updates(self):
       """Unregister form manager when window closes."""
       # CRITICAL: Capture "before" snapshot BEFORE unregistering
       # This snapshot has the form manager's live values
       before_snapshot = type(self).collect_live_context()

       # Remove from registry
       self._active_form_managers.remove(self)
       type(self)._live_context_token_counter += 1

       # Defer notification until after current call stack completes
       # This ensures the form manager is fully unregistered
       def notify_listeners():
           # Collect "after" snapshot (without form manager)
           after_snapshot = type(self).collect_live_context()

           # Build set of changed field identifiers
           changed_fields = {f"{self.field_id}.{param}" for param in self.parameters}

           # Call dedicated handle_window_close() method if available
           for listener, _, _ in self._external_listeners:
               if hasattr(listener, 'handle_window_close'):
                   listener.handle_window_close(
                       self.object_instance,
                       self.context_obj,
                       before_snapshot,  # With edited values
                       after_snapshot,   # Without edited values
                       changed_fields
                   )

       QTimer.singleShot(0, notify_listeners)

**Dedicated Window Close Handler**

The ``handle_window_close()`` method receives snapshots as parameters instead of storing them as listener state. This is architecturally cleaner than setting attributes on listeners:

.. code-block:: python

   def handle_window_close(
       self,
       editing_object: Any,
       context_object: Any,
       before_snapshot: Any,  # LiveContextSnapshot with form manager
       after_snapshot: Any,   # LiveContextSnapshot without form manager
       changed_fields: Set[str],
   ) -> None:
       """Handle window close events with dedicated snapshot parameters.

       This is called when a config editor window is closed without saving.
       Unlike incremental updates, this receives explicit before/after snapshots
       to compare the unsaved edits against the reverted state.
       """
       scope_id = self._extract_scope_id_for_preview(editing_object, context_object)
       target_keys, _ = self._resolve_scope_targets(scope_id)

       # Add target keys to pending sets
       self._pending_preview_keys.update(target_keys)
       self._pending_label_keys.update(target_keys)

       # Window close always triggers full refresh with explicit snapshots
       self._schedule_preview_update(
           full_refresh=True,
           before_snapshot=before_snapshot,
           after_snapshot=after_snapshot,
           changed_fields=changed_fields,
       )

The snapshots are stored temporarily in ``_pending_window_close_*`` attributes for the timer callback to access, then cleared after use. This avoids polluting listener state with event-specific data.

Scope ID Extraction Logic
--------------------------

The ``_extract_scope_id_for_preview()`` method determines which scope to use when resolving values from ``LiveContextSnapshot.scoped_values``. Different object types have different scope extraction logic:

**For PipelineConfig objects**:

.. code-block:: python

   def _extract_scope_id_for_preview(self, editing_object, context_object):
       """Extract scope_id for preview resolution.

       For PipelineConfig: Use the plate_path from context_object (Orchestrator)
       For FunctionStep: Use step scope (plate_path::step_index)
       """
       if isinstance(editing_object, PipelineConfig):
           # Plate scope: "/path/to/plate"
           if hasattr(context_object, 'plate_path'):
               return context_object.plate_path
           return None

       elif isinstance(editing_object, FunctionStep):
           # Step scope: "/path/to/plate::step_0"
           if hasattr(context_object, 'plate_path'):
               step_index = self._get_step_index(editing_object)
               return f"{context_object.plate_path}::step_{step_index}"
           return None

**Why this matters**:

1. **PipelineConfig editors** use plate scope because PipelineConfig is plate-specific
2. **Step editors** use step scope because steps can have step-specific overrides
3. **Scope determines which values to use**: When resolving ``well_filter_config.well_filter`` for a step, the system looks in ``scoped_values["/path/to/plate::step_0"][PipelineConfig]['well_filter_config']``

**Critical for window close events**:

When a PipelineConfig editor closes, the form manager's scoped values are keyed by plate_path. The listener must extract the same plate_path to find the correct scoped values in the before/after snapshots.

.. code-block:: python

   # In handle_window_close()
   scope_id = self._extract_scope_id_for_preview(editing_object, context_object)
   # For PipelineConfig: scope_id = "/home/user/plate"
   # For FunctionStep: scope_id = "/home/user/plate::step_0"

   # Use scope_id to extract scoped values
   if scope_id and live_context_snapshot:
       scoped_values = live_context_snapshot.scoped_values.get(scope_id, {})

**Context-Aware Resolution**

Flash detection uses ``LiveContextResolver`` to resolve field values through the context hierarchy (GlobalPipelineConfig → PipelineConfig → Step). This ensures flash detection sees the same resolved values that the UI displays.

**Batch Resolution for Performance**

Flash detection uses batch resolution to check multiple objects efficiently:

.. code-block:: python

   # Instead of resolving each field individually (O(N) context setups)
   for field in fields:
       before_value = resolver.resolve_config_attr(obj_before, field, ...)
       after_value = resolver.resolve_config_attr(obj_after, field, ...)

   # Batch resolve ALL fields at once (O(1) context setup)
   before_values = resolver.resolve_all_lazy_attrs(obj_before, ...)
   after_values = resolver.resolve_all_lazy_attrs(obj_after, ...)

The ``resolve_all_lazy_attrs()`` method works for both dataclass and non-dataclass objects:

- **Dataclass objects** (e.g., PipelineConfig): Uses ``fields()`` to get all field names
- **Non-dataclass objects** (e.g., FunctionStep): Introspects to find dataclass attributes (e.g., ``fiji_streaming_config``, ``step_well_filter_config``)

This unified approach ensures flash detection works correctly for window close events on both PipelineConfig editors and step editors.

.. code-block:: python

   def _build_flash_context_stack(self, obj, live_context_snapshot) -> list:
       """Build context stack for flash resolution.

       For PipelineEditor: GlobalPipelineConfig → PipelineConfig → Step
       For PlateManager: GlobalPipelineConfig → PipelineConfig
       """
       return [
           get_current_global_config(GlobalPipelineConfig),
           self._get_pipeline_config_preview_instance(live_context_snapshot),
           obj  # The step or pipeline config (preview instance)
       ]

   def _resolve_flash_field_value(self, obj, identifier, live_context_snapshot):
       """Resolve field value through context stack for flash detection."""
       context_stack = self._build_flash_context_stack(obj, live_context_snapshot)

       if context_stack:
           # Use LiveContextResolver for context-aware resolution
           return self._resolve_through_context_stack(
               obj, identifier, context_stack, live_context_snapshot
           )
       else:
           # Fallback to simple object graph walk
           return self._walk_object_path(obj, identifier)

This ensures that flash detection compares the same resolved values that the user sees in the UI, preventing false positives and false negatives.

Color Generation
================

Perceptually Distinct Colors
----------------------------

The system uses the ``distinctipy`` library to generate 50 perceptually distinct colors for orchestrators:

.. code-block:: python

   from distinctipy import distinctipy
   
   # Generate perceptually distinct colors
   colors = distinctipy.get_colors(
       n_colors=50,
       exclude_colors=[(0, 0, 0), (1, 1, 1)],  # Exclude black and white
       pastel_factor=0.5  # Pastel for softer backgrounds
   )

**Deterministic color assignment** uses MD5 hashing of scope_id:

.. code-block:: python

   import hashlib
   
   def hash_scope_to_color_index(scope_id: str, palette_size: int) -> int:
       """Hash scope_id to deterministic color index."""
       hash_bytes = hashlib.md5(scope_id.encode()).digest()
       hash_int = int.from_bytes(hash_bytes[:4], 'big')
       return hash_int % palette_size

WCAG Compliance
---------------

All generated colors are adjusted to meet WCAG AA contrast requirements (4.5:1 ratio):

.. code-block:: python

   from wcag_contrast_ratio import rgb as contrast_rgb
   
   def _ensure_wcag_compliant(color_rgb: tuple, background_rgb: tuple = (30, 30, 30)) -> tuple:
       """Adjust color to meet WCAG AA contrast (4.5:1 ratio)."""
       ratio = contrast_rgb(color_rgb, background_rgb)
       
       if ratio < 4.5:
           # Lighten color until compliant
           # ... adjustment logic ...
       
       return adjusted_color

Layered Border System
=====================

Border Layering Pattern
-----------------------

Steps use layered borders with cycling tint factors and patterns to provide visual differentiation:

**Tint Factors**: ``[0.7, 1.0, 1.4]`` (darker, neutral, brighter)

**Patterns**: ``['solid', 'dashed', 'dotted']``

**Cycling Logic**: Cycle through all 9 tint+pattern combinations before adding layers:

.. code-block:: python

   # Step 0-2:   1 border with solid pattern, tints [dark, neutral, bright]
   # Step 3-5:   1 border with dashed pattern, tints [dark, neutral, bright]
   # Step 6-8:   1 border with dotted pattern, tints [dark, neutral, bright]
   # Step 9-17:  2 borders (all combinations)
   # Step 18-26: 3 borders (all combinations)

   num_border_layers = (step_index // 9) + 1
   combo_index = step_index % 9
   step_pattern_index = combo_index // 3  # 0, 1, or 2
   step_tint = combo_index % 3

Border Rendering
----------------

Borders are rendered by the ``MultilinePreviewItemDelegate`` using custom painting:

.. code-block:: python

   # Border layers stored as list of (width, tint_index, pattern) tuples
   border_layers = index.data(Qt.ItemDataRole.UserRole + 3)
   base_color_rgb = index.data(Qt.ItemDataRole.UserRole + 4)

   # Draw each border layer from outside to inside
   inset = 0
   for layer_data in border_layers:
       width, tint_index, pattern = layer_data

       # Calculate tinted color
       tint_factor = tint_factors[tint_index]
       border_color = QColor(base_color_rgb).darker(120)

       # Set pen style based on pattern
       if pattern == 'dashed':
           pen.setDashPattern([8, 6])
       elif pattern == 'dotted':
           pen.setDashPattern([2, 6])

       # Draw border with proper inset
       border_offset = int(inset + (width / 2.0))
       painter.drawRect(option.rect.adjusted(
           border_offset, border_offset,
           -border_offset - 1, -border_offset - 1
       ))

       inset += width

Flash Animations
================

List Item Flash
---------------

List items (orchestrators and steps) flash by temporarily increasing background opacity to 100%:

.. code-block:: python

   from openhcs.pyqt_gui.widgets.shared.list_item_flash_animation import flash_list_item

   # Flash step list item
   flash_list_item(
       list_widget=self.step_list,
       row=step_index,
       scope_id=f"{self.current_plate}::{step_token}@{step_index}",
       item_type=ListItemType.STEP
   )

**Design**: Flash animators do NOT store item references (items can be destroyed during flash). Instead, they store ``(list_widget, row, scope_id, item_type)`` for color recomputation.

Widget Flash
------------

Form widgets (QLineEdit, QComboBox, etc.) flash using QPalette manipulation:

.. code-block:: python

   from openhcs.pyqt_gui.widgets.shared.widget_flash_animation import flash_widget

   # Flash widget to indicate inherited value update
   flash_widget(line_edit)

**Flash mechanism**:

1. Store original palette
2. Apply light green flash color (144, 238, 144 RGB at 100 alpha)
3. Restore original palette after 300ms

Enum-Driven Polymorphic Dispatch
=================================

The system uses enum-driven polymorphic dispatch to select correct background colors without conditionals:

.. code-block:: python

   class ListItemType(Enum):
       """Type of list item for scope-based coloring.

       Uses enum-driven polymorphic dispatch pattern:
       - Enum value stores method name
       - Enum method uses getattr() for polymorphic dispatch
       """
       ORCHESTRATOR = "to_qcolor_orchestrator_bg"
       STEP = "to_qcolor_step_item_bg"

       def get_background_color(self, color_scheme: ScopeColorScheme) -> QColor:
           """Get background color using polymorphic dispatch."""
           method = getattr(color_scheme, self.value)
           return method()

**Pattern follows OpenHCS ProcessingContract enum design**: Extensible without modifying existing code.

Integration Examples
====================

Pipeline Editor Integration
---------------------------

.. code-block:: python

   from openhcs.pyqt_gui.widgets.mixins import CrossWindowPreviewMixin

   class PipelineEditorWidget(QWidget, CrossWindowPreviewMixin):
       def _refresh_step_items_by_index(
           self,
           indices: List[int],
           live_context_snapshot,
           label_subset: Optional[Set[int]] = None,
           changed_fields: Optional[Set[str]] = None,
           live_context_before=None,
       ) -> None:
           """Refresh step items with incremental updates and flash animations.

           Critical ordering: Apply styling BEFORE flash to prevent overwriting flash color.
           """
           for step_index in indices:
               step = self.pipeline_steps[step_index]
               item = self.step_list.item(step_index)

               should_update_labels = (
                   label_subset is None or step_index in label_subset
               )

               # Get preview instance (merges step-scoped live values)
               step_for_display = self._get_step_preview_instance(step, live_context_snapshot)

               # Format display text (resolves through hierarchy)
               display_text = self._format_resolved_step_for_display(
                   step_for_display, live_context_snapshot
               )

               # CRITICAL: Apply styling BEFORE flash (so flash color isn't overwritten)
               if should_update_labels:
                   self._apply_step_item_styling(item)

               # Flash on incremental update
               self._flash_step_item(step_index)

               # Update label
               if should_update_labels:
                   item.setText(display_text)

Plate Manager Integration
--------------------------

.. code-block:: python

   class PlateManagerWidget(QWidget, CrossWindowPreviewMixin):
       def _update_single_plate_item(self, plate_path: str) -> None:
           """Update plate item with flash detection."""
           # Get pipeline config before/after
           config_before = self._get_pipeline_config_preview_instance(
               plate_path, self._last_live_context_snapshot
           )
           config_after = self._get_pipeline_config_preview_instance(
               plate_path, self._collect_live_context()
           )

           # Check if resolved value changed
           if self._check_resolved_value_changed(
               config_before, config_after, self._pending_changed_fields
           ):
               self._flash_plate_item(plate_path)

Common Pitfalls and Maintenance Notes
======================================

This section documents common mistakes and architectural issues discovered during development.

Using After Snapshot for Expansion (WRONG)
-------------------------------------------

**Problem**: When expanding identifiers for window close events, using ``live_context_after`` to determine field types fails because the form manager has been unregistered.

.. code-block:: python

   # WRONG: live_context_after has NO values for window close events
   def _expand_identifiers_for_inheritance(self, obj, changed_fields, live_context_after):
       field_type = self._get_field_type_from_context(live_context_after)  # Returns None!

**Solution**: Use ``live_context_before`` which still has the form manager's values:

.. code-block:: python

   # CORRECT: live_context_before has form manager's values
   def _expand_identifiers_for_inheritance(self, obj, changed_fields, live_context_before):
       field_type = self._get_field_type_from_context(live_context_before)  # Works!

**Why this happens**: The "after" snapshot is collected AFTER the form manager is unregistered, so it doesn't include the form manager's values. The "before" snapshot is collected BEFORE unregistering, so it has all the values needed for type introspection.

Storing Event-Specific State on Listeners (WRONG)
--------------------------------------------------

**Problem**: Early implementations stored window close snapshots as attributes on listener widgets (``_window_close_before_snapshot``, ``_window_close_after_snapshot``). This caused ``AttributeError`` on long-lived widgets created before the attributes were added.

.. code-block:: python

   # WRONG: Storing event-specific state on listeners
   def handle_cross_window_preview_change(self, field_path, ...):
       if self._window_close_before_snapshot is not None:  # AttributeError!
           # Use window close snapshots

**Solution**: Pass snapshots as parameters to a dedicated ``handle_window_close()`` method:

.. code-block:: python

   # CORRECT: Event data passed as parameters
   def handle_window_close(self, editing_object, context_object,
                          before_snapshot, after_snapshot, changed_fields):
       # Snapshots are parameters, not listener state

**Architectural principle**: Window close is a form manager event, not listener state. Event-specific data should be passed as parameters, not stored on listeners.

Forgetting to Use Scoped Values (WRONG)
----------------------------------------

**Problem**: When resolving values for plate-specific or step-specific objects, using only ``live_context_snapshot.values`` (global context) misses scoped values.

.. code-block:: python

   # WRONG: Only checks global values
   pipeline_config_values = live_context_snapshot.values.get(PipelineConfig, {})

**Solution**: Extract scoped values using the object's scope_id:

.. code-block:: python

   # CORRECT: Use scoped values for plate/step-specific objects
   scope_id = self._extract_scope_id_for_preview(editing_object, context_object)
   if scope_id and live_context_snapshot:
       scoped_values = live_context_snapshot.scoped_values.get(scope_id, {})
       pipeline_config_values = scoped_values.get(PipelineConfig, {})

**When to use scoped values**:

- **PipelineConfig**: Always use scoped values (keyed by plate_path)
- **FunctionStep**: Always use scoped values (keyed by plate_path::step_index)
- **GlobalPipelineConfig**: Always use global values

Hardcoding Type Names Instead of Using Canonical Roots (WRONG)
---------------------------------------------------------------

**Problem**: Checking only for uppercase type names misses canonicalized lowercase roots.

.. code-block:: python

   # WRONG: Only detects uppercase type names
   if first_part[0].isupper():
       # Handle parent type format

**Solution**: Check both uppercase type names AND canonical roots:

.. code-block:: python

   # CORRECT: Detects both formats
   is_type_or_root = first_part[0].isupper() or first_part in self._preview_scope_aliases.values()
   if is_type_or_root:
       # Handle parent type format

**Why both are needed**: Form managers send ``"PipelineConfig.well_filter_config"`` but the mixin canonicalizes to ``"pipeline_config.well_filter_config"``. Both formats must be recognized as parent type paths.

Using resolve_all_lazy_attrs for Non-Lazy Fields (WRONG)
---------------------------------------------------------

**Problem**: ``resolve_all_lazy_attrs()`` only resolves fields that are lazy (None or LazyDataclass). For inherited attributes on non-dataclass objects like FunctionStep, this misses concrete inherited values.

.. code-block:: python

   # WRONG: Misses inherited concrete values
   before_attrs = resolver.resolve_all_lazy_attrs(step_before, ...)
   # Only resolves lazy fields, misses step_well_filter_config if it's concrete

**Solution**: Use ``resolve_all_config_attrs()`` which resolves ALL config attributes:

.. code-block:: python

   # CORRECT: Resolves all config attributes (lazy or concrete)
   before_attrs = resolver.resolve_all_config_attrs(step_before, field_names, ...)

**When to use which**:

- ``resolve_all_lazy_attrs()``: For dataclass objects where you want ALL fields
- ``resolve_all_config_attrs()``: For specific field names on any object (dataclass or not)

Future Refactoring Opportunities
---------------------------------

The current system works but has architectural complexity that should be addressed in future refactoring:

1. **Dual identifier format**: Establish single canonical format (lowercase) throughout the system instead of supporting both uppercase type names and lowercase canonical roots

2. **Scope ID extraction**: Move scope extraction logic to a centralized service instead of duplicating it in mixins

3. **Snapshot structure**: Consider flattening ``scoped_values`` to avoid nested dict lookups (``scoped_values[scope_id][Type][field_name]`` → ``scoped_values[(scope_id, Type)][field_name]``)

4. **Expansion logic**: The three identifier formats could be unified with a more generic pattern matching system

5. **Batch resolution API**: The distinction between ``resolve_all_lazy_attrs()`` and ``resolve_all_config_attrs()`` is confusing; consider a single method with a flag

**Important**: These refactorings should only be done after the system is stable and thoroughly documented. The current implementation is production-grade and works correctly; premature refactoring would introduce risk.

Debugging Flash Detection Issues
=================================

When flash detection doesn't work as expected, use these debugging techniques:

Check the Logs
--------------

OpenHCS logs are stored in ``~/.local/share/openhcs/logs/``. The most recent log file contains detailed information about flash detection:

.. code-block:: bash

   # Find most recent log
   ls -t ~/.local/share/openhcs/logs/openhcs_unified_*.log | head -1

   # Check window close events
   tail -3000 <logfile> | grep -E "(handle_window_close|Using window_close|FLASHING)"

   # Check identifier expansion
   tail -3000 <logfile> | grep "Expanded to.*identifiers"

   # Check snapshot collection
   tail -3000 <logfile> | grep "Stored window close snapshots"

**Key log messages**:

- ``"handle_window_close: N changed fields"`` - Window close event received with N fields
- ``"Stored window close snapshots: before=X, after=Y"`` - Snapshots stored in pending state
- ``"Using window_close snapshots: before=X, after=Y"`` - Timer callback using snapshots
- ``"Expanded 'field' to include N identifiers"`` - Identifier expansion results
- ``"🔥 FLASHING step X"`` - Flash triggered for step X
- ``"Results: N changed"`` - Batch resolution found N changed fields

Verify Snapshot Contents
-------------------------

Add debug logging to inspect snapshot contents:

.. code-block:: python

   def handle_window_close(self, editing_object, context_object,
                          before_snapshot, after_snapshot, changed_fields):
       logger.debug(f"Before snapshot values: {before_snapshot.values}")
       logger.debug(f"Before snapshot scoped_values: {before_snapshot.scoped_values}")
       logger.debug(f"After snapshot values: {after_snapshot.values}")
       logger.debug(f"After snapshot scoped_values: {after_snapshot.scoped_values}")

**What to check**:

- **Before snapshot should have form manager's values**: Check that ``before_snapshot.scoped_values[scope_id][PipelineConfig]`` contains the edited values
- **After snapshot should NOT have form manager's values**: Check that ``after_snapshot.scoped_values[scope_id][PipelineConfig]`` has reverted to saved values
- **Scope ID must match**: The scope_id used to extract values must match the scope_id used by the form manager

Verify Identifier Expansion
----------------------------

Add debug logging to see what identifiers are being expanded:

.. code-block:: python

   def _expand_identifiers_for_inheritance(self, obj, changed_fields, live_context_snapshot):
       logger.debug(f"Expanding identifiers: {changed_fields}")
       expanded = self._do_expansion(...)
       logger.debug(f"Expanded to {len(expanded)} identifiers: {expanded}")
       return expanded

**What to check**:

- **Simple fields should expand to nested paths**: ``"well_filter"`` → ``{"well_filter_config.well_filter", "step_well_filter_config.well_filter", ...}``
- **Parent type paths should expand to all nested fields**: ``"PipelineConfig.well_filter_config"`` → ``{"step_well_filter_config.well_filter", "step_well_filter_config.well_filter_mode", ...}``
- **Expansion should use live_context_before**: If expansion returns empty set, check that you're using ``live_context_before`` not ``live_context_after``

Verify Batch Resolution
------------------------

Add debug logging to see what values are being compared:

.. code-block:: python

   def _check_with_batch_resolution(self, obj_before, obj_after, field_names, ...):
       before_attrs = resolver.resolve_all_config_attrs(obj_before, field_names, ...)
       after_attrs = resolver.resolve_all_config_attrs(obj_after, field_names, ...)

       logger.debug(f"Before attrs: {before_attrs}")
       logger.debug(f"After attrs: {after_attrs}")

       for field_name in field_names:
           if before_attrs[field_name] != after_attrs[field_name]:
               logger.debug(f"Field '{field_name}' changed: {before_attrs[field_name]} → {after_attrs[field_name]}")

**What to check**:

- **Values should be resolved, not lazy**: If you see ``LazyWellFilterConfig(...)`` in the output, resolution failed
- **Before/after should differ for changed fields**: If values are identical but flash isn't triggering, check the flash triggering logic
- **Scoped values should be used**: For plate/step objects, verify that scoped values are being used, not global values

Common Symptoms and Solutions
------------------------------

**Symptom**: PlateManager flashes but PipelineEditor steps don't

**Cause**: Identifier expansion not finding step-specific fields

**Solution**: Check that expansion logic handles parent type paths (``"PipelineConfig.well_filter_config"``) and expands to step-specific fields (``"step_well_filter_config.well_filter"``)

---

**Symptom**: No flash on window close, but flash works on incremental updates

**Cause**: Window close snapshots not being captured or passed correctly

**Solution**: Verify that ``handle_window_close()`` is being called and that before/after snapshots differ

---

**Symptom**: AttributeError on ``_window_close_before_snapshot``

**Cause**: Old code storing snapshots as listener attributes instead of passing as parameters

**Solution**: Update to use ``handle_window_close()`` method with snapshot parameters

---

**Symptom**: Flash triggers on every window close, even when no values changed

**Cause**: Comparing wrong snapshots or not using scoped values

**Solution**: Verify that before snapshot has form manager values, after snapshot doesn't, and scoped values are being used for plate/step objects

Performance Characteristics
===========================

**Flash Detection**: O(1) per changed field (simple attribute comparison on preview instances)

**Color Generation**: O(1) with caching (colors computed once per scope_id and cached)

**Border Rendering**: O(n) where n = number of border layers (typically 1-3)

**Memory**: Minimal overhead (flash animators store only (widget_id, row, scope_id, item_type))

Configuration
=============

All visual parameters are centralized in ``ScopeVisualConfig``:

.. code-block:: python

   from openhcs.pyqt_gui.widgets.shared.scope_visual_config import ScopeVisualConfig

   config = ScopeVisualConfig()

   # Flash settings
   config.FLASH_DURATION_MS = 300
   config.LIST_ITEM_FLASH_ENABLED = True
   config.WIDGET_FLASH_ENABLED = True

   # Color settings (HSV)
   config.ORCHESTRATOR_HUE_RANGE = (0, 360)
   config.ORCHESTRATOR_SATURATION = 50
   config.ORCHESTRATOR_VALUE = 80
   config.ORCHESTRATOR_BG_ALPHA = 15  # 15% opacity

   config.STEP_HUE_RANGE = (0, 360)
   config.STEP_SATURATION = 40
   config.STEP_VALUE = 85
   config.STEP_BG_ALPHA = 5  # 5% opacity

   # Border settings
   config.ORCHESTRATOR_BORDER_WIDTH = 3
   config.STEP_BORDER_BASE_WIDTH = 2

See Also
========

- :doc:`gui_performance_patterns` - Cross-window preview system and incremental updates
- :doc:`configuration_framework` - Lazy dataclass resolution and context system
- :doc:`cross_window_update_optimization` - Type-based inheritance filtering
- :doc:`parameter_form_lifecycle` - Form lifecycle and context synchronization

