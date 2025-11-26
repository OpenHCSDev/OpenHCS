====================================
Scope Hierarchy for Live Context
====================================

*Module: openhcs.pyqt_gui.widgets.shared.parameter_form_manager*  
*Status: STABLE*

---

Overview
========

Multiple orchestrators can exist simultaneously (different plates, different pipelines). The scope hierarchy system prevents cross-orchestrator parameter bleed-through by ensuring step and function editors only see parameters from their own orchestrator context.

Problem Context
===============

Without scope isolation, parameter forms collect live context from all open windows:

.. code-block:: python

    # Orchestrator A: Plate 1, Step 1
    step_editor_A.get_parameter('gaussian_sigma')  # Should see Step 1 values
    
    # Orchestrator B: Plate 2, Step 2 (different plate!)
    step_editor_B.get_parameter('gaussian_sigma')  # Should NOT see Step 1 values
    
    # Without scope isolation:
    # Both editors see each other's parameters → incorrect placeholder text

Scope isolation ensures each editor only sees parameters from its own orchestrator.

Solution: Hierarchical Scope IDs
=================================

Scope IDs create a hierarchy that matches the orchestrator → step relationship.

**Current Implementation** (uses ``::`` separator and plate_path):

.. code-block:: python

    # Orchestrator/Plate scope (unique per plate)
    plate_scope = str(orchestrator.plate_path)
    # Example: "/data/plates/plate_001"

    # Step scope (inherits plate scope)
    step_token = getattr(step, '_pipeline_scope_token', step.name)
    step_scope = f"{plate_scope}::{step_token}"
    # Example: "/data/plates/plate_001::step_0"

**Note**: The ``::`` (double colon) separator is used for hierarchical scoping, not ``.`` (period).

Editors with matching scope prefixes share live context. Editors with different scopes are isolated.

Scope Hierarchy Architecture
=============================

Two-Level Hierarchy
--------------------

.. code-block:: python

    # Level 1: Plate/Orchestrator (uses actual plate_path)
    scope_id = "/data/plates/plate_001"
    # Shared by: All config editors for this plate

    # Level 2: Step (inherits plate scope with :: separator)
    scope_id = "/data/plates/plate_001::step_0"
    # Shared by: Step editor and its function editor for this specific step

**Real Examples from Code**:

.. code-block:: python

    # From dual_editor_window.py:240-245
    def _build_step_scope_id(self, fallback_name: str) -> str:
        plate_scope = getattr(self.orchestrator, 'plate_path', 'no_orchestrator')
        token = getattr(self.editing_step, '_pipeline_scope_token', None)
        if token:
            return f"{plate_scope}::{token}"
        return f"{plate_scope}::{fallback_name}"

    # From plate_manager.py:419, 1141
    scope_id = str(orchestrator.plate_path)  # Plate-level config editing

**Key insight**: Step and function editors share the same scope prefix (including step token), enabling them to see each other's live parameters while remaining isolated from other orchestrators and other steps.

Scope Matching Logic
--------------------

**Actual Implementation** (from ``parameter_form_manager.py:375-393``):

.. code-block:: python

    @staticmethod
    def _is_scope_visible_static(manager_scope: str, filter_scope) -> bool:
        """
        Check if scopes match (prefix matching for hierarchical scopes).
        Supports generic hierarchical scope strings like 'x::y::z'.
        """
        # Convert filter_scope to string if it's a Path
        filter_scope_str = str(filter_scope) if not isinstance(filter_scope, str) else filter_scope

        return (
            manager_scope == filter_scope_str or
            manager_scope.startswith(f"{filter_scope_str}::") or
            filter_scope_str.startswith(f"{manager_scope}::")
        )

**Examples**:

.. code-block:: python

    # Same plate: plate scope matches step scope (parent-child)
    _is_scope_visible_static(
        "/data/plates/plate_001::step_0",     # manager_scope (step)
        "/data/plates/plate_001"               # filter_scope (plate)
    )
    # → True (step scope starts with "plate_scope::")

    # Different plates: no match
    _is_scope_visible_static(
        "/data/plates/plate_001::step_0",     # manager_scope
        "/data/plates/plate_002"               # filter_scope
    )
    # → False (different plate prefixes)

This ensures step and function editors see each other's parameters (same plate/step) while remaining isolated from other orchestrators.

Implementation Patterns
=======================

Dual Editor Window
------------------

Step and function editors share scope to enable parameter synchronization.

**Actual Implementation** (from ``dual_editor_window.py:240-267``):

.. code-block:: python

    class DualEditorWindow(BaseFormDialog):
        def _build_step_scope_id(self, fallback_name: str) -> str:
            plate_scope = getattr(self.orchestrator, 'plate_path', 'no_orchestrator')
            token = getattr(self.editing_step, '_pipeline_scope_token', None)
            if token:
                return f"{plate_scope}::{token}"
            return f"{plate_scope}::{fallback_name}"

        def create_step_tab(self):
            step_name = getattr(self.editing_step, 'name', 'unknown_step')
            scope_id = self._build_step_scope_id(step_name)
            # Result: "/data/plates/plate_001::step_0"

            # Step editor uses step scope
            self.step_editor = StepParameterEditorWidget(
                self.editing_step,
                scope_id=scope_id
            )

        def create_function_tab(self):
            step_name = getattr(self.editing_step, 'name', 'unknown_step')
            scope_id = self._build_step_scope_id(step_name)
            # Same scope as step editor!

            # Function editor uses same step scope
            self.func_editor = FunctionListEditorWidget(
                scope_id=scope_id  # Same as step editor
            )

**Why same scope?** Function editor needs to see step parameters (e.g., ``processing_config.group_by``) for placeholder resolution.

Function List Editor
--------------------

.. code-block:: python

    class FunctionListEditor(QWidget):
        def __init__(self, step, scope_id):
            self.step = step
            self.scope_id = scope_id  # Inherited from dual editor
            
        def refresh_from_step_context(self):
            """Refresh function editor when step parameters change."""
            # Collect live context from step editor (same scope)
            live_context = self._collect_live_context()
            
            # Resolve group_by placeholder using step's processing_config
            group_by_value = self._resolve_group_by_placeholder(live_context)
            
            # Update UI
            self.group_by_selector.setCurrentValue(group_by_value)

Config Window
-------------

Config windows use plate-scoped or global scope depending on the config being edited.

**Actual Implementation** (from ``config_window.py:59,77,117`` and ``plate_manager.py:1141-1148``):

.. code-block:: python

    class ConfigWindow(BaseFormDialog):
        def __init__(self, config_class, current_config, ...,
                     scope_id: Optional[str] = None):
            # scope_id passed from caller
            self.scope_id = scope_id

            self.form_manager = ParameterFormManager.from_dataclass_instance(
                dataclass_instance=current_config,
                scope_id=self.scope_id  # Plate-scoped or None for global
            )

    # From plate_manager.py - creating plate-scoped config window
    scope_id = str(orchestrator.plate_path) if orchestrator else None
    config_window = ConfigWindow(
        config_class,
        current_config,
        scope_id=scope_id  # "/data/plates/plate_001" or None
    )

**Scope Semantics**:

- ``scope_id=None``: Global config (GlobalPipelineConfig) - visible to all orchestrators
- ``scope_id="/data/plates/plate_001"``: Plate-scoped config (PipelineConfig) - only visible to this plate's editors

Scope Isolation Examples
=========================

Isolated Orchestrators
-----------------------

.. code-block:: python

    # Orchestrator A: Plate 1
    orchestrator_A = PipelineOrchestrator(plate_path=Path("/data/plates/plate_001"))
    scope_A = str(orchestrator_A.plate_path)  # "/data/plates/plate_001"

    # Orchestrator B: Plate 2
    orchestrator_B = PipelineOrchestrator(plate_path=Path("/data/plates/plate_002"))
    scope_B = str(orchestrator_B.plate_path)  # "/data/plates/plate_002"

    # Step editors are isolated (using actual implementation)
    step_editor_A = StepParameterEditor(step_A, scope_id=f"{scope_A}::step_0")
    step_editor_B = StepParameterEditor(step_B, scope_id=f"{scope_B}::step_0")
    # step_editor_A: "/data/plates/plate_001::step_0"
    # step_editor_B: "/data/plates/plate_002::step_0"

    # step_editor_A does NOT see step_editor_B's parameters
    # Different scope prefixes: "/data/plates/plate_001" vs "/data/plates/plate_002"

Shared Step/Function Context
-----------------------------

.. code-block:: python

    # Same plate, same step
    plate_scope = "/data/plates/plate_001"
    step_scope = f"{plate_scope}::step_0"  # "/data/plates/plate_001::step_0"

    # Step editor
    step_editor = StepParameterEditor(step, scope_id=step_scope)

    # Function editor (same scope!)
    function_editor = FunctionListEditor(step, scope_id=step_scope)

    # function_editor DOES see step_editor's parameters
    # Same scope: "/data/plates/plate_001::step_0"

Cross-Window Synchronization
=============================

The scope system enables selective cross-window synchronization:

.. code-block:: python

    # User edits step parameter in step editor
    step_editor.update_parameter('processing_config.group_by', GroupBy.WELL)
    
    # Triggers cross-window refresh
    ParameterFormManager.trigger_global_cross_window_refresh()
    
    # Function editor receives refresh signal (same scope)
    function_editor.refresh_from_step_context()
    
    # Function editor sees updated group_by value
    # Updates group_by selector to match step editor

**Key insight**: Scope matching ensures only related windows refresh, preventing unnecessary updates.

Implementation Notes
====================

**🔬 Source Code**: 

- Scope matching: ``openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`` (line 2948)
- Dual editor scope setup: ``openhcs/pyqt_gui/windows/dual_editor_window.py`` (line 244)
- Function editor scope: ``openhcs/pyqt_gui/widgets/function_list_editor.py`` (line 36)

**🏗️ Architecture**: 

- :doc:`parameter_form_manager_live_context` - Live context collection
- :doc:`../architecture/configuration-management-system` - Configuration hierarchy

**📊 Performance**: 

- Scope matching is O(n) where n = number of active form managers
- Typically < 10 managers active, so overhead is negligible
- Scope string comparison is fast (prefix matching)

Key Design Decisions
====================

**Why use plate_path for orchestrator scope instead of object ID?**

- Plate path is semantically meaningful (shows which plate the editor is for)
- Plate path is stable across sessions (object ID changes each run)
- Plate path enables future scope persistence/serialization
- In practice, only one orchestrator per plate is active at a time

**Why use ``::`` separator instead of ``.``?**

- Avoids conflicts with file paths (which use ``.`` for extensions)
- More visually distinct in logs and debugging
- Consistent with other path-like separators in the codebase

**Why share scope between step and function editors?**

Function editor needs step parameters for placeholder resolution (e.g., ``group_by`` selector). Sharing scope enables this without manual parameter passing.

**Why use strings for scope IDs?**

Scope IDs are strings, enabling serialization and comparison without object reference issues.

Common Gotchas
==============

- **Don't use global scope (``None``) for plate-specific editors**: Each plate must have unique scope (``plate_path``) to prevent parameter bleed-through
- **Step and function editors must share scope**: Function editor needs step parameters for placeholder resolution
- **Scope IDs are immutable**: Don't change ``scope_id`` after form manager creation
- **Scope matching uses ``::`` separator**: ``"/data/plates/plate_001"`` matches ``"/data/plates/plate_001::step_0"`` but not ``"/data/plates/plate_002"``
- **Separator matters**: Use ``::`` (double colon), not ``.`` (period) or ``:`` (single colon)

Debugging Scope Issues
======================

Symptom: Function Editor Not Syncing
-------------------------------------

**Cause**: Step and function editors have different scopes

**Diagnosis**:

.. code-block:: python

    # Check scope IDs
    logger.debug(f"Step editor scope: {step_editor.form_manager.scope_id}")
    logger.debug(f"Function editor scope: {function_editor.scope_id}")
    # Should be identical (including step token)

**Fix**: Ensure both editors use same ``scope_id`` from ``_build_step_scope_id()``

Symptom: Cross-Orchestrator Bleed-Through
------------------------------------------

**Cause**: Multiple orchestrators sharing same scope prefix

**Diagnosis**:

.. code-block:: python

    # Check orchestrator/plate scopes
    logger.debug(f"Orchestrator A scope: {scope_A}")
    logger.debug(f"Orchestrator B scope: {scope_B}")
    # Should have different plate_path prefixes

**Fix**: Ensure each orchestrator uses unique ``plate_path`` as scope prefix


Pipeline Editor Preview Labels
===============================

The pipeline editor displays real-time preview labels (MAT, NAP, FIJI, FILT) that show which configurations are enabled for each step. These labels must update immediately when fields are changed in the step editor, including when fields are reset to None.

Critical Implementation Details
--------------------------------

**Problem**: Preview labels were not updating when resetting fields that had concrete saved values.

**Root Cause**: The pipeline editor was resolving config objects from the original saved step instead of from the merged step with live values.

When a step is saved with a concrete value (e.g., ``napari_streaming_config.enabled=True``), and then reset to None in the step editor:

1. The live form manager has ``enabled=None`` in its current values
2. The pipeline editor collects live context and merges it into a new step object
3. **BUG**: The config object being resolved was from the ORIGINAL saved step, not the merged step
4. Result: Lazy resolution sees the saved concrete value instead of the live None value

**Solution**: Resolve config from merged step, not original step

.. code-block:: python

    # WRONG: Resolve from original step's config
    config = getattr(step, 'napari_streaming_config')  # Has saved enabled=True
    # ... merge live values into step ...
    resolved = config.enabled  # Still resolves to True!

    # CORRECT: Resolve from merged step's config
    step_to_use = merge_live_values(step, live_values)  # Has enabled=None
    config = getattr(step_to_use, 'napari_streaming_config')  # Has live enabled=None
    resolved = config.enabled  # Correctly resolves to None, walks up context

**Implementation** (``openhcs/pyqt_gui/widgets/pipeline_editor.py``):

.. code-block:: python

    # Build merged step with live values
    step_to_use = step
    if step_live_values:
        step_to_use = self._merge_live_values(step, step_live_values)

    # CRITICAL: Get config from merged step, not original step!
    config_to_resolve = getattr(step_to_use, config_attr_name, config)

    # Now resolve through context stack
    with config_context(global_config):
        with config_context(pipeline_config):
            with config_context(step_to_use):
                resolved_value = config_to_resolve.enabled

This ensures that when a field is reset to None in the step editor, the pipeline editor sees the None value and correctly resolves it through the context hierarchy (GlobalPipelineConfig → PipelineConfig → Step).

Scope Matching for Step Editors
--------------------------------

The pipeline editor must match step editors by scope_id to collect the correct live values:

.. code-block:: python

    # Build step-specific scope
    step_scope = f"{plate_path}::{step.name}"

    # Only collect live context from:
    # 1. Global scope (None)
    # 2. Exact plate scope match
    # 3. Exact step scope match (for THIS specific step)
    is_visible = (
        manager.scope_id is None or
        manager.scope_id == plate_scope or
        manager.scope_id == step_scope
    )

This prevents collecting live values from other step editors in the same plate, ensuring each step's preview labels only reflect its own editor's state.

Critical Pattern: Always Use Preview Instances for Resolution
==============================================================

**CRITICAL RULE**: When resolving config attributes for display (flash detection, unsaved changes, preview labels), you MUST use preview instances with scoped live values merged, not the original objects.

Why This Matters
-----------------

The live context snapshot contains scoped values in ``scoped_values[scope_id][obj_type]``, but these values are NOT automatically visible during resolution unless you merge them into the object first.

**Common Bug Pattern** (WRONG):

.. code-block:: python

    # WRONG: Use original step directly
    def _resolve_config_attr(self, step, config, attr_name, live_context_snapshot):
        context_stack = [global_config, pipeline_config, step]  # Original step!

        # Resolution will NOT see step editor changes because step doesn't have
        # the live values merged into it yet
        resolved = resolver.resolve_config_attr(config, attr_name, context_stack)

**Correct Pattern** (RIGHT):

.. code-block:: python

    # CORRECT: Get preview instance with scoped live values merged
    def _resolve_config_attr(self, step, config, attr_name, live_context_snapshot):
        # CRITICAL: Merge scoped live values into step BEFORE building context stack
        step_preview = self._get_step_preview_instance(step, live_context_snapshot)

        context_stack = [global_config, pipeline_config, step_preview]  # Preview instance!

        # Now resolution sees step editor changes
        resolved = resolver.resolve_config_attr(config, attr_name, context_stack)

Single Source of Truth: _build_context_stack_with_live_values
--------------------------------------------------------------

To prevent this bug from recurring, use a centralized helper that enforces the pattern:

.. code-block:: python

    def _build_context_stack_with_live_values(
        self,
        step: FunctionStep,  # Original step (NOT preview instance)
        live_context_snapshot: Optional[LiveContextSnapshot]
    ) -> Optional[list]:
        """
        Build context stack for resolution with live values merged.

        CRITICAL: This MUST use preview instances (with scoped live values merged)
        for all objects in the context stack.

        Pattern:
        1. Get preview instance for each object (merges scoped live values)
        2. Build context stack: GlobalPipelineConfig → PipelineConfig → Step
        3. Pass to LiveContextResolver

        This is the SINGLE SOURCE OF TRUTH for building context stacks.
        All resolution code (flash detection, unsaved changes, label updates)
        MUST use this method.
        """
        # Get preview instances with scoped live values merged
        global_config = self._get_global_config_preview_instance(live_context_snapshot)
        pipeline_config = self._get_pipeline_config_preview_instance(live_context_snapshot)
        step_preview = self._get_step_preview_instance(step, live_context_snapshot)

        # Build context stack with preview instances
        return [global_config, pipeline_config, step_preview]

**Usage**:

.. code-block:: python

    # Flash detection
    def _build_flash_context_stack(self, obj, live_context_snapshot):
        return self._build_context_stack_with_live_values(obj, live_context_snapshot)

    # Unsaved changes detection
    def _resolve_config_attr(self, step, config, attr_name, live_context_snapshot):
        context_stack = self._build_context_stack_with_live_values(step, live_context_snapshot)
        return resolver.resolve_config_attr(config, attr_name, context_stack, ...)

Generic Helper: _get_preview_instance_generic
----------------------------------------------

The ``CrossWindowPreviewMixin`` provides a generic helper for extracting and merging live values:

.. code-block:: python

    def _get_preview_instance_generic(
        self,
        obj: Any,
        obj_type: type,
        scope_id: Optional[str],
        live_context_snapshot: Optional[LiveContextSnapshot],
        use_global_values: bool = False
    ) -> Any:
        """
        Generic preview instance getter with scoped live values merged.

        This is the SINGLE SOURCE OF TRUTH for extracting and merging live values
        from LiveContextSnapshot.

        Args:
            obj: Original object to merge live values into
            obj_type: Type to look up in scoped_values or values dict
            scope_id: Scope identifier (e.g., "/path/to/plate::step_0")
                     Ignored if use_global_values=True
            use_global_values: If True, use snapshot.values (for GlobalPipelineConfig)
                              If False, use snapshot.scoped_values[scope_id]

        Returns:
            Object with live values merged, or original object if no live values
        """

**Usage Examples**:

.. code-block:: python

    # For GlobalPipelineConfig (uses global values)
    global_preview = self._get_preview_instance_generic(
        obj=self.global_config,
        obj_type=GlobalPipelineConfig,
        scope_id=None,
        live_context_snapshot=snapshot,
        use_global_values=True  # Use snapshot.values
    )

    # For PipelineConfig (uses scoped values)
    pipeline_preview = self._get_preview_instance_generic(
        obj=orchestrator.pipeline_config,
        obj_type=PipelineConfig,
        scope_id=str(plate_path),  # Plate scope
        live_context_snapshot=snapshot,
        use_global_values=False  # Use snapshot.scoped_values[plate_path]
    )

    # For FunctionStep (uses scoped values)
    step_preview = self._get_preview_instance_generic(
        obj=step,
        obj_type=FunctionStep,
        scope_id=f"{plate_path}::{step_token}",  # Step scope
        live_context_snapshot=snapshot,
        use_global_values=False  # Use snapshot.scoped_values[step_scope]
    )

Implementation Requirements
---------------------------

Subclasses must implement ``_merge_with_live_values`` to define merge strategy:

.. code-block:: python

    def _merge_with_live_values(self, obj: Any, live_values: Dict[str, Any]) -> Any:
        """Merge object with live values from ParameterFormManager.

        For dataclasses: Use dataclasses.replace
        For non-dataclass objects: Use copy + setattr
        """
        reconstructed_values = self._live_context_resolver.reconstruct_live_values(live_values)

        if dataclasses.is_dataclass(obj):
            return dataclasses.replace(obj, **reconstructed_values)
        else:
            obj_clone = copy.deepcopy(obj)
            for field_name, value in reconstructed_values.items():
                setattr(obj_clone, field_name, value)
            return obj_clone

Historical Bug: Unsaved Changes Not Detected
---------------------------------------------

**Symptom**: Unsaved changes indicator (†) not appearing on step names when editing step configs.

**Root Cause**: ``_resolve_config_attr()`` was using the original step instead of a preview instance with scoped live values merged.

**Evidence**:

.. code-block:: python

    # Logs showed scoped values WERE being collected:
    live_context_snapshot.scoped_values keys: ['/home/ts/test_plate::step_6']

    # But resolution showed None for both live and saved:
    live=None vs saved=None

    # Because the original step was used, not the preview instance!

**Fix**: Use ``_get_step_preview_instance()`` to merge scoped live values before building context stack.

.. code-block:: python

    # Before (WRONG):
    context_stack = [global_config, pipeline_config, step]  # Original step

    # After (CORRECT):
    step_preview = self._get_step_preview_instance(step, live_context_snapshot)
    context_stack = [global_config, pipeline_config, step_preview]  # Preview instance

**Lesson**: The existing flash detection code was already using this pattern correctly. When implementing new resolution code, always check if similar code exists and follow the same pattern.


Window Close Flash Detection System
====================================

When a config window closes with unsaved changes, the system must detect which objects (steps, plates) had their resolved values change and flash them to provide visual feedback.

Critical Architecture Insight
------------------------------

**The before_snapshot must include ALL active form managers, not just the closing window.**

This is counterintuitive but essential for correct flash detection when multiple windows are open from different scopes.

Why This Matters
~~~~~~~~~~~~~~~~~

When a config window closes, we compare:

- **Before**: All form managers active (including the closing window)
- **After**: All form managers active (excluding the closing window)

If the before_snapshot only contains the closing window's values, preview instances won't have other open windows' values (like step overrides), causing incorrect flash detection.

**Example Bug Scenario**:

.. code-block:: python

    # Setup:
    # - PipelineConfig window open with well_filter=2 (plate scope)
    # - Step_6 window open with well_filter=3 (step scope override)
    # - User closes PipelineConfig without saving

    # WRONG: before_snapshot only has PipelineConfig values
    before_snapshot = closing_window._create_snapshot_for_this_manager()
    # before_snapshot.scoped_values = {"/plate_001": {PipelineConfig: {well_filter: 2}}}
    # Missing: step_6's override!

    # When creating step_6 preview instance for "before" context:
    step_6_preview_before = _get_preview_instance_generic(
        step_6,
        scope_id="/plate_001::step_6",
        live_context_snapshot=before_snapshot
    )
    # Looks for scoped_values["/plate_001::step_6"] → NOT FOUND
    # Falls back to plate scope → resolves to 2

    # When creating step_6 preview instance for "after" context:
    step_6_preview_after = _get_preview_instance_generic(
        step_6,
        scope_id="/plate_001::step_6",
        live_context_snapshot=after_snapshot
    )
    # Finds scoped_values["/plate_001::step_6"] → resolves to 3

    # Comparison: 2 != 3 → INCORRECTLY FLASHES step_6!
    # But step_6's resolved value didn't actually change (it was always 3 due to override)

**Correct Implementation**:

.. code-block:: python

    # CORRECT: before_snapshot includes ALL active form managers
    before_snapshot = ParameterFormManager.collect_live_context()
    # before_snapshot.scoped_values = {
    #     "/plate_001": {PipelineConfig: {well_filter: 2}},
    #     "/plate_001::step_6": {FunctionStep: {well_filter: 3}}  # Step override included!
    # }

    # When creating step_6 preview instance for "before" context:
    step_6_preview_before = _get_preview_instance_generic(
        step_6,
        scope_id="/plate_001::step_6",
        live_context_snapshot=before_snapshot
    )
    # Finds scoped_values["/plate_001::step_6"] → resolves to 3

    # When creating step_6 preview instance for "after" context:
    step_6_preview_after = _get_preview_instance_generic(
        step_6,
        scope_id="/plate_001::step_6",
        live_context_snapshot=after_snapshot
    )
    # Finds scoped_values["/plate_001::step_6"] → resolves to 3

    # Comparison: 3 == 3 → NO FLASH (correct!)

Scope Precedence in Resolution
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The scope hierarchy determines which value wins during resolution:

1. **Step scope** (``/plate_001::step_6``) - highest precedence (specificity=2)
2. **Plate scope** (``/plate_001``) - middle precedence (specificity=1)
3. **Global scope** (``None``) - lowest precedence (specificity=0)

When a step has its own override at step scope, it takes precedence over plate scope and global scope values. This is why the before_snapshot must include step overrides - otherwise resolution incorrectly uses lower-precedence values.

**Scope-Aware Priority Resolution** (Added in commit cf4f06b0):

The configuration resolution system now tracks scope information through the context stack and uses scope specificity to prioritize configs when multiple configs match during field resolution.

.. code-block:: python

    # From dual_axis_resolver.py
    def get_scope_specificity(scope_id: Optional[str]) -> int:
        """Calculate scope specificity for priority ordering.

        More specific scopes have higher values:
        - None (global): 0
        - "plate_path": 1
        - "plate_path::step": 2
        - "plate_path::step::nested": 3
        """
        if scope_id is None:
            return 0
        return scope_id.count('::') + 1

When multiple configs match during MRO traversal, the resolver sorts them by scope specificity and returns the value from the most specific scope. This ensures plate-scoped configs override global configs, and step-scoped configs override both.

**Context Manager Scope Tracking**:

The ``config_context()`` manager now accepts ``context_provider`` parameter for automatic scope derivation via the ``ScopedObject`` interface:

.. code-block:: python

    # From context_manager.py
    current_config_scopes: contextvars.ContextVar[Dict[str, Optional[str]]] = ...
    current_scope_id: contextvars.ContextVar[Optional[str]] = ...

    # Objects implementing ScopedObject can derive their own scope
    with config_context(pipeline_config, context_provider=orchestrator):
        # Scope information is automatically derived via pipeline_config.build_scope_id(orchestrator)
        # resolve_field_inheritance() can prioritize by scope specificity
        pass

**ScopedObject Interface**:

Objects that need scope identification implement the ``ScopedObject`` ABC:

.. code-block:: python

    from openhcs.config_framework import ScopedObject

    class GlobalPipelineConfig(ScopedObject):
        def build_scope_id(self, context_provider) -> Optional[str]:
            return None  # Global scope

    class PipelineConfig(GlobalPipelineConfig):
        def build_scope_id(self, context_provider) -> str:
            return str(context_provider.plate_path)

    class FunctionStep(ScopedObject):
        def build_scope_id(self, context_provider) -> str:
            return f"{context_provider.plate_path}::{self.token}"

Scope specificity is critical for sibling inheritance - the parent overlay must have the same scope as the current config to avoid being filtered out by the resolver. See :doc:`../architecture/sibling_inheritance_system` for details.

For UI code that only has scope strings (not full objects), use ``ScopeProvider``:

.. code-block:: python

    from openhcs.config_framework import ScopeProvider

    # UI code with only scope string
    scope_provider = ScopeProvider(scope_id="/plate_001::step_6")
    with config_context(step_config, context_provider=scope_provider):
        # Scope is provided without needing full orchestrator object
        pass

Implementation Pattern
~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

    # In parameter_form_manager.py, when window closes:
    def unregister_from_cross_window_updates(self):
        if self in type(self)._active_form_managers:
            # CRITICAL: Capture "before" snapshot BEFORE unregistering
            # This snapshot must include ALL active form managers (not just this one)
            before_snapshot = type(self).collect_live_context()

            # Remove from registry
            self._active_form_managers.remove(self)

            # Capture "after" snapshot AFTER unregistering
            after_snapshot = type(self).collect_live_context()

            # Notify listeners (e.g., pipeline editor) to check for flashes
            self.window_closed.emit(before_snapshot, after_snapshot, changed_fields)

LiveContextSnapshot Structure
==============================

The ``LiveContextSnapshot`` dataclass captures the state of all active form managers at a point in time.

Structure
---------

.. code-block:: python

    @dataclass
    class LiveContextSnapshot:
        token: int  # Cache invalidation token
        values: Dict[type, Dict[str, Any]]  # Global context (for GlobalPipelineConfig)
        scoped_values: Dict[str, Dict[type, Dict[str, Any]]]  # Scoped context (for PipelineConfig, FunctionStep)
        scopes: Dict[str, Optional[str]]  # Maps config type names to scope IDs for dual-axis resolution

**Key Differences**:

- ``values``: Global context, not scoped. Used for GlobalPipelineConfig.

  - Format: ``{GlobalPipelineConfig: {field_name: value, ...}}``
  - No scope_id key - these values are visible to all scopes

- ``scoped_values``: Scoped context, keyed by scope_id. Used for PipelineConfig and FunctionStep.

  - Format: ``{scope_id: {obj_type: {field_name: value, ...}}}``
  - Example: ``{"/plate_001": {PipelineConfig: {well_filter: 2}}}``
  - Example: ``{"/plate_001::step_6": {FunctionStep: {well_filter: 3}}}``

- ``scopes``: Maps config type names to their scope IDs for scope-aware resolution.

  - Format: ``{config_type_name: scope_id}``
  - Example: ``{"GlobalPipelineConfig": None, "PipelineConfig": "/plate_001", "FunctionStep": "/plate_001::step_6"}``
  - Used by ``_build_context_stack()`` to initialize the ``current_config_scopes`` ContextVar for dual-axis resolution
  - Enables scope specificity filtering to prevent parent scopes from seeing child scope values

Usage in Preview Instance Creation
-----------------------------------

.. code-block:: python

    def _get_preview_instance_generic(
        self,
        obj: Any,
        obj_type: type,
        scope_id: Optional[str],
        live_context_snapshot: Optional[LiveContextSnapshot],
        use_global_values: bool = False
    ) -> Any:
        """Extract live values from snapshot and merge into object."""

        if not live_context_snapshot:
            return obj

        # For GlobalPipelineConfig: use snapshot.values (global context)
        if use_global_values:
            live_values = live_context_snapshot.values.get(obj_type, {})

        # For PipelineConfig/FunctionStep: use snapshot.scoped_values[scope_id]
        else:
            if scope_id and scope_id in live_context_snapshot.scoped_values:
                live_values = live_context_snapshot.scoped_values[scope_id].get(obj_type, {})
            else:
                live_values = {}

        # Merge live values into object
        return self._merge_with_live_values(obj, live_values)

Framework-Level Cache Control
==============================

The ``FrameworkConfig`` provides master switches to disable caching systems for debugging cache-related bugs.

Environment Variables
---------------------

.. code-block:: bash

    # Disable all token-based caches
    export OPENHCS_DISABLE_TOKEN_CACHES=1

    # Disable specific caches
    export OPENHCS_DISABLE_LAZY_RESOLUTION_CACHE=1
    export OPENHCS_DISABLE_PLACEHOLDER_TEXT_CACHE=1
    export OPENHCS_DISABLE_LIVE_CONTEXT_RESOLVER_CACHE=1
    export OPENHCS_DISABLE_UNSAVED_CHANGES_CACHE=1

Configuration API
-----------------

.. code-block:: python

    from openhcs.config_framework import get_framework_config, FrameworkConfig

    # Get current framework config
    config = get_framework_config()

    # Check if caches are disabled
    if config.disable_lazy_resolution_cache:
        # Force full resolution without cache
        pass

**Integration Points**:

- ``LazyMethodBindings.__getattribute__``: Checks ``disable_lazy_resolution_cache`` before using cache
- ``LazyDefaultPlaceholderService``: Checks ``disable_placeholder_text_cache`` before using cache
- ``LiveContextResolver``: Checks ``disable_live_context_resolver_cache`` before using cache
- ``check_step_has_unsaved_changes()``: Checks ``disable_unsaved_changes_cache`` before using cache

**Use Case**: When debugging cache-related bugs, set ``OPENHCS_DISABLE_TOKEN_CACHES=1`` to force all systems to bypass caches and perform full resolution on every access.

Token-Based Cache Invalidation
===============================

The ``_live_context_token_counter`` is a class-level counter that increments on every parameter change, invalidating all caches globally.

How It Works
------------

.. code-block:: python

    class ParameterFormManager:
        _live_context_token_counter: int = 0  # Class-level counter

        def _emit_cross_window_change(self, param_name: str, value: Any):
            """Emit cross-window change signal and invalidate caches."""
            # Invalidate live context cache by incrementing token
            type(self)._live_context_token_counter += 1

            # Emit signal
            self.context_value_changed.emit(field_path, value, ...)

Every ``LiveContextSnapshot`` captures the current token value:

.. code-block:: python

    @staticmethod
    def collect_live_context(scope_filter=None) -> LiveContextSnapshot:
        """Collect live context from all active form managers."""
        # ... collect values ...

        # Capture current token
        token = ParameterFormManager._live_context_token_counter
        return LiveContextSnapshot(token=token, values=..., scoped_values=...)

Caches check if their cached token matches the current token:

.. code-block:: python

    def check_step_has_unsaved_changes(step, live_context_snapshot):
        """Check if step has unsaved changes (with caching)."""
        cache_key = (id(step), live_context_snapshot.token)

        # Check cache
        if cache_key in check_step_has_unsaved_changes._cache:
            return check_step_has_unsaved_changes._cache[cache_key]

        # Cache miss - compute result
        result = _compute_unsaved_changes(step, live_context_snapshot)

        # Cache result
        check_step_has_unsaved_changes._cache[cache_key] = result
        return result

**Key Insight**: Token-based invalidation is global and immediate. Any parameter change anywhere invalidates all caches, ensuring consistency.

Scoped Unsaved Changes Cache
=============================

**Added in commit cf4f06b0**

The unsaved changes cache is now scoped to prevent cross-step contamination. Previously, the cache was unscoped (``Dict[Type, Set[str]]``), causing step 6's unsaved changes to incorrectly mark all steps as having unsaved changes.

Cache Structure
---------------

.. code-block:: python

    # From parameter_form_manager.py
    # OLD (unscoped): Dict[Type, Set[str]]
    # NEW (scoped): Dict[Tuple[Type, Optional[str]], Set[str]]
    _configs_with_unsaved_changes: Dict[Tuple[Type, Optional[str]], Set[str]] = {}

    # Example cache entries:
    # (LazyWellFilterConfig, None) → {'well_filter'}  # Global scope
    # (LazyWellFilterConfig, "/plate") → {'well_filter_mode'}  # Plate scope
    # (LazyWellFilterConfig, "/plate::step_6") → {'well_filter'}  # Step scope

Multi-Level Cache Lookup
-------------------------

The fast-path now checks cache at multiple scope levels (step-specific, plate-level, global) using MRO chain traversal:

.. code-block:: python

    def check_step_has_unsaved_changes(step, ...):
        expected_step_scope = f"{plate_path}::step_token"

        for config_attr, config in step_configs.items():
            config_type = type(config)

            # Check the entire MRO chain (including parent classes)
            for mro_class in config_type.__mro__:
                # Try step-specific scope first
                step_cache_key = (mro_class, expected_step_scope)
                if step_cache_key in ParameterFormManager._configs_with_unsaved_changes:
                    has_any_relevant_changes = True
                    break

                # Try plate-level scope
                plate_scope = expected_step_scope.split('::')[0]
                plate_cache_key = (mro_class, plate_scope)
                if plate_cache_key in ParameterFormManager._configs_with_unsaved_changes:
                    has_any_relevant_changes = True
                    break

                # Try global scope (None)
                global_cache_key = (mro_class, None)
                if global_cache_key in ParameterFormManager._configs_with_unsaved_changes:
                    has_any_relevant_changes = True
                    break

**Cross-Step Isolation**: The scoped cache prevents step 6's unsaved changes from incorrectly marking step 0 as having unsaved changes.

**MRO Chain Traversal**: Checking the entire MRO chain ensures that changes to parent config types (e.g., ``WellFilterConfig``) are detected in child configs (e.g., ``StepWellFilterConfig``).

Cache Invalidation
------------------

The cache is invalidated when the live context token changes:

.. code-block:: python

    # From parameter_form_manager.py
    _configs_with_unsaved_changes_token: int = -1  # Token when cache was last populated

    # On value change:
    type(self)._live_context_token_counter += 1  # Invalidates cache

    # On reset:
    type(self)._clear_unsaved_changes_cache("reset_all")

Token-Based Instance Selection Pattern
=======================================

**Added in commit cf4f06b0**

When resolving config attributes for display (unsaved changes, preview labels), the system must choose between the preview instance (with live values) and the original instance (saved values) based on the context token.

Why This Matters
-----------------

The ``resolve_attr`` callback is used during resolution to fetch config attributes. When comparing live vs saved values, we need to ensure:

- **Live context**: Use preview instance (with live values merged)
- **Saved context**: Use original instance (saved values only)

The context token determines which instance to use.

Implementation Pattern
----------------------

.. code-block:: python

    # From pipeline_editor.py and plate_manager.py
    def _format_resolved_step_for_display(self, step_index, live_context_snapshot):
        original_step = self.pipeline_steps[step_index]
        step_preview = self._get_step_preview_instance(original_step, live_context_snapshot)

        def resolve_attr(parent_obj, config_obj, attr_name, context):
            # CRITICAL: Token-based instance selection
            # If context token matches live token, use preview instance
            # If context token is different (saved snapshot), use original instance
            is_live_context = (context.token == live_context_snapshot.token)
            step_to_use = step_preview if is_live_context else original_step

            return self._resolve_config_attr(step_to_use, config_obj, attr_name, context)

        # Pass resolve_attr callback to unsaved changes checker
        has_unsaved = check_step_has_unsaved_changes(
            original_step,
            config_indicators,
            resolve_attr,  # Callback uses token-based selection
            live_context_snapshot
        )

**Key Insight**: The ``context`` parameter in ``resolve_attr`` contains a token. When the checker creates a saved snapshot for comparison, it has a different token than the live snapshot. This allows the callback to automatically select the correct instance.

Window Close Scope Detection
=============================

**Added in commit cf4f06b0**

When a config window closes with unsaved changes, the system must detect whether the change affects all steps (global/plate-level) or only specific steps (step-level).

The Problem with '::' Separator
--------------------------------

**CRITICAL BUG**: The original logic assumed that ``::`` separator in ``scope_id`` means step scope, but plate paths can also contain ``::`` (e.g., ``/path/to/plate::with::colons``).

.. code-block:: python

    # WRONG: Can't rely on '::' separator
    if '::' in scope_id:
        # This is a step-specific change
        check_only_this_step = True
    else:
        # This is a global/plate-level change
        check_all_steps = True

**Counterexample**: Plate path ``/home/user/plate::experiment`` contains ``::`` but is NOT a step scope.

Correct Detection Pattern
--------------------------

Use ``_pending_preview_keys`` to detect global/plate-level changes:

.. code-block:: python

    # From pipeline_editor.py
    def _handle_full_preview_refresh(self, live_context_before, live_context_after):
        # If _pending_preview_keys contains all step indices, this is a global/plate-level change
        all_step_indices = set(range(len(self.pipeline_steps)))

        if self._pending_preview_keys == all_step_indices:
            logger.info("Global/plate-level change - checking ALL steps for unsaved changes")
            # Check all steps for unsaved changes
            for step_index in all_step_indices:
                has_unsaved = check_step_has_unsaved_changes(...)
                self._update_step_unsaved_marker(step_index, has_unsaved)
        else:
            # Step-specific change - only check steps in _pending_preview_keys
            for step_index in self._pending_preview_keys:
                has_unsaved = check_step_has_unsaved_changes(...)
                self._update_step_unsaved_marker(step_index, has_unsaved)

**How _pending_preview_keys is Set**:

The ``_resolve_scope_targets()`` method determines which steps should be updated:

.. code-block:: python

    # From pipeline_editor.py
    def _resolve_scope_targets(self, manager_scope_id, emitted_values):
        # If this is a GlobalPipelineConfig or PipelineConfig change, return ALL_ITEMS_SCOPE
        if manager_scope_id == self.ALL_ITEMS_SCOPE:
            # Return all step indices for incremental update
            return set(range(len(self.pipeline_steps)))

        # Otherwise, extract step index from scope_id
        if '::' in manager_scope_id:
            step_token = manager_scope_id.split('::')[-1]
            step_index = self._extract_step_index_from_token(step_token)
            return {step_index}

        return set()

**Key Insight**: ``_resolve_scope_targets()`` returns the set of step indices that should be updated. When it returns all step indices, ``_pending_preview_keys`` is set to all indices, signaling a global/plate-level change.

Field Path Format and Fast-Path Optimization
=============================================

The ``_last_emitted_values`` dictionary tracks the last emitted value for each field in a form manager, enabling fast-path optimization for unsaved changes detection.

Field Path Format
-----------------

Field paths use dot notation to represent the full path from root object to leaf field:

.. code-block:: python

    # Format: "<RootObjectType>.<config_attr>.<nested_field>..."

    # Examples:
    "GlobalPipelineConfig.step_materialization_config.well_filter"
    "PipelineConfig.step_well_filter_config.enabled"
    "FunctionStep.napari_streaming_config.enabled"

**Structure**:

1. **Root object type**: ``GlobalPipelineConfig``, ``PipelineConfig``, ``FunctionStep``
2. **Config attribute**: ``step_materialization_config``, ``napari_streaming_config``, etc.
3. **Nested fields**: ``well_filter``, ``enabled``, etc.

Fast-Path Optimization
----------------------

Before doing expensive full resolution comparison, check if any form manager has emitted changes for fields relevant to this object:

.. code-block:: python

    def check_step_has_unsaved_changes(step, live_context_snapshot):
        """Check if step has unsaved changes."""

        # FAST PATH: Check if any form manager has relevant changes
        has_any_relevant_changes = False
        for manager in ParameterFormManager._active_form_managers:
            if not manager._last_emitted_values:
                continue

            # Check each emitted field path
            for field_path, field_value in manager._last_emitted_values.items():
                # Extract config attribute from field path
                # "GlobalPipelineConfig.step_materialization_config.well_filter" → "step_materialization_config"
                path_parts = field_path.split('.')
                if len(path_parts) >= 2:
                    config_attr_from_path = path_parts[1]

                    # Check if this config attribute exists on the step
                    if hasattr(step, config_attr_from_path):
                        has_any_relevant_changes = True
                        break

        if not has_any_relevant_changes:
            # No form manager has emitted changes for this step's configs
            # Skip expensive full resolution comparison
            return False

        # SLOW PATH: Do full resolution comparison
        return _check_all_configs_for_unsaved_changes(step, live_context_snapshot)

**Performance Impact**: Fast-path can skip 90%+ of full resolution comparisons when no relevant changes exist.

Scope Matching in Fast-Path
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The fast-path must also check scope matching to prevent step windows from affecting other steps:

.. code-block:: python

    # Build expected step scope for this step
    expected_step_scope = None
    if scope_filter and step_token:
        expected_step_scope = f"{scope_filter}::{step_token}"

    for manager in ParameterFormManager._active_form_managers:
        # If manager has a step-specific scope (contains ::step_), only consider it
        # relevant if it matches the current step's expected scope
        if manager.scope_id and '::step_' in manager.scope_id:
            if expected_step_scope and manager.scope_id != expected_step_scope:
                # Different step - skip this manager
                continue

        # Check for relevant changes...

This prevents a step window from triggering unsaved changes detection for OTHER steps in the same plate.

Cleanup on Window Close
~~~~~~~~~~~~~~~~~~~~~~~~

When a window closes, its ``_last_emitted_values`` must be cleared to prevent stale fast-path matches:

.. code-block:: python

    def unregister_from_cross_window_updates(self):
        if self in type(self)._active_form_managers:
            # ... capture snapshots ...

            # Remove from registry
            self._active_form_managers.remove(self)

            # CRITICAL: Clear _last_emitted_values
            self._last_emitted_values.clear()

            # ... emit signals ...

Without this cleanup, other windows would see stale field paths and incorrectly think there are unsaved changes.

