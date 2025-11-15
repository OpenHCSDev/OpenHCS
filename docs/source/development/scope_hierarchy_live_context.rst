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

Scope IDs create a hierarchy that matches the orchestrator → step → function relationship:

.. code-block:: python

    # Orchestrator scope (unique per plate/pipeline)
    orchestrator_scope = f"orchestrator_{id(orchestrator)}"
    
    # Step scope (inherits orchestrator scope)
    step_scope = f"{orchestrator_scope}.step_{step_index}"
    
    # Function scope (inherits step scope)
    function_scope = f"{step_scope}.function"

Editors with matching scope prefixes share live context. Editors with different scopes are isolated.

Scope Hierarchy Architecture
=============================

Three-Level Hierarchy
---------------------

.. code-block:: python

    # Level 1: Orchestrator
    scope_id = "orchestrator_140234567890"
    # Shared by: All steps and functions in this orchestrator
    
    # Level 2: Step
    scope_id = "orchestrator_140234567890.step_0"
    # Shared by: Step editor and its function editor
    
    # Level 3: Function
    scope_id = "orchestrator_140234567890.step_0.function"
    # Shared by: Function editor only

**Key insight**: Step and function editors share the same scope prefix, enabling them to see each other's live parameters while remaining isolated from other orchestrators.

Scope Matching Logic
--------------------

.. code-block:: python

    def _collect_live_context_from_other_windows(self):
        """Collect live parameter values from other windows with matching scope."""
        live_context = {}
        
        for other_manager in ParameterFormManager._active_form_managers:
            # Skip self
            if other_manager is self:
                continue
            
            # CRITICAL: Only collect from managers with matching scope prefix
            if not self._scopes_match(other_manager.scope_id):
                continue
            
            # Collect parameters from matching scope
            live_context.update(other_manager.get_current_parameters())
        
        return live_context
    
    def _scopes_match(self, other_scope_id):
        """Check if scopes share common prefix."""
        # Same orchestrator: "orchestrator_123" matches "orchestrator_123.step_0"
        # Different orchestrator: "orchestrator_123" does NOT match "orchestrator_456"
        return (self.scope_id.startswith(other_scope_id) or 
                other_scope_id.startswith(self.scope_id))

This ensures step and function editors see each other's parameters (same orchestrator) while remaining isolated from other orchestrators.

Implementation Patterns
=======================

Dual Editor Window
------------------

Step and function editors share scope to enable parameter synchronization:

.. code-block:: python

    class DualEditorWindow(QMainWindow):
        def __init__(self, orchestrator, step_index):
            # Create orchestrator-specific scope
            orchestrator_scope = f"orchestrator_{id(orchestrator)}"
            step_scope = f"{orchestrator_scope}.step_{step_index}"
            
            # Step editor uses step scope
            self.step_editor = StepParameterEditor(
                step=step,
                scope_id=step_scope
            )
            
            # Function editor uses same step scope (not function scope!)
            # This enables it to see step parameters for placeholder resolution
            self.function_editor = FunctionListEditor(
                step=step,
                scope_id=step_scope  # Same as step editor
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

Config windows use global scope to share context across all orchestrators:

.. code-block:: python

    class ConfigWindow(BaseFormDialog):
        def __init__(self, config_class):
            # Global scope: shared by all config windows
            scope_id = f"config_{config_class.__name__}"
            
            self.form_manager = ParameterFormManager(
                object_instance=config_instance,
                scope_id=scope_id
            )

**Why global scope?** GlobalPipelineConfig changes should be visible to all orchestrators.

Scope Isolation Examples
=========================

Isolated Orchestrators
-----------------------

.. code-block:: python

    # Orchestrator A: Plate 1
    orchestrator_A = PipelineOrchestrator(plate_path="plate1")
    scope_A = f"orchestrator_{id(orchestrator_A)}"  # "orchestrator_140234567890"
    
    # Orchestrator B: Plate 2
    orchestrator_B = PipelineOrchestrator(plate_path="plate2")
    scope_B = f"orchestrator_{id(orchestrator_B)}"  # "orchestrator_140234568901"
    
    # Step editors are isolated
    step_editor_A = StepParameterEditor(step_A, scope_id=f"{scope_A}.step_0")
    step_editor_B = StepParameterEditor(step_B, scope_id=f"{scope_B}.step_0")
    
    # step_editor_A does NOT see step_editor_B's parameters
    # Different scope prefixes: "orchestrator_140234567890" vs "orchestrator_140234568901"

Shared Step/Function Context
-----------------------------

.. code-block:: python

    # Same orchestrator, same step
    orchestrator_scope = "orchestrator_140234567890"
    step_scope = f"{orchestrator_scope}.step_0"
    
    # Step editor
    step_editor = StepParameterEditor(step, scope_id=step_scope)
    
    # Function editor (same scope!)
    function_editor = FunctionListEditor(step, scope_id=step_scope)
    
    # function_editor DOES see step_editor's parameters
    # Same scope prefix: "orchestrator_140234567890.step_0"

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

**Why use object ID for orchestrator scope?**

Ensures unique scope even if multiple orchestrators process the same plate. Object ID is guaranteed unique per instance.

**Why share scope between step and function editors?**

Function editor needs step parameters for placeholder resolution (e.g., ``group_by`` selector). Sharing scope enables this without manual parameter passing.

**Why not use orchestrator reference directly?**

Scope IDs are strings, enabling serialization and comparison without object reference issues.

Common Gotchas
==============

- **Don't use global scope for orchestrator-specific editors**: Each orchestrator must have unique scope to prevent parameter bleed-through
- **Step and function editors must share scope**: Function editor needs step parameters for placeholder resolution
- **Scope IDs are immutable**: Don't change scope_id after form manager creation
- **Scope matching is prefix-based**: "orchestrator_123" matches "orchestrator_123.step_0" but not "orchestrator_1234"

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
    # Should have same prefix

**Fix**: Ensure both editors use same scope_id

Symptom: Cross-Orchestrator Bleed-Through
------------------------------------------

**Cause**: Multiple orchestrators sharing same scope prefix

**Diagnosis**:

.. code-block:: python

    # Check orchestrator scopes
    logger.debug(f"Orchestrator A scope: {scope_A}")
    logger.debug(f"Orchestrator B scope: {scope_B}")
    # Should be different

**Fix**: Use unique object IDs for each orchestrator scope


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

