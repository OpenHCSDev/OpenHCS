====================================
Scope Filtering: Dual Use Cases
====================================

*Module: openhcs.config_framework.dual_axis_resolver, openhcs.pyqt_gui.widgets.shared.parameter_form_manager*  
*Status: STABLE*

---

Overview
========

The scope filtering system has **two distinct use cases** that require **different filtering semantics**:

1. **Values Collection** - Gathering form values for preview/comparison (uses bidirectional matching)
2. **Scopes Dict Building** - Telling the resolver where each config "lives" (uses strict filtering)

Using the wrong filter for the wrong use case causes **scope contamination bugs** where sibling inheritance fails.

The Problem
===========

When a step editor is open (scope = ``plate::step_6``) and you open the PipelineConfig window (scope = ``plate``), the system needs to:

1. **Collect step-level VALUES** for preview purposes (pipeline editor needs to see unsaved step changes)
2. **Exclude step-level SCOPES** from the scopes dict (prevents step scopes from polluting plate-level resolution)

If both use the same filter, you get scope contamination:

.. code-block:: python

    # BUG: Using bidirectional filter for BOTH use cases
    
    # Values collection (CORRECT - needs bidirectional)
    for manager in active_managers:
        if is_scope_visible(manager.scope_id, "plate"):  # ✅ Includes step managers
            scoped_values["plate::step_6"][StepWellFilterConfig] = {well_filter: 333}
    
    # Scopes dict building (WRONG - needs strict)
    for manager in active_managers:
        if is_scope_visible(manager.scope_id, "plate"):  # ❌ Includes step managers
            scopes["StepWellFilterConfig"] = "plate::step_6"  # POLLUTION!
    
    # Result: When PipelineConfig tries to resolve step_materialization_config.well_filter
    # via sibling inheritance, it looks up StepWellFilterConfig scope → sees "plate::step_6"
    # (specificity 2), but PipelineConfig is at plate-level (specificity 1).
    # Resolver says: "That config is more specific than me, can't see it" → returns None

The Solution
============

Use **different filters** for the two use cases:

1. **Values Collection**: ``is_scope_visible()`` - bidirectional matching
2. **Scopes Dict Building**: ``is_scope_at_or_above()`` - strict filtering

Bidirectional Matching (Values Collection)
-------------------------------------------

``is_scope_visible(manager_scope, filter_scope)`` returns ``True`` if scopes are in the same hierarchy (parent, child, or same).

.. code-block:: python

    from openhcs.config_framework.dual_axis_resolver import is_scope_visible
    
    # Examples
    is_scope_visible(None, "plate")              # True - global visible to all
    is_scope_visible("plate", "plate")           # True - exact match
    is_scope_visible("plate", "plate::step")     # True - manager is parent of filter
    is_scope_visible("plate::step", "plate")     # True - manager is child of filter (same hierarchy)
    is_scope_visible("plate1::step", "plate2")   # False - different hierarchy

**Use Case**: Collecting values from all managers in the same hierarchy for preview purposes.

When the pipeline editor (plate-level) collects live context, it NEEDS to see step-level values to detect unsaved changes and update preview labels.

Strict Filtering (Scopes Dict Building)
----------------------------------------

``is_scope_at_or_above(manager_scope, filter_scope)`` returns ``True`` only if manager is at same level or LESS specific than filter.

.. code-block:: python

    from openhcs.config_framework.dual_axis_resolver import is_scope_at_or_above
    
    # Examples
    is_scope_at_or_above(None, "plate")           # True - global visible to all
    is_scope_at_or_above("plate", "plate")        # True - exact match
    is_scope_at_or_above("plate", "plate::step")  # True - manager is parent of filter
    is_scope_at_or_above("plate::step", "plate")  # False - manager is MORE specific than filter

**Use Case**: Building the scopes dict that tells the resolver where each config type "lives".

When the PipelineConfig window builds its scopes dict, it should NOT include step-level managers, because that would tell the resolver "StepWellFilterConfig lives at step-level", which breaks sibling inheritance at plate-level.

Implementation
==============

Values Collection (parameter_form_manager.py:502)
--------------------------------------------------

.. code-block:: python

    @classmethod
    def collect_live_context(cls, scope_filter=None) -> LiveContextSnapshot:
        """Collect live values from all active form managers."""
        
        for manager in cls._active_form_managers:
            # Use bidirectional matching - step values ARE collected
            if not cls._is_scope_visible_static(manager.scope_id, scope_filter):
                continue
            
            # Add to scoped_values
            scoped_values[manager.scope_id][obj_type] = manager.get_user_modified_values()

Scopes Dict Building (parameter_form_manager.py:577)
-----------------------------------------------------

.. code-block:: python

    def add_manager_to_scopes(manager, is_nested=False):
        """Helper to add a manager and its nested managers to scopes_dict."""
        from openhcs.config_framework.dual_axis_resolver import is_scope_at_or_above
        
        if manager.scope_id is not None:
            # Use strict filtering - step scopes are NOT added
            if not is_scope_at_or_above(manager.scope_id, scope_filter_str):
                return
        
        # Add to scopes dict
        scopes_dict[config_type_name] = manager.scope_id

Why This Matters
================

The scopes dict is used by the resolver to determine which scope a config type belongs to. This affects sibling inheritance:

.. code-block:: python

    # When resolving step_materialization_config.well_filter via sibling inheritance:
    
    # 1. Resolver looks up StepWellFilterConfig in scopes dict
    scopes = {"StepWellFilterConfig": "plate::step_6"}  # From step editor
    
    # 2. Resolver checks if this scope is visible from current scope (plate-level)
    current_scope = "plate"  # PipelineConfig window
    config_scope = scopes["StepWellFilterConfig"]  # "plate::step_6"
    
    # 3. Resolver uses scope specificity to filter
    if get_scope_specificity(config_scope) > get_scope_specificity(current_scope):
        return None  # Config is more specific, not visible
    
    # Result: Sibling inheritance fails because step-level scope polluted the scopes dict

With the fix, step-level managers don't add their scopes when building for plate-level:

.. code-block:: python

    # Scopes dict when PipelineConfig builds it (step editor is open)
    scopes = {"StepWellFilterConfig": "plate"}  # From PipelineConfig window, NOT step editor
    
    # Now sibling inheritance works:
    config_scope = scopes["StepWellFilterConfig"]  # "plate"
    current_scope = "plate"  # PipelineConfig window
    # Same specificity → visible → sibling inheritance succeeds

See Also
========

- :doc:`sibling_inheritance_system` - Parent overlay pattern and sibling inheritance
- :doc:`../development/scope_hierarchy_live_context` - Scope hierarchy and LiveContextSnapshot
- :doc:`configuration_framework` - Dual-axis resolution and MRO-based inheritance

