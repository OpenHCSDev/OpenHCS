Sibling Inheritance System
==========================

**Real-time cross-field inheritance within the same configuration context.**

*Status: STABLE*

*Module: openhcs.pyqt_gui.widgets.shared.parameter_form_manager*

Overview
--------

Sibling inheritance enables nested configurations at the same hierarchical level to inherit field values from each other. When a user edits ``step_well_filter_config.well_filter`` in the step editor, sibling configs like ``step_materialization_config`` and ``napari_streaming_config`` immediately show the inherited value in their placeholders.

This is distinct from parent-child inheritance (Step → Pipeline → Global). Sibling inheritance operates **horizontally** within a single context level, while parent-child inheritance operates **vertically** across context levels.

.. code-block:: python

   # Example: FunctionStep has multiple nested configs at the same level
   step = FunctionStep(
       name="normalize",
       step_well_filter_config=LazyStepWellFilterConfig(well_filter="A1"),
       step_materialization_config=LazyStepMaterializationConfig(well_filter=None),  # Inherits "A1"
       napari_streaming_config=LazyNapariStreamingConfig(well_filter=None),  # Inherits "A1"
   )

All three configs inherit from ``WellFilterConfig`` via their MRO, so they share the ``well_filter`` field. When ``step_well_filter_config.well_filter`` is set to ``"A1"``, the other configs resolve their ``None`` values by looking up the MRO chain and finding ``step_well_filter_config`` in the parent overlay.

Architecture
------------

Sibling inheritance uses the **parent overlay pattern**: when refreshing placeholders for a nested config, the form manager creates a temporary overlay instance of the parent object (e.g., ``FunctionStep``) containing only user-modified values from sibling configs. This overlay is added to the context stack so the resolver can find sibling values.

Key Components
~~~~~~~~~~~~~~

1. **Parent Overlay Creation** (:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._build_context_stack`)
   
   Creates temporary parent instance with user-modified values from all nested configs except the current one.

2. **User-Modified Value Extraction** (:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.get_user_modified_values`)
   
   Extracts only non-None raw values from nested dataclasses, preserving lazy resolution for unmodified fields.

3. **Tuple Reconstruction** (:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._create_overlay_instance`)
   
   Reconstructs nested dataclass instances from tuple format ``(type, dict)`` before instantiation.

4. **Scope-Aware Resolution** (:py:mod:`openhcs.config_framework.dual_axis_resolver`)
   
   Filters configs by scope specificity to prevent cross-contamination between different orchestrators.

See Also
--------

- :doc:`configuration_framework` - Dual-axis resolution and MRO-based inheritance
- :doc:`context_system` - Context stacking and scope management
- :doc:`parameter_form_lifecycle` - Form lifecycle and placeholder updates
- :doc:`scope_hierarchy_live_context` - Scope specificity and filtering

Implementation Details
----------------------

Parent Overlay Pattern
~~~~~~~~~~~~~~~~~~~~~~

When a nested config form (e.g., ``step_materialization_config``) needs to resolve placeholders, it:

1. Gets the parent manager (step editor)
2. Calls ``parent_manager.get_user_modified_values()`` to extract user-modified values
3. Excludes the current nested config from the parent values (to prevent self-reference)
4. Creates a parent overlay instance (``FunctionStep``) with the filtered values
5. Adds the parent overlay to the context stack with the parent's scope
6. Resolves placeholders within this context

This makes sibling configs visible to the resolver via the parent overlay.

.. code-block:: python

   # Simplified example from _build_context_stack()
   if parent_manager:
       # Get user-modified values from parent (includes all nested configs)
       parent_values = parent_manager.get_user_modified_values()
       
       # Exclude current nested config to prevent self-reference
       filtered_values = {k: v for k, v in parent_values.items() 
                         if k != self.field_id}
       
       # Create parent overlay with sibling values
       parent_overlay = FunctionStep(**filtered_values)
       
       # Add to context stack with parent's scope
       with config_context(parent_overlay, context_provider=parent_scope):
           # Now resolver can find sibling configs in parent_overlay
           resolved_value = lazy_config.well_filter  # Finds "A1" from sibling

User-Modified Value Extraction
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.get_user_modified_values` extracts only values that were explicitly set by the user, preserving lazy resolution for unmodified fields.

For nested dataclasses, it returns tuples ``(type, dict)`` containing only non-None raw values:

.. code-block:: python

   # Example return value
   {
       'name': 'normalize',
       'enabled': True,
       'step_well_filter_config': (LazyStepWellFilterConfig, {'well_filter': 'A1'}),
       'step_materialization_config': (LazyStepMaterializationConfig, {'backend': 'DISK'}),
   }

This tuple format preserves only user-modified fields inside nested configs, avoiding pollution of the context with default values.

**Critical Design Decision**: This method works for **all objects** (lazy dataclasses, scoped objects like ``FunctionStep``, etc.), not just lazy dataclasses. The early return for non-lazy-dataclass objects was removed in commit ``9d21d494`` to fix sibling inheritance in the step editor.

Tuple Reconstruction
~~~~~~~~~~~~~~~~~~~~

:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._create_overlay_instance` handles the tuple format by reconstructing nested dataclasses before instantiation:

.. code-block:: python

   # From _create_overlay_instance()
   reconstructed_values = {}
   for key, value in values_dict.items():
       if isinstance(value, tuple) and len(value) == 2:
           dataclass_type, field_dict = value
           if dataclasses.is_dataclass(dataclass_type):
               # Reconstruct nested dataclass
               reconstructed_values[key] = dataclass_type(**field_dict)
           else:
               # Skip non-dataclass tuples (e.g., functions)
               pass
       else:
           reconstructed_values[key] = value
   
   return overlay_type(**reconstructed_values)

The dataclass check prevents errors when encountering non-dataclass tuples (e.g., ``func`` parameter in ``FunctionStep``).

Scope-Aware Resolution
~~~~~~~~~~~~~~~~~~~~~~

The parent overlay must be added to the context stack with the **parent's scope** to ensure correct specificity filtering:

.. code-block:: python

   # From _build_context_stack()
   parent_scopes = {type(parent_overlay).__name__: parent_manager.scope_id}
   context_provider = ScopeProvider(parent_manager.scope_id)
   
   with config_context(parent_overlay, 
                      context_provider=context_provider,
                      config_scopes=parent_scopes):
       # Parent overlay has correct scope specificity
       pass

Without this, the parent overlay defaults to ``PipelineConfig`` scope (specificity=1) instead of ``FunctionStep`` scope (specificity=2), causing the resolver to skip sibling configs.

See :doc:`scope_hierarchy_live_context` for details on scope specificity.

Scoped Objects vs Lazy Dataclasses
-----------------------------------

The sibling inheritance system works with two types of parent objects:

**Lazy Dataclasses** (``GlobalPipelineConfig``, ``PipelineConfig``)
   - Inherit from ``GlobalConfigBase``
   - Have ``_resolve_field_value()`` method for lazy resolution
   - Are dataclasses with ``@dataclass`` decorator
   - Example: ``PipelineConfig`` with nested ``path_planning_config``

**Scoped Objects** (``FunctionStep``)
   - Inherit from ``ScopedObject`` ABC
   - Have ``build_scope_id()`` method for scope identification
   - Are NOT dataclasses (regular classes with attributes)
   - Have lazy config attributes (e.g., ``step_well_filter_config: LazyStepWellFilterConfig``)
   - Example: ``FunctionStep`` with nested ``step_well_filter_config``, ``step_materialization_config``

The key difference is that ``FunctionStep`` is a **scoped object with lazy config attributes**, not a lazy dataclass itself. This means:

- ``hasattr(FunctionStep, '_resolve_field_value')`` → ``False``
- ``hasattr(FunctionStep, 'build_scope_id')`` → ``True``
- ``dataclasses.is_dataclass(FunctionStep)`` → ``False``
- ``isinstance(FunctionStep, ScopedObject)`` → ``True``

The sibling inheritance system must work for **both** types, which is why :py:meth:`get_user_modified_values` cannot have an early return for non-lazy-dataclass objects.

Common Pitfalls and Debugging
------------------------------

Bug: Early Return in get_user_modified_values
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Symptom**: Sibling inheritance works in pipeline config editor but not in step editor.

**Root Cause**: Early return in :py:meth:`get_user_modified_values` for non-lazy-dataclass objects:

.. code-block:: python

   # WRONG - breaks sibling inheritance for FunctionStep
   def get_user_modified_values(self):
       if not hasattr(self.config, '_resolve_field_value'):
           return self.get_current_values()  # Returns lazy instances, not raw values!
       # ... extract raw values from nested dataclasses

This breaks sibling inheritance for ``FunctionStep`` because:

1. ``FunctionStep`` is not a lazy dataclass (no ``_resolve_field_value``)
2. Early return calls ``get_current_values()`` which returns lazy dataclass instances
3. Parent overlay is created with lazy instances instead of raw values
4. Resolver cannot access raw values from lazy instances in parent overlay
5. Sibling configs show "(none)" instead of inherited values

**Fix**: Remove early return and extract raw values for all objects:

.. code-block:: python

   # CORRECT - works for all objects
   def get_user_modified_values(self):
       current_values = self.get_current_values()

       # Extract raw values from nested dataclasses for ALL objects
       for field_name, value in current_values.items():
           if dataclasses.is_dataclass(value):
               # Extract raw values and return as tuple
               raw_values = {f.name: object.__getattribute__(value, f.name)
                           for f in dataclasses.fields(value)}
               user_modified[field_name] = (type(value), raw_values)

**Fixed in**: Commit ``9d21d494`` (2025-11-25)

Bug: Missing Scope in Parent Overlay
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Symptom**: Parent overlay is created but resolver skips sibling configs.

**Root Cause**: Parent overlay added to context stack without scope:

.. code-block:: python

   # WRONG - parent overlay defaults to PipelineConfig scope
   parent_overlay = FunctionStep(**parent_values)
   with config_context(parent_overlay):  # No context_provider or config_scopes!
       # Resolver sees parent_overlay with specificity=1 (PipelineConfig)
       # Current config has specificity=2 (FunctionStep)
       # Resolver skips parent_overlay due to specificity mismatch

**Fix**: Pass parent's scope when adding parent overlay:

.. code-block:: python

   # CORRECT - parent overlay has correct scope
   parent_scopes = {type(parent_overlay).__name__: parent_manager.scope_id}
   context_provider = ScopeProvider(parent_manager.scope_id)

   with config_context(parent_overlay,
                      context_provider=context_provider,
                      config_scopes=parent_scopes):
       # Resolver sees parent_overlay with specificity=2 (FunctionStep)
       # Matches current config specificity
       # Sibling configs are found!

**Fixed in**: Commit ``9d21d494`` (2025-11-25)

Bug: Reconstructing Non-Dataclass Tuples
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Symptom**: Error when opening step editor: "Reconstructing func from tuple".

**Root Cause**: Attempting to reconstruct functions as dataclasses:

.. code-block:: python

   # WRONG - tries to reconstruct all tuples
   for key, value in parent_values.items():
       if isinstance(value, tuple) and len(value) == 2:
           dataclass_type, field_dict = value
           reconstructed[key] = dataclass_type(**field_dict)  # Fails for functions!

**Fix**: Check if type is a dataclass before reconstructing:

.. code-block:: python

   # CORRECT - only reconstructs dataclasses
   for key, value in parent_values.items():
       if isinstance(value, tuple) and len(value) == 2:
           dataclass_type, field_dict = value
           if dataclasses.is_dataclass(dataclass_type):
               reconstructed[key] = dataclass_type(**field_dict)
           else:
               # Skip non-dataclass tuples (e.g., func parameter)
               pass

**Fixed in**: Commit ``9d21d494`` (2025-11-25)

Bug: GlobalPipelineConfig Assigned Plate-Level Scope
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Symptom**: Sibling inheritance works in step editor but NOT in pipeline config window. When step editor is closed, pipeline config window suddenly works correctly.

**Root Cause**: Variable shadowing in ``collect_live_context()`` caused ``GlobalPipelineConfig`` to be incorrectly assigned a plate-level scope:

.. code-block:: python

   # In collect_live_context():
   base_type = get_base_type_for_lazy(obj_type)  # Returns GlobalPipelineConfig for PipelineConfig

   # Later, when mapping base types:
   # WRONG - shadows base_type with MRO parent (NOT GlobalPipelineConfig)
   base_type = manager.dataclass_type.__mro__[1]  # Returns ScopedObject, not GlobalPipelineConfig!
   if base_type and is_global_config_type(base_type):  # Returns False!
       # Skipped - global config not detected

This breaks sibling inheritance because:

1. ``get_base_type_for_lazy(PipelineConfig)`` correctly returns ``GlobalPipelineConfig``
2. But line 636 shadows ``base_type`` with MRO parent (e.g., ``ScopedObject``)
3. ``is_global_config_type(ScopedObject)`` returns ``False``
4. ``GlobalPipelineConfig`` gets assigned plate-level scope instead of ``None``
5. All configs are skipped by scope filter (``scope_specificity=1 > current_specificity=0``)
6. Sibling configs show "(none)" instead of inherited values

**Log Evidence**:

.. code-block:: text

   🔍 BUILD SCOPES: GlobalPipelineConfig -> /path/to/plate (base of PipelineConfig)
   🔍 SCOPE FILTER: Skipping GlobalPipelineConfig (scope_specificity=1 > current_specificity=0) for field enabled

**Fix**: Remove the shadowing line and use the original ``base_type`` from ``get_base_type_for_lazy()``:

.. code-block:: python

   # CORRECT - use base_type from get_base_type_for_lazy (line 583)
   if base_name:
       from openhcs.config_framework.lazy_factory import is_global_config_type
       if base_type and is_global_config_type(base_type) and canonical_scope is not None:
           logger.info(f"Skipping {base_name} -> {canonical_scope} (global config must always have scope=None)")
       # ... rest of logic

**Fixed in**: Commit ``289e1d52`` (2025-11-25)

Bug: Missing _is_global_config Marker
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Symptom**: ``is_global_config_type(GlobalPipelineConfig)`` returns ``False`` even though ``GlobalPipelineConfig`` is decorated with ``@auto_create_decorator``.

**Root Cause**: The ``@auto_create_decorator`` decorator never set the ``_is_global_config`` marker that ``is_global_config_type()`` checks for:

.. code-block:: python

   # is_global_config_type() checks for the marker
   def is_global_config_type(config_type: Type) -> bool:
       return hasattr(config_type, '_is_global_config') and config_type._is_global_config

   # But auto_create_decorator never set it!
   def auto_create_decorator(global_config_class):
       # ... validation and decorator creation ...
       # MISSING: global_config_class._is_global_config = True
       return global_config_class

**Fix**: Add the marker in ``auto_create_decorator``:

.. code-block:: python

   def auto_create_decorator(global_config_class):
       # CRITICAL: Mark the class for is_global_config_type() checks
       global_config_class._is_global_config = True
       # ... rest of decorator logic ...
       return global_config_class

**Fixed in**: Commit ``9c8b45f4`` (2025-11-25)

Debugging Checklist
~~~~~~~~~~~~~~~~~~~

When sibling inheritance is not working:

1. **Check parent overlay creation**

   Search logs for ``SIBLING INHERITANCE: {field_id} getting parent values``

   - If missing: Parent overlay is not being created (check conditions in ``_build_context_stack``)
   - If present: Check what values are being extracted

2. **Check user-modified value extraction**

   Search logs for ``get_user_modified_values: {field_name} → tuple``

   - Should see tuples for nested dataclasses with user-modified fields
   - Should NOT see lazy dataclass instances

3. **Check parent overlay scope**

   Search logs for ``PARENT OVERLAY: Adding parent overlay with scope={scope_id}``

   - Scope should match parent manager's scope_id
   - Should NOT be ``None`` for step editor

4. **Check scope specificity**

   Search logs for ``PARENT OVERLAY SCOPE CHECK: {field_id} - parent_specificity={N}, current_specificity={M}``

   - Parent and current specificity should match (both 2 for step editor)
   - ``compatible=True`` means scopes are compatible

5. **Check resolver behavior**

   Search logs for ``STEP 2: Checking MRO class {ConfigType}`` and ``STEP 2: No match``

   - Should find parent overlay in available_configs
   - Should NOT skip due to scope mismatch

Code Navigation Guide
---------------------

To understand and debug sibling inheritance, navigate the code in this order:

1. **Start**: :py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._on_nested_parameter_changed`

   Entry point when user edits a nested config field. Triggers refresh of sibling managers.

2. **Extract**: :py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.get_user_modified_values`

   Extracts user-modified values from parent manager. Returns tuples for nested dataclasses.

3. **Build**: :py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._build_context_stack`

   Creates parent overlay and adds it to context stack with correct scope.

4. **Reconstruct**: :py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._create_overlay_instance`

   Reconstructs nested dataclasses from tuple format before instantiation.

5. **Resolve**: :py:mod:`openhcs.config_framework.dual_axis_resolver`

   Walks MRO and finds configs in available_configs, filtering by scope specificity.

6. **Display**: :py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._apply_placeholder_text_with_flash_detection`

   Shows resolved value in placeholder text.

Mental Model
------------

Think of sibling inheritance as a **horizontal lookup** within a single parent object:

.. code-block:: text

   FunctionStep (parent)
   ├── step_well_filter_config (sibling 1) ← User sets well_filter="A1"
   ├── step_materialization_config (sibling 2) ← Inherits well_filter="A1"
   └── napari_streaming_config (sibling 3) ← Inherits well_filter="A1"

When refreshing placeholders for ``step_materialization_config``:

1. Create temporary ``FunctionStep`` with only ``step_well_filter_config`` (exclude self)
2. Add this overlay to context stack
3. Resolve ``step_materialization_config.well_filter`` → walks MRO → finds ``WellFilterConfig`` → looks in available_configs → finds ``step_well_filter_config`` in parent overlay → returns ``"A1"``

This is different from **vertical lookup** (parent-child inheritance):

.. code-block:: text

   GlobalPipelineConfig (grandparent)
   └── PipelineConfig (parent)
       └── FunctionStep (child)
           └── step_well_filter_config

When resolving ``step_well_filter_config.well_filter``:

1. Walk MRO: ``LazyStepWellFilterConfig`` → ``LazyWellFilterConfig`` → ...
2. For each MRO class, check available_configs (contains GlobalPipelineConfig, PipelineConfig, FunctionStep)
3. Return first concrete value found

The key insight is that **sibling inheritance uses the same MRO-based resolution as parent-child inheritance**, but operates on a temporary parent overlay instead of the actual context stack.

Implementation References
-------------------------

**Core Files**:

- ``openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`` - Form manager with sibling inheritance logic
- ``openhcs/config_framework/dual_axis_resolver.py`` - MRO-based resolution with scope filtering
- ``openhcs/config_framework/context_manager.py`` - Context stacking and scope management
- ``openhcs/core/steps/abstract.py`` - AbstractStep inherits from ScopedObject
- ``openhcs/core/steps/function_step.py`` - FunctionStep with lazy config attributes

**Related Documentation**:

- :doc:`configuration_framework` - Dual-axis resolution and MRO-based inheritance
- :doc:`context_system` - Context stacking and ScopedObject interface
- :doc:`parameter_form_lifecycle` - Form lifecycle and placeholder updates
- :doc:`scope_hierarchy_live_context` - Scope specificity and filtering
- :doc:`dynamic_dataclass_factory` - Lazy dataclass generation and resolution

