Placeholder Inheritance Debugging Guide
=======================================

**Systematic debugging approaches for the OpenHCS placeholder inheritance system.**

*Status: STABLE*
*Module: openhcs.pyqt_gui.widgets.shared.parameter_form_manager*

Overview
--------

The placeholder inheritance system enables configuration fields to inherit values from parent configurations through lazy dataclass resolution. When users click reset buttons on inherited fields, the system must exclude the target field from context building to allow proper inheritance resolution. This guide provides systematic debugging approaches for inheritance chain failures.

The core challenge is that form managers must build context from current UI state while selectively excluding fields during reset operations. The system involves complex interactions between nested form managers, context building, widget value reading, and lazy dataclass resolution.

Understanding the inheritance flow is essential for debugging: child fields with ``None`` values trigger lazy resolution, which checks thread-local context for parent field values, then generates placeholder text showing inherited values like "Pipeline default: {inherited_value}".

System Architecture
-------------------

Core Components
~~~~~~~~~~~~~~~

**Form Managers**: UI components that manage individual configuration sections. Each form manager has a ``field_id`` that identifies its configuration section and manages widgets for that section's parameters.

**Context Building**: Process of creating configuration context for inheritance resolution by collecting current values from all form managers and combining widget state with parameter values.

**Exclusion Logic**: Mechanism to exclude specific fields during reset operations, implemented in the widget reading loop of :py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._build_context_from_current_form_values`.

**Lazy Resolution**: On-demand value resolution that checks thread-local context for parent field values and falls back to defaults when inheritance chains are available.

Field Naming Architecture
~~~~~~~~~~~~~~~~~~~~~~~~~

The system handles two distinct field naming patterns that require different context building approaches:

**Nested Form Managers** have ``field_id`` values like ``nested_well_filter_config`` but correspond to context fields named ``well_filter_config`` (without the ``nested_`` prefix). Widget names follow the pattern ``nested_well_filter_config.well_filter``.

**Non-Nested Form Managers** use ``field_id`` of ``config`` for top-level configuration and context fields also named ``config``. Widget names follow the pattern ``config.num_workers``.

The critical fix for nested form managers strips the ``nested_`` prefix during context field lookup to ensure ``hasattr()`` checks succeed and the widget reading loop executes properly.

Context Building Process
------------------------

Normal Context Building Flow
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._build_context_from_current_form_values` orchestrates context building by iterating through all form managers to collect current values. For each form manager, it reads widget values and combines them with parameter values, then builds context with all current form state for lazy dataclass resolution.

The method first checks ``hasattr(current_context, context_field_name)`` to verify the form's dataclass exists in context. If found, it enters the widget reading loop where current widget values are collected and combined with existing parameter values.

Context Building During Reset
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Reset operations call context building with an ``exclude_field`` parameter to exclude the target field from widget value reading. The exclusion logic in the widget reading loop checks ``exclude_field and param_name == exclude_field`` and skips reading the widget value for excluded fields.

This allows the context to be built without the field being reset, enabling lazy resolution to inherit from parent configurations instead of using the current (soon-to-be-reset) value.

The reset flow: user clicks reset → :py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.reset_parameter` calls context building with exclusion → context built without target field → lazy resolution inherits from parent → placeholder text updated with inherited value.

Debugging Patterns
------------------

Essential Debug Output
~~~~~~~~~~~~~~~~~~~~~~

Add these debug prints to trace the inheritance system:

.. code-block:: python

   # In _build_context_from_current_form_values()
   print(f"🔍 CONTEXT BUILD DEBUG: {self.field_id} building context with exclude_field='{exclude_field}'")
   print(f"🔍 CONTEXT DEBUG: form_field_name='{form_field_name}', context_field_name='{context_field_name}', hasattr={hasattr(current_context, context_field_name)}")

   # In widget reading loop
   print(f"🔍 EXCLUSION DEBUG: Checking param_name='{param_name}' vs exclude_field='{exclude_field}'")
   if exclude_field and param_name == exclude_field:
       print(f"🔍 WIDGET DEBUG: {self.field_id}.{param_name} EXCLUDED from context (reset)")

   # In lazy resolution code
   print(f"🔍 LAZY RESOLUTION DEBUG: Resolving {dataclass_name}.{field_name}")
   print(f"🔍 LAZY RESOLUTION DEBUG: Context has {parent_field} = '{parent_value}'")

Successful Operation Patterns
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Successful Context Building**:

.. code-block:: text

   🔍 CONTEXT DEBUG: form_field_name='nested_well_filter_config', context_field_name='well_filter_config', hasattr=True
   🔍 CONTEXT DEBUG: current_dataclass_instance=WellFilterConfig(...)

**Successful Exclusion**:

.. code-block:: text

   🔍 EXCLUSION DEBUG: Checking param_name='well_filter' vs exclude_field='well_filter'
   🔍 WIDGET DEBUG: nested_step_materialization_config.well_filter EXCLUDED from context (reset)

**Successful Inheritance**:

.. code-block:: text

   🔍 LAZY RESOLUTION DEBUG: Resolving StepMaterializationConfig.well_filter
   🔍 LAZY RESOLUTION DEBUG: Context has step_well_filter_config.well_filter = '789'
   🔍 OVERRIDE CHECK: StepMaterializationConfig.well_filter default='None' has_override=False
   🔍 OVERRIDE CHECK: StepWellFilterConfig.well_filter default='1' has_override=True

Common Failure Patterns
-----------------------

Context Building Failures
~~~~~~~~~~~~~~~~~~~~~~~~~

**Field Naming Mismatch**:

.. code-block:: text

   🔍 CONTEXT DEBUG: form_field_name='nested_well_filter_config', context_field_name='nested_well_filter_config', hasattr=False

This indicates the field naming fix is not applied. The ``context_field_name`` should strip the ``nested_`` prefix to match the actual context field name.

**Investigation Steps**: 1. Verify the prefix stripping logic is applied 2. Check if ``field_id`` follows expected naming patterns 3. Confirm context contains the expected field names

Exclusion Logic Failures
~~~~~~~~~~~~~~~~~~~~~~~~

**Exclusion Not Working**:

.. code-block:: text

   🔍 WIDGET DEBUG: nested_step_materialization_config.well_filter widget value = 'some_value'

If widget values are being read for the excluded field, exclusion is not working.

**Investigation Steps**: 1. Verify context building reaches the widget reading loop 2. Check if ``exclude_field`` parameter is passed correctly 3. Confirm ``param_name`` matches ``exclude_field`` exactly

Inheritance Resolution Failures
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Wrong Inheritance Chain**:

.. code-block:: text

   🔍 LAZY RESOLUTION DEBUG: Context has wrong_parent_field = 'unexpected_value'

This indicates context contains wrong parent values or inheritance logic errors.

**Investigation Steps**: 1. Trace lazy resolution debug output to verify inheritance path 2. Check if context building collected correct parent values 3. Verify inheritance decorators are properly configured

Testing and Validation
----------------------

Automated Testing
~~~~~~~~~~~~~~~~~

Use :py:func:`tests.pyqt_gui.functional.test_reset_placeholder_simplified.TestResetPlaceholderInheritance.test_comprehensive_inheritance_chains` to validate inheritance chains. This test verifies multiple inheritance levels, reset functionality, and placeholder text accuracy through UI automation.

Manual Testing Protocol
~~~~~~~~~~~~~~~~~~~~~~~

1. **Set Parent Field**: Set parent field to concrete value (e.g., ``step_well_filter_config.well_filter = "789"``)
2. **Verify Child Inheritance**: Verify child field shows inherited placeholder (e.g., ``step_materialization_config.well_filter`` shows "Pipeline default: 789")
3. **Test Reset Functionality**: Reset child field and verify placeholder updates correctly
4. **Test Parent Reset**: Reset parent field and verify child field updates to new inherited value
5. **Validate Chain Propagation**: Test multiple levels of inheritance to ensure chains propagate correctly

Known Issues and Limitations
----------------------------

Non-Nested Field Reset Bug
~~~~~~~~~~~~~~~~~~~~~~~~~~

Non-nested fields don't reset placeholder values properly when a config is saved and reopened. When reopened, resetting a concrete non-nested field causes the placeholder to show the concrete value instead of the inherited value.

This appears related to how the configuration cache system interacts with reset functionality for non-nested fields, where concrete values become part of cached context and reset logic may not properly exclude them.

Architecture Improvement Needed
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The current use of ``nested_`` string prefixes is a code smell that creates fragile field naming dependencies. The system should migrate to using complete field paths like ``config.step_materialization_config.well_filter`` with context field names that match form manager field paths exactly, eliminating string manipulation and prefix stripping logic.
