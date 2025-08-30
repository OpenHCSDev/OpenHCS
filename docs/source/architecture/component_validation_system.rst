Component Validation System
===========================

Overview
--------

Traditional validation systems hardcode assumptions about component names and valid combinations. The GenericValidator eliminates these assumptions by deriving validation rules from component configuration metadata.

.. code-block:: python

   class GenericValidator(Generic[T]):
       def __init__(self, config: ComponentConfiguration[T]):
           self.config = config

       def validate_step(self, variable_components: List[T], group_by: Optional[T]) -> ValidationResult:
           # Core constraint: group_by ∉ variable_components
           self.config.validate_combination(variable_components, group_by)

This enables the same validation logic to work with any component configuration - wells, timepoints, batches - without code changes.

Core Constraint Validation
-------------------------

The system validates the fundamental processing constraint that prevents ambiguous behavior.

.. code-block:: python

   def validate_step(self, variable_components: List[T], group_by: Optional[T],
                    func_pattern: Any, step_name: str) -> ValidationResult:
       """Validate step configuration using generic rules."""
       try:
           # Core constraint: group_by ∉ variable_components
           self.config.validate_combination(variable_components, group_by)

           # Dict pattern requirements
           if isinstance(func_pattern, dict) and not group_by:
               return ValidationResult(
                   is_valid=False,
                   error_message=f"Dict pattern requires group_by in step '{step_name}'"
               )

           return ValidationResult(is_valid=True)
       except ValueError as e:
           return ValidationResult(is_valid=False, error_message=str(e))

The constraint ensures that the component used for function routing is not also used for data grouping.

Integration with Compilation
----------------------------

The validation system integrates with the OpenHCS compilation pipeline to provide early constraint checking.

.. code-block:: python

   # In FuncStepContractValidator.validate_funcstep()
   config = get_openhcs_config()
   validator = GenericValidator(config)

   # Check for constraint violation: group_by ∈ variable_components
   if step.group_by and step.group_by.value in [vc.value for vc in step.variable_components]:
       # Auto-resolve constraint violation by nullifying group_by
       logger.warning(f"Step '{step_name}': Auto-resolved group_by conflict")
       step.group_by = None

This prevents invalid configurations from reaching the execution phase.

Extension Examples
------------------

Custom Validation Rules
~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   class ExtendedValidator(GenericValidator):
       """Extended validator with custom constraints."""

       def validate_step(self, variable_components, group_by, func_pattern, step_name):
           """Extended validation with custom constraints."""
           # Run base validation
           result = super().validate_step(variable_components, group_by, func_pattern, step_name)
           if not result.is_valid:
               return result

           # Add custom validation logic
           if self._has_custom_constraint_violation(variable_components, group_by):
               return ValidationResult(
                   is_valid=False,
                   error_message=f"Custom constraint violation in step '{step_name}'"
               )

           return ValidationResult(is_valid=True)

**Common Gotchas**:

- Don't use ``GroupBy.NONE`` with dict patterns - validation will fail
- Component keys are cached on initialization - call ``clear_component_cache()`` if input directory changes
- Dict pattern keys must match actual component values, not enum names




