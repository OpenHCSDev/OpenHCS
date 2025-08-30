Multiprocessing Coordination System
===================================

Overview
--------

Traditional OpenHCS multiprocessing was hardcoded to use wells as the parallelization axis. The MultiprocessingCoordinator eliminates this assumption by providing axis-agnostic task coordination that can use any component for parallelization.

.. code-block:: python

   class MultiprocessingCoordinator(Generic[T]):
       def __init__(self, config: ComponentConfiguration[T]):
           self.config = config
           self.axis = config.multiprocessing_axis

       def create_tasks(self, orchestrator, axis_filter=None) -> Dict[str, Task[T]]:
           """Create tasks for multiprocessing axis values."""
           axis_values = orchestrator.get_component_keys(self.axis, axis_filter)
           return {value: Task(axis_value=value, context=orchestrator.create_context(value))
                   for value in axis_values}

This enables optimal parallelization strategies - wells, timepoints, batches, or any other component - without code changes.

Task Coordination
-----------------

The coordinator creates and executes tasks for any multiprocessing axis.

Task Creation
~~~~~~~~~~~~

.. code-block:: python

   def create_tasks(self, orchestrator, axis_filter=None) -> Dict[str, Task[T]]:
       """Create tasks for multiprocessing axis values."""
       # Get axis values from orchestrator using the multiprocessing axis component directly
       axis_values = orchestrator.get_component_keys(self.axis, axis_filter)

       if not axis_values:
           logger.warning(f"No {self.axis.value} values found for multiprocessing")
           return {}

       # Create tasks
       tasks = {}
       for axis_value in axis_values:
           context = orchestrator.create_context(axis_value)
           tasks[axis_value] = Task(axis_value=axis_value, context=context)

       return tasks

Tasks are created dynamically based on the available component values for the configured multiprocessing axis.

Task Execution
~~~~~~~~~~~~~

.. code-block:: python

   def execute_tasks(self, tasks: Dict[str, Task[T]], pipeline_definition: List[Any],
                    executor, processor_func) -> Dict[str, Any]:
       """Execute tasks using the provided executor."""
       if not tasks:
           logger.warning("No tasks to execute")
           return {}

       logger.info(f"Executing {len(tasks)} tasks using {type(executor).__name__}")

       # Submit tasks to executor
       future_to_axis = {}
       for axis_value, task in tasks.items():
           future = executor.submit(processor_func, task.context, pipeline_definition)
           future_to_axis[future] = axis_value

       # Collect results
       results = {}
       for future in concurrent.futures.as_completed(future_to_axis):
           axis_value = future_to_axis[future]
           try:
               result = future.result()
               results[axis_value] = result
               logger.debug(f"Task completed for {self.axis.value}: {axis_value}")
           except Exception as e:
               logger.error(f"Task failed for {self.axis.value} {axis_value}: {e}")
               results[axis_value] = None

       return results

The coordinator handles task submission, execution monitoring, and result collection generically.

Configuration Examples
---------------------

Different parallelization strategies through component configuration.

.. code-block:: python

   # Well-based parallelization (traditional)
   well_config = ComponentConfigurationFactory.create_configuration(
       StandardComponents,
       multiprocessing_axis=StandardComponents.WELL,
       default_variable=[StandardComponents.SITE],
       default_group_by=StandardComponents.CHANNEL
   )

   # Timepoint-based parallelization (temporal analysis)
   temporal_config = ComponentConfigurationFactory.create_configuration(
       TimeSeriesComponents,
       multiprocessing_axis=TimeSeriesComponents.TIMEPOINT,
       default_variable=[TimeSeriesComponents.WELL, TimeSeriesComponents.SITE],
       default_group_by=TimeSeriesComponents.CHANNEL
   )

**Common Gotchas**:

- Component keys are cached on initialization - call ``clear_component_cache()`` if input directory changes
- Task contexts must be serializable for ProcessPoolExecutor
- Axis values are discovered from actual data, not enum definitions
