Atomic Operations
=================

The ``atomic()`` context manager enables multiple ObjectState changes to be recorded as a single undo step. This is critical for operations that logically belong together.

Problem: Multiple Snapshots for One Action
------------------------------------------

Without atomicity, each ObjectState modification records its own snapshot:

.. code-block:: python

   # Adding a pipeline step creates 3 separate snapshots:
   ObjectStateRegistry.register(step_state)    # Snapshot 1: "register step"
   pipeline_state.update_parameter(...)        # Snapshot 2: "edit step_scope_ids"  
   ObjectStateRegistry.register(func_state)    # Snapshot 3: "register function"

   # User must undo 3 times to revert "add step" action!

Solution: atomic() Context Manager
----------------------------------

Wrap related operations in ``atomic()`` to coalesce them:

.. code-block:: python

   from objectstate import ObjectStateRegistry

   with ObjectStateRegistry.atomic("add step"):
       ObjectStateRegistry.register(step_state)
       pipeline_state.update_parameter("step_scope_ids", new_ids)
       ObjectStateRegistry.register(func_state)
   # Single snapshot "add step" recorded here

   # User undoes once to revert entire "add step" action

How It Works
------------

The atomic mechanism uses depth counting to support nesting:

.. code-block:: text

   atomic("outer")          _atomic_depth = 1
   ├── register(...)        snapshot deferred
   ├── atomic("inner")      _atomic_depth = 2
   │   └── update(...)      snapshot deferred
   └── (inner exits)        _atomic_depth = 1, still deferred
   (outer exits)            _atomic_depth = 0, record "outer" snapshot

**Key behaviors:**

1. ``_atomic_depth`` tracks nesting level (0 = not in atomic block)
2. While ``_atomic_depth > 0``, all ``record_snapshot()`` calls are deferred
3. Only the outermost block's label is used for the final snapshot
4. The snapshot is recorded when ``_atomic_depth`` returns to 0

API Reference
-------------

.. py:method:: ObjectStateRegistry.atomic(label: str)
   :classmethod:

   Context manager for atomic operations.

   :param label: Human-readable label for the coalesced snapshot
   :type label: str

   **Example:**

   .. code-block:: python

      with ObjectStateRegistry.atomic("delete step"):
          # Unregister function ObjectStates
          ObjectStateRegistry.unregister_scope_and_descendants(func_scope)
          # Update pipeline's step list
          pipeline_state.update_parameter("step_scope_ids", remaining_ids)
          # Unregister step ObjectState
          ObjectStateRegistry.unregister(step_state)
      # Single "delete step" snapshot

Nested Atomic Blocks
--------------------

Atomic blocks can be nested safely:

.. code-block:: python

   with ObjectStateRegistry.atomic("batch import"):
       for step_data in steps_to_import:
           with ObjectStateRegistry.atomic("add step"):
               # Each step add is its own logical unit,
               # but all are coalesced under "batch import"
               create_step(step_data)
   # Only one "batch import" snapshot recorded

The innermost label is ignored - only the outermost label is used.

Real-World Use Cases
--------------------

Code Mode Apply
~~~~~~~~~~~~~~~

When applying code-mode edits, multiple operations occur:

.. code-block:: python

   def _apply_edited_pattern(self, new_pattern):
       with ObjectStateRegistry.atomic("code edit"):
           # Recreates function panes (registers new ObjectStates)
           self._populate_function_list(new_pattern)
           # Updates step's func parameter
           self.function_pattern_changed.emit(new_pattern)

Step Reordering
~~~~~~~~~~~~~~~

Drag-and-drop reordering involves multiple state updates:

.. code-block:: python

   def _reorder_steps(self, from_idx, to_idx):
       with ObjectStateRegistry.atomic("reorder steps"):
           # Update step indices
           for i, step_state in enumerate(step_states):
               step_state.update_parameter("index", new_indices[i])
           # Update pipeline's ordering
           pipeline_state.update_parameter("step_order", new_order)

Best Practices
--------------

1. **Use descriptive labels**: Labels appear in time-travel UI and debugging

   .. code-block:: python

      # Good
      with ObjectStateRegistry.atomic("add threshold step"):
      
      # Bad  
      with ObjectStateRegistry.atomic("operation"):

2. **Keep atomic blocks small**: Only wrap logically related operations

3. **Avoid side effects in atomic blocks**: Don't perform I/O or network calls

4. **Always use context manager**: Never manually manipulate ``_atomic_depth``

Thread Safety
-------------

The atomic mechanism is **not** thread-safe. ``_atomic_depth`` is a class variable shared across all threads. If your application uses multiple threads modifying ObjectStates, ensure atomic blocks are not entered concurrently from different threads.

For thread-safe alternatives, consider:

- Using per-thread ObjectState registries
- Serializing all ObjectState modifications through a single thread
- Using locks around atomic blocks

