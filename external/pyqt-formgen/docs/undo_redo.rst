Undo / Redo
===========

The undo/redo system in ``ObjectStateRegistry`` is a git-like DAG of snapshots, not just a
linear stack. Snapshots capture *all* ObjectStates at a point in time.

Data model
----------
- ``_snapshots: Dict[str, Snapshot]``: all snapshots (UUID → Snapshot)
- ``_timelines: Dict[str, Timeline]``: named branches; each has a ``head_id``
- ``_current_timeline`` / ``_current_head``: current branch and cursor for time travel
- Snapshots store ``all_states`` (scope_id → StateSnapshot) plus parent links for branching

Core operations
---------------
- ``record_snapshot(label, triggering_scope=None)`` (internal): create a new snapshot, prune unreachable
- ``undo()``: move to parent snapshot in the current branch
- ``redo()``: move to child if unique; otherwise stay
- ``time_travel_to_snapshot(id)`` / ``time_travel_to(index)``: jump arbitrarily in history
- ``create_branch(name)`` / ``switch_branch(name)``: multi-branch history
- ``atomic(label)`` context manager: batch multiple changes into one undo step
- ``export_history_to_dict()`` / ``import_history_from_dict()``: serialize/restore history
- ``save_history_to_file(path)`` / ``load_history_from_file(path)``: JSON persistence

Behavior
--------
- Recording from a non-head position creates a new branch (preserves old future as an auto-branch).
- Undo/redo/time travel rewires the live registry: registers/unregisters ObjectStates to match the snapshot and restores saved/live resolved values.
- History size is bounded by ``_max_history_size``; unreachable snapshots are pruned.

Example
-------

.. code-block:: python

   from objectstate import ObjectStateRegistry

   # Single undo step for a grouped change
   with ObjectStateRegistry.atomic("add item"):
       ObjectStateRegistry.register(item_state)
       parent_state.update_parameter("items", new_items)

   # Undo/redo
   ObjectStateRegistry.undo()
   ObjectStateRegistry.redo()

   # Persist history
   history = ObjectStateRegistry.export_history_to_dict()
   ObjectStateRegistry.import_history_from_dict(history)
