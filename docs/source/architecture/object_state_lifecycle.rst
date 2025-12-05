ObjectState Lifecycle and Contracts
===================================

Purpose
-------

ObjectState holds the UI MODEL extracted from an object without any PyQt dependencies. ParameterFormManager (PFM) is the VIEW that reads/writes ObjectState; ObjectState persists beyond a single window.

Responsibilities
----------------

- Store parameters, types, defaults extracted by ``UnifiedParameterAnalyzer``
- Track user edits (``_user_set_fields``) and resets (``reset_fields``)
- Manage nested states (one ObjectState per nested dataclass field)
- Provide scoped discovery via ``ObjectStateRegistry`` for live context
- Provide saved baselines for save/cancel flows (``mark_saved`` / ``restore_saved``)

Lifecycle
---------

.. list-table::
   :header-rows: 1
   :widths: 30 70

   * - Owner
     - Creation/Destruction
   * - PipelineEditor (steps)
     - Create when step added; unregister when step removed
   * - FunctionListWidget (functions)
     - Create when function added; unregister when function removed
   * - Config windows (global/pipeline)
     - Create on window open (or during orchestrator init); persist for lifetime of orchestrator/app
   * - Nested dataclasses
     - Created recursively inside parent ObjectState; inherit parent scope/context

Baseline and Cancel Behavior
----------------------------

.. note::
   ``saved_parameters`` is captured from the backing object (raw ``object.__getattribute__`` for dataclasses). If the backing object carries constructor defaults (e.g., lazy configs with class defaults), ``restore_saved()`` will reapply those concrete values unless the caller updates the baseline after normalization.

Key methods:

- ``mark_saved()``: capture current values (and resolved snapshot), clear dirty/reset flags. Call after successful save.
- ``restore_saved()``: revert ``parameters`` to ``saved_parameters`` and restore edit/reset flags. Call on cancel.
- ``is_dirty()``: true once a parameter is mutated after the last ``mark_saved()``.

Lazy Config Defaults
--------------------

- Lazy dataclasses created with constructor defaults may carry concrete values (e.g., ``FijiStreamingConfig.port=5565``).
- If the backing object has not been explicitly set, normalize to ``None`` in ``ObjectState.parameters`` before opening the PFM, then call ``mark_saved()`` to update the baseline so cancel restores placeholders instead of class defaults.

Live Context Integration
------------------------

- ``ObjectStateRegistry`` stores all states keyed by ``scope_id``.
- ``LiveContextService.collect()`` walks the registry, calling ``get_user_modified_values()``/``get_user_modified_overlay()`` on each state (and nested states).
- Consumers merge ancestor scopes via ``merge_ancestor_values(scopes, my_scope)`` and build context stacks for placeholder resolution.

Contracts for Callers
---------------------

1. Create/register ObjectState at lifecycle ownership points (step added, function added, config window opened).
2. Pass ObjectState into PFM; do not mutate ``parameters`` directly from the UI—use dispatcher/state updates.
3. On save: call ``mark_saved()`` (or rely on ``BaseFormDialog.accept``).
4. On cancel: call ``restore_saved()`` before closing (``BaseFormDialog.reject`` does this).
5. When removing the owning object, unregister from ``ObjectStateRegistry`` to keep live context accurate.
