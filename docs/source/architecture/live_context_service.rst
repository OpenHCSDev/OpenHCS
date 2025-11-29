Live Context Service
====================

**Centralized cross-window coordination with token-based cache invalidation.**

*Module: openhcs.pyqt_gui.widgets.shared.services.live_context_service*

The Cross-Window Update Problem
-------------------------------

OpenHCS allows users to edit configuration at multiple levels simultaneously. A user might
have the global pipeline configuration window open, a plate-specific configuration window,
and a step editor dialog—all at the same time. When they change a value in the global
config, placeholder text in the step editor should update to reflect the new inherited value.

The naive solution is to wire signals between every pair of windows that might affect each
other. But this creates N×N complexity: every window needs to know about every other window,
and adding a new window type requires updating all existing windows. This quickly becomes
unmaintainable.

The Solution: Broadcast with Token Invalidation
-----------------------------------------------

``LiveContextService`` solves this with a broadcast pattern. Instead of windows talking
directly to each other, they all register with a central service. When any value changes
anywhere, the service increments a token and notifies all listeners. Listeners don't need
to know *what* changed—they just know *something* changed and they should refresh.

This dramatically simplifies the architecture:

1. **Token-based invalidation** - A single counter that increments on any change
2. **Simple listener callbacks** - No field path matching, just "something changed"
3. **WeakSet registry** - Automatic cleanup when managers are garbage collected
4. **Cache with token validation** - Avoid recomputing live context when unchanged

The token is the key insight. Listeners can cache their computed state along with the
token value. On the next notification, they compare tokens—if unchanged, they can skip
the expensive refresh. This makes the broadcast pattern efficient despite its simplicity.

.. code-block:: text

    ┌─────────────────────┐     ┌────────────────────────┐
    │  FormManager A      │────▶│  LiveContextService    │
    │  (GlobalConfig)     │     │                        │
    └─────────────────────┘     │  - _active_managers    │
                                │  - _change_callbacks   │
    ┌─────────────────────┐     │  - _token_counter      │
    │  FormManager B      │────▶│                        │
    │  (StepConfig)       │     └────────────────────────┘
    └─────────────────────┘              │
                                         ▼
                            ┌────────────────────────┐
                            │  Listeners             │
                            │  (PlateManager, etc.)  │
                            └────────────────────────┘

API Reference
-------------

The service is implemented as class methods on ``LiveContextService``, making it
effectively a singleton. All state is stored as class attributes, ensuring there's
only one registry across the entire application.

Token Management
~~~~~~~~~~~~~~~~

The token is a simple integer counter. Comparing tokens is O(1), making cache
validation essentially free:

.. code-block:: python

    from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService

    # Get current token (for cache validation)
    token = LiveContextService.get_token()

    # Increment token (invalidates all caches, notifies listeners)
    LiveContextService.increment_token()

Manager Registry
~~~~~~~~~~~~~~~~

Form managers register themselves when they're created and are automatically
removed when garbage collected (via WeakSet). This prevents memory leaks and
ensures the registry stays current:

.. code-block:: python

    # Register a form manager for cross-window updates
    LiveContextService.register(manager)

    # Unregister (also called automatically via WeakSet)
    LiveContextService.unregister(manager)

    # Get all active managers (read-only)
    managers = LiveContextService.get_active_managers()

Change Listeners
~~~~~~~~~~~~~~~~

Listeners receive no arguments—they just know something changed. This keeps the
interface simple and avoids the complexity of field-level subscriptions:

.. code-block:: python

    def on_context_changed():
        """Called when any form value changes."""
        snapshot = LiveContextService.collect()
        # Use snapshot.values to update placeholders, etc.

    # Connect listener
    LiveContextService.connect_listener(on_context_changed)

    # Disconnect listener
    LiveContextService.disconnect_listener(on_context_changed)

Live Context Collection
~~~~~~~~~~~~~~~~~~~~~~~

When a listener needs to update its display (e.g., refresh placeholder text), it calls
``collect()`` to get a snapshot of all values from all registered managers. The snapshot
includes the token, so the listener can cache both the snapshot and the token for
efficient cache validation on subsequent notifications.

The filtering options allow listeners to focus on relevant context. A step editor
only cares about values from ancestor scopes (global and plate-level), not sibling
steps. The ``for_type`` parameter uses the configuration type hierarchy to collect
only from managers whose config type is an ancestor of the specified type:

.. code-block:: python

    # Collect live context from all managers
    snapshot = LiveContextService.collect()

    # Snapshot structure:
    # - snapshot.token: int (cache validation token)
    # - snapshot.values: Dict[type, Dict[str, Any]]
    # - snapshot.scoped_values: Dict[str, Dict[type, Dict[str, Any]]]

    # Filter by scope
    snapshot = LiveContextService.collect(scope_filter="plate_path::0")

    # Filter by type hierarchy (only collect from ancestors)
    snapshot = LiveContextService.collect(for_type=NapariStreamingConfig)

Global Refresh
~~~~~~~~~~~~~~

Sometimes you need to force all windows to refresh—for example, after loading a new
pipeline. ``trigger_global_refresh()`` calls each manager's refresh method:

.. code-block:: python

    # Trigger cross-window refresh for all active managers
    LiveContextService.trigger_global_refresh()

LiveContextSnapshot
-------------------

The collection result is an immutable dataclass. Immutability ensures that cached
snapshots can't be accidentally modified, which would break cache validation logic:

.. code-block:: python

    @dataclass(frozen=True)
    class LiveContextSnapshot:
        token: int  # For cache validation
        values: Dict[type, Dict[str, Any]]  # Type -> field values
        scoped_values: Dict[str, Dict[type, Dict[str, Any]]]  # Scope -> Type -> values

Handling Qt Object Lifecycle
----------------------------

PyQt has a subtle but critical issue: Python objects can hold references to Qt widgets
that have been deleted on the C++ side. Calling methods on these "zombie" objects
raises ``RuntimeError: wrapped C/C++ object has been deleted``.

The service handles this by checking ``sip.isdeleted()`` before invoking callbacks.
Callbacks from deleted objects are silently skipped and removed from the registry:

.. code-block:: python

    def _notify_change(cls) -> None:
        dead_callbacks = []
        for callback in cls._change_callbacks:
            # Check if bound method's object has been deleted (PyQt C++ side)
            callback_self = getattr(callback, '__self__', None)
            if callback_self is not None:
                from PyQt6 import sip
                if sip.isdeleted(callback_self):
                    dead_callbacks.append(callback)
                    continue
            callback()
        
        # Clean up dead callbacks
        for cb in dead_callbacks:
            cls._change_callbacks.remove(cb)

This prevents ``RuntimeError: wrapped C/C++ object has been deleted`` errors.

Usage Pattern
-------------

Typical usage in a widget:

.. code-block:: python

    class PlateManagerWidget(QWidget):
        def __init__(self):
            super().__init__()
            # Connect as listener
            LiveContextService.connect_listener(self._on_context_changed)
        
        def _on_context_changed(self):
            """Debounced callback - refresh placeholders."""
            snapshot = LiveContextService.collect(
                scope_filter=self.current_plate_path,
                for_type=type(self.current_step)
            )
            self._refresh_placeholders_with_context(snapshot.values)
        
        def closeEvent(self, event):
            # Disconnect on close
            LiveContextService.disconnect_listener(self._on_context_changed)
            super().closeEvent(event)

See Also
--------

- :doc:`parameter_form_service_architecture` - Form managers that register with this service
- :doc:`cross_window_update_optimization` - Optimization patterns for cross-window updates
- :doc:`context_system` - Lazy config context and resolution
- :doc:`field_change_dispatcher` - Dispatches field changes that trigger token increment

