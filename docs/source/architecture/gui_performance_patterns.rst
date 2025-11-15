GUI Performance Patterns
========================

OpenHCS GUI implements several performance optimization patterns to maintain responsiveness when editing complex pipelines with many steps and cross-window dependencies.

Cross-Window Preview System
---------------------------

The cross-window preview system enables real-time preview updates in list widgets (like pipeline editor step lists) when users edit configuration values in other windows (like step editor dialogs).

**Problem**

Traditional approach: When a user edits a step's configuration in a dialog, the pipeline editor must refresh its entire step list to show updated preview text. With 20+ steps, this causes:

- Redundant context collection (gathering live values from all open forms)
- Redundant context resolution (building context stacks 20+ times)
- Full widget list rebuilds (destroying and recreating all list items)
- Measured latency: 60ms per keystroke

**Solution Architecture**

The cross-window preview system uses three components:

1. **Token-based caching**: Global token counter invalidates all caches when any value changes
2. **Scope-based routing**: Changes routed to specific items via hierarchical scope IDs
3. **Incremental updates**: Only affected items refresh, not entire lists

**CrossWindowPreviewMixin**

Reusable mixin for widgets that consume cross-window updates:

.. code-block:: python

   from openhcs.pyqt_gui.widgets.mixins import CrossWindowPreviewMixin
   
   class PipelineEditorWidget(QWidget, CrossWindowPreviewMixin):
       def __init__(self):
           super().__init__()
           self._init_cross_window_preview_mixin()
           
           # Register as external listener
           ParameterFormManager.register_external_listener(
               self,
               value_changed_handler=self._on_cross_window_context_changed,
               refresh_handler=None  # Optional
           )
       
       def _on_cross_window_context_changed(self, field_path, new_value, 
                                           editing_object, context_object):
           self.handle_cross_window_preview_change(
               field_path, new_value, editing_object, context_object
           )

**Scope IDs**

Hierarchical scope identifiers enable targeted updates:

.. code-block:: python

   # Format: "plate_path::step_token"
   scope_id = f"{orchestrator.plate_path}::{step._pipeline_scope_token}"
   
   # Example: "/path/to/plate::step_001"
   # Enables routing changes to specific step in specific plate

**Scope Mapping**

Map scope IDs to item keys for incremental updates:

.. code-block:: python

   def _build_scope_index_map(self) -> Dict[str, int]:
       """Map scope IDs to step indices."""
       scope_map = {}
       for idx, step in enumerate(self.pipeline_steps):
           token = getattr(step, '_pipeline_scope_token', None)
           if token:
               scope_id = f"{self.current_plate}::{token}"
               scope_map[scope_id] = idx
       return scope_map

**Implementing Mixin Hooks**

Subclasses must implement four hooks:

.. code-block:: python

   def _should_process_preview_field(self, field_path, new_value, 
                                     editing_object, context_object) -> bool:
       """Return True if field affects preview display."""
       # Check if field is in STEP_PREVIEW_FIELDS
       # Check if field is pipeline/global config (affects all)
       
   def _extract_scope_id_for_preview(self, editing_object, 
                                     context_object) -> Optional[str]:
       """Extract scope ID from editing object."""
       # Return step-specific scope for FunctionStep
       # Return "PIPELINE_CONFIG_CHANGE" for PipelineConfig
       # Return "GLOBAL_CONFIG_CHANGE" for GlobalPipelineConfig
       
   def _process_pending_preview_updates(self) -> None:
       """Apply incremental updates for pending keys."""
       # Collect live context ONCE
       # Refresh only items in self._pending_preview_keys
       
   def _handle_full_preview_refresh(self) -> None:
       """Fallback when incremental updates not possible."""
       # Call update_step_list() or equivalent

**Performance Impact**

- Context collection: 20+ calls → 1 call (cached via token)
- Context resolution: 20+ operations → 1 operation (incremental update)
- Widget updates: Full rebuild → Text-only update on existing widgets
- Measured latency: 60ms → 1ms per keystroke

Live Context Collection
-----------------------

``ParameterFormManager.collect_live_context()`` provides cached access to live form values:

.. code-block:: python

   from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import (
       ParameterFormManager
   )
   
   # Collect live context with scope filtering
   snapshot = ParameterFormManager.collect_live_context(
       scope_filter=self.current_plate
   )
   
   # Use snapshot for resolution
   for step_index in indices_to_refresh:
       display_text = self.format_item_for_display(
           step, 
           live_context_snapshot=snapshot
       )

**Caching Behavior**

- Token-based: Snapshot cached until token changes
- Scope-filtered: Separate cache entries per scope filter
- Automatic invalidation: Token increments on any form value change
- Type aliasing: Maps lazy/base types for flexible matching

**Token Lifecycle**

1. User edits form field → ``_emit_cross_window_context_changed()``
2. Token incremented → ``_live_context_token_counter += 1``
3. All caches invalidated globally
4. Next ``collect_live_context()`` call recomputes snapshot
5. Subsequent calls with same token return cached snapshot

Async Operations in GUI
----------------------

Heavy operations (file I/O, network requests, blocking waits) must run in background threads to prevent UI freezes.

**Problem**

Blocking operations on the UI thread cause:

- Frozen interface (no repaints, no event processing)
- Unresponsive buttons and menus
- Poor user experience (appears crashed)
- Cannot cancel long-running operations

**Solution: Background Workers**

Move heavy operations to daemon threads:

.. code-block:: python

   import threading

   def on_user_action(self):
       """UI thread: Lightweight checks only."""
       # Check preconditions (cheap)
       if not self.is_valid():
           return

       # Spawn background worker
       threading.Thread(
           target=self._heavy_operation_async,
           args=(param1, param2),
           daemon=True
       ).start()

   def _heavy_operation_async(self, param1, param2):
       """Background thread: Heavy operations."""
       try:
           # Load from disk (blocking I/O)
           data = load_from_file(path)

           # Wait for external service (blocking)
           if not service.wait_for_ready(timeout=15.0):
               raise RuntimeError("Service not ready")

           # Process data (CPU-intensive)
           result = process_data(data)

           # Update UI via signal (thread-safe)
           self._status_update_signal.emit(f"Completed: {result}")

       except Exception as e:
           # Show error dialog on UI thread
           QTimer.singleShot(0, lambda: QMessageBox.warning(
               self, "Error", str(e)
           ))

**Thread-Safe UI Updates**

Never call UI methods directly from background threads. Use Qt signals or QTimer:

.. code-block:: python

   class MyWidget(QWidget):
       # Define signal for cross-thread communication
       _status_update_signal = pyqtSignal(str)

       def __init__(self):
           super().__init__()
           # Connect signal to UI update method
           self._status_update_signal.connect(self._update_status_label)

       def _update_status_label(self, text: str):
           """UI thread: Safe to update widgets."""
           self.status_label.setText(text)

       def _background_worker(self):
           """Background thread: Emit signal instead of direct update."""
           # ❌ WRONG: self.status_label.setText("Loading...")
           # ✅ CORRECT: Emit signal
           self._status_update_signal.emit("Loading...")

**QTimer for One-Shot UI Operations**

Use ``QTimer.singleShot()`` to schedule UI operations from background threads:

.. code-block:: python

   def _background_worker(self):
       """Background thread."""
       try:
           result = expensive_operation()
       except Exception as e:
           # Schedule dialog on UI thread
           QTimer.singleShot(0, lambda: QMessageBox.warning(
               self, "Error", f"Operation failed: {e}"
           ))
           return

       # Schedule success dialog on UI thread
       QTimer.singleShot(0, lambda: QMessageBox.information(
           self, "Success", f"Result: {result}"
       ))

**Daemon Threads**

Always use ``daemon=True`` for background workers:

- Daemon threads automatically terminate when app exits
- Non-daemon threads prevent app from closing
- User doesn't have to wait for background operations to finish

**Example: Async ROI Streaming**

From ``image_browser.py``:

.. code-block:: python

   def _stream_roi_file(self, roi_zip_path: Path):
       """UI thread: Lightweight checks only."""
       # Check which viewers are enabled (cheap)
       napari_enabled = self.napari_enable_checkbox.isChecked()
       fiji_enabled = self.fiji_enable_checkbox.isChecked()

       if not napari_enabled and not fiji_enabled:
           QMessageBox.information(self, "No Viewers", "Enable at least one viewer")
           return

       # Resolve configs on UI thread (cheap)
       napari_config = self._resolve_napari_config()
       fiji_config = self._resolve_fiji_config()

       # Spawn background workers
       if napari_enabled:
           threading.Thread(
               target=self._stream_single_roi_async,
               args=(napari_viewer, roi_zip_path, napari_config),
               daemon=True
           ).start()

       if fiji_enabled:
           threading.Thread(
               target=self._stream_single_roi_async,
               args=(fiji_viewer, roi_zip_path, fiji_config),
               daemon=True
           ).start()

   def _stream_single_roi_async(self, viewer, roi_zip_path, config):
       """Background thread: Heavy operations."""
       try:
           # Load ROIs from disk (blocking I/O)
           self._status_update_signal.emit(f"Loading {roi_zip_path.name}...")
           rois = load_rois_from_zip(roi_zip_path)

           # Wait for viewer (blocking, up to 15s)
           if not viewer.wait_for_ready(timeout=15.0):
               raise RuntimeError("Viewer not ready")

           # Stream to viewer (blocking I/O)
           self._status_update_signal.emit(f"Streaming to viewer...")
           filemanager.save(rois, roi_zip_path, backend, **metadata)

           # Success message on UI thread
           msg = f"Streamed {len(rois)} ROIs"
           self._status_update_signal.emit(msg)

       except Exception as e:
           # Error dialog on UI thread
           QTimer.singleShot(0, lambda: QMessageBox.warning(
               self, "Error", str(e)
           ))

Best Practices
-------------

**When to Use Incremental Updates**

Use incremental updates when:

- List has many items (10+)
- Updates are frequent (per-keystroke)
- Items have stable identities (indices, IDs)
- Preview computation is expensive

**When to Use Full Refresh**

Use full refresh when:

- List structure changes (items added/removed/reordered)
- Scope mapping is invalid or stale
- Incremental update complexity outweighs benefits

**When to Use Background Threads**

Use background threads when:

- Operation blocks for >100ms
- File I/O or network requests
- Waiting for external services
- CPU-intensive processing

**Threading Safety Checklist**

1. ✅ Use ``daemon=True`` for all background threads
2. ✅ Never call UI methods from background threads
3. ✅ Use Qt signals for cross-thread communication
4. ✅ Use ``QTimer.singleShot()`` for one-shot UI operations
5. ✅ Handle exceptions in background threads
6. ✅ Show errors via dialogs on UI thread

**Optimization Checklist**

1. ✅ Collect live context ONCE per refresh cycle
2. ✅ Use token caching for expensive operations
3. ✅ Update existing widgets instead of rebuilding
4. ✅ Batch multiple changes before processing
5. ✅ Use scope filtering to limit context collection
6. ✅ Implement incremental updates for large lists
7. ✅ Move blocking operations to background threads

