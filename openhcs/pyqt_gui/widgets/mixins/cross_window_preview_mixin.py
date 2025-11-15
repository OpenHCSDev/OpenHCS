"""Mixin for widgets that consume cross-window ParameterFormManager updates."""

from __future__ import annotations

from typing import Any, Callable, Dict, Hashable, Optional, Set, Type
import logging

logger = logging.getLogger(__name__)


class CrossWindowPreviewMixin:
    """Shared helpers for windows that respond to cross-window preview updates.

    This mixin provides:
    1. Scope-based routing for targeted updates
    2. Debounced preview updates (100ms trailing debounce)
    3. Incremental updates (only affected items refresh)
    4. Configurable preview fields (per-widget control over which fields show previews)

    Usage:
        class MyWidget(QWidget, CrossWindowPreviewMixin):
            def __init__(self):
                super().__init__()
                self._init_cross_window_preview_mixin()

                # Configure which fields to show in previews
                self.enable_preview_for_field('napari_streaming_config.enabled',
                                             lambda v: 'N:✓' if v else 'N:✗')
                self.enable_preview_for_field('fiji_streaming_config.enabled',
                                             lambda v: 'F:✓' if v else 'F:✗')

                # Implement the 4 required hooks...
    """

    # Debounce delay for preview updates (ms)
    # Trailing debounce: timer restarts on each change, only executes after typing stops
    PREVIEW_UPDATE_DEBOUNCE_MS = 100

    def _init_cross_window_preview_mixin(self) -> None:
        self._preview_scope_map: Dict[str, Hashable] = {}
        self._pending_preview_keys: Set[Hashable] = set()
        self._preview_update_timer = None  # QTimer for debouncing preview updates

        # Per-widget preview field configuration
        self._preview_fields: Dict[str, Callable] = {}  # field_path -> formatter function

        # CRITICAL: Register as external listener for cross-window refresh signals
        # This makes preview labels reactive to live context changes
        # Listen to both value changes AND refresh events (e.g., reset button clicks)
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        ParameterFormManager.register_external_listener(
            self,
            value_changed_handler=self.handle_cross_window_preview_change,
            refresh_handler=self.handle_cross_window_preview_refresh  # Listen to refresh events (reset buttons)
        )

    # --- Scope mapping helpers -------------------------------------------------
    def set_preview_scope_mapping(self, scope_map: Dict[str, Hashable]) -> None:
        """Replace the scope->item mapping used for incremental updates."""
        self._preview_scope_map = dict(scope_map)

    def register_preview_scope(self, scope_id: Optional[str], item_key: Hashable) -> None:
        if scope_id:
            self._preview_scope_map[scope_id] = item_key

    def unregister_preview_scope(self, scope_id: Optional[str]) -> None:
        if scope_id and scope_id in self._preview_scope_map:
            del self._preview_scope_map[scope_id]

    # --- Preview field configuration -------------------------------------------
    def enable_preview_for_field(self, field_path: str, formatter: Optional[Callable[[Any], str]] = None) -> None:
        """Enable preview label for a specific field.

        This allows per-widget control over which configuration fields are shown
        in preview labels. Each widget can configure its own set of preview fields.

        Args:
            field_path: Dot-separated field path (e.g., 'napari_streaming_config.enabled')
            formatter: Optional formatter function that takes the field value and returns
                      a string for display. If None, uses str() to format the value.

        Example:
            # Show napari streaming status with checkmark/cross
            self.enable_preview_for_field(
                'napari_streaming_config.enabled',
                lambda v: 'N:✓' if v else 'N:✗'
            )

            # Show num_workers with simple formatting
            self.enable_preview_for_field(
                'global_config.num_workers',
                lambda v: f'W:{v}'
            )
        """
        self._preview_fields[field_path] = formatter or str

    def disable_preview_for_field(self, field_path: str) -> None:
        """Disable preview label for a specific field.

        Args:
            field_path: Dot-separated field path to disable
        """
        self._preview_fields.pop(field_path, None)

    def is_preview_enabled(self, field_path: str) -> bool:
        """Check if preview is enabled for a specific field.

        Args:
            field_path: Dot-separated field path to check

        Returns:
            True if preview is enabled for this field, False otherwise
        """
        return field_path in self._preview_fields

    def format_preview_value(self, field_path: str, value: Any) -> str:
        """Format a value for preview display using the registered formatter.

        Args:
            field_path: Dot-separated field path
            value: The value to format

        Returns:
            Formatted string for display. If no formatter is registered for this
            field, returns str(value).
        """
        formatter = self._preview_fields.get(field_path, str)
        try:
            return formatter(value)
        except Exception:
            # Fallback to str() if formatter fails
            return str(value)

    def get_enabled_preview_fields(self) -> Set[str]:
        """Get the set of all enabled preview field paths.

        Returns:
            Set of field paths that have preview enabled
        """
        return set(self._preview_fields.keys())

    # --- Event routing ---------------------------------------------------------
    def handle_cross_window_preview_change(
        self,
        field_path: Optional[str],
        new_value: Any,
        editing_object: Any,
        context_object: Any,
    ) -> None:
        """Shared handler to route cross-window updates to incremental refreshes.

        Uses trailing debounce: timer restarts on each change, only executes after
        changes stop for PREVIEW_UPDATE_DEBOUNCE_MS milliseconds.
        """
        import logging
        logger = logging.getLogger(__name__)

        if not self._should_process_preview_field(
            field_path, new_value, editing_object, context_object
        ):
            return

        scope_id = self._extract_scope_id_for_preview(editing_object, context_object)

        # Add affected items to pending set
        if scope_id in ("PIPELINE_CONFIG_CHANGE", "GLOBAL_CONFIG_CHANGE"):
            # Refresh ALL items (add all item keys to pending updates)
            # Generic: works with any item key type (int for steps, str for plates, etc.)
            all_item_keys = list(self._preview_scope_map.values())
            for item_key in all_item_keys:
                self._pending_preview_keys.add(item_key)
        elif scope_id and scope_id in self._preview_scope_map:
            item_key = self._preview_scope_map[scope_id]
            self._pending_preview_keys.add(item_key)
        elif scope_id is None:
            # Unknown scope - trigger full refresh
            self._schedule_preview_update(full_refresh=True)
            return
        else:
            # Scope not in map - might be a new item or unrelated change
            return

        # Schedule debounced update (trailing debounce - restarts timer on each change)
        self._schedule_preview_update(full_refresh=False)

    def handle_cross_window_preview_refresh(
        self,
        editing_object: Any,
        context_object: Any,
    ) -> None:
        """Handle cross-window refresh events (e.g., reset button clicks).

        This is called when a ParameterFormManager emits context_refreshed signal,
        which happens when:
        - User clicks Reset button (reset_all_parameters or reset_parameter)
        - User cancels a config editor window (trigger_global_cross_window_refresh)

        Unlike handle_cross_window_preview_change which does incremental updates,
        this triggers a full refresh since reset can affect multiple fields.
        """
        import logging
        logger = logging.getLogger(__name__)

        # Extract scope ID to determine which item needs refresh
        scope_id = self._extract_scope_id_for_preview(editing_object, context_object)

        # Add affected items to pending set (same logic as handle_cross_window_preview_change)
        if scope_id in ("PIPELINE_CONFIG_CHANGE", "GLOBAL_CONFIG_CHANGE"):
            # Refresh ALL items
            all_item_keys = list(self._preview_scope_map.values())
            for item_key in all_item_keys:
                self._pending_preview_keys.add(item_key)
            logger.info(f"handle_cross_window_preview_refresh: Refreshing ALL items ({len(all_item_keys)} items)")
        elif scope_id and scope_id in self._preview_scope_map:
            item_key = self._preview_scope_map[scope_id]
            self._pending_preview_keys.add(item_key)
            logger.info(f"handle_cross_window_preview_refresh: Refreshing item {item_key} for scope {scope_id}")
        elif scope_id is None:
            # Unknown scope - trigger full refresh
            logger.info("handle_cross_window_preview_refresh: Unknown scope, triggering full refresh")
            self._schedule_preview_update(full_refresh=True)
            return
        else:
            # Scope not in map - might be unrelated change
            logger.debug(f"handle_cross_window_preview_refresh: Scope {scope_id} not in map, skipping")
            return

        # Schedule debounced update
        self._schedule_preview_update(full_refresh=False)

    def _schedule_preview_update(self, full_refresh: bool = False) -> None:
        """Schedule a debounced preview update.

        Trailing debounce: timer restarts on each call, only executes after
        calls stop for PREVIEW_UPDATE_DEBOUNCE_MS milliseconds.

        Args:
            full_refresh: If True, trigger full refresh instead of incremental
        """
        from PyQt6.QtCore import QTimer

        # Cancel existing timer if any (trailing debounce - restart on each change)
        if self._preview_update_timer is not None:
            self._preview_update_timer.stop()

        # Schedule new update after configured delay
        self._preview_update_timer = QTimer()
        self._preview_update_timer.setSingleShot(True)

        if full_refresh:
            self._preview_update_timer.timeout.connect(self._handle_full_preview_refresh)
        else:
            self._preview_update_timer.timeout.connect(self._process_pending_preview_updates)

        delay = max(0, self.PREVIEW_UPDATE_DEBOUNCE_MS)
        self._preview_update_timer.start(delay)

    # --- Preview instance with live values (shared pattern) -------------------
    def _get_preview_instance(self, obj: Any, live_context_snapshot, scope_id: str, obj_type: Type) -> Any:
        """Get object instance with live values merged (shared pattern for PipelineEditor and PlateManager).

        This implements the pattern from docs/source/development/scope_hierarchy_live_context.rst:
        - Get live values from scoped_values for this scope_id
        - Merge live values into the object
        - Return merged object for display

        Args:
            obj: Original object (FunctionStep for PipelineEditor, PipelineConfig for PlateManager)
            live_context_snapshot: LiveContextSnapshot from ParameterFormManager
            scope_id: Scope identifier (e.g., "plate_path::step_name" or "plate_path")
            obj_type: Type to look up in scoped_values (e.g., FunctionStep or PipelineConfig)

        Returns:
            Object with live values merged, or original object if no live values
        """
        if live_context_snapshot is None:
            return obj

        token = getattr(live_context_snapshot, 'token', None)
        if token is None:
            return obj

        # Get scoped values for this scope_id
        scoped_values = getattr(live_context_snapshot, 'scoped_values', {}) or {}
        scope_entries = scoped_values.get(scope_id)
        if not scope_entries:
            logger.debug(f"No scope entries for {scope_id}")
            return obj

        # Get live values for this object type
        obj_live_values = scope_entries.get(obj_type)
        if not obj_live_values:
            logger.debug(f"No live values for {obj_type.__name__} in scope {scope_id}")
            return obj

        # Merge live values into object
        merged_obj = self._merge_with_live_values(obj, obj_live_values)
        return merged_obj

    def _merge_with_live_values(self, obj: Any, live_values: Dict[str, Any]) -> Any:
        """Merge object with live values from ParameterFormManager.

        This must be implemented by subclasses because the merge strategy depends on the object type:
        - PipelineEditor: Uses copy.deepcopy(step) and setattr for each field
        - PlateManager: Uses dataclasses.replace or manual reconstruction

        Args:
            obj: Original object
            live_values: Dict of field_name -> value from ParameterFormManager

        Returns:
            New object with live values merged
        """
        raise NotImplementedError("Subclasses must implement _merge_with_live_values")

    # --- Hooks for subclasses --------------------------------------------------
    def _should_process_preview_field(
        self,
        field_path: Optional[str],
        new_value: Any,
        editing_object: Any,
        context_object: Any,
    ) -> bool:
        """Return True if a cross-window change should trigger a preview update."""
        raise NotImplementedError

    def _extract_scope_id_for_preview(
        self, editing_object: Any, context_object: Any
    ) -> Optional[str]:
        """Extract the relevant scope identifier from the editing/context objects."""
        raise NotImplementedError

    def _process_pending_preview_updates(self) -> None:
        """Apply incremental updates for all pending preview keys."""
        raise NotImplementedError

    def _handle_full_preview_refresh(self) -> None:
        """Fallback handler when incremental updates are not possible."""
        raise NotImplementedError
