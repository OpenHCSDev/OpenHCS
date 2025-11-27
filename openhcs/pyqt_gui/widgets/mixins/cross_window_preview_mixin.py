"""Mixin for widgets that consume cross-window ParameterFormManager updates."""

from __future__ import annotations

from typing import Any, Callable, Dict, Hashable, Iterable, Optional, Set, Tuple, Type
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

    # Scope resolver sentinels
    ALL_ITEMS_SCOPE = "__ALL_ITEMS_SCOPE__"
    FULL_REFRESH_SCOPE = "__FULL_REFRESH__"
    ROOTLESS_SCOPE = "__ROOTLESS__"

    def _init_cross_window_preview_mixin(self) -> None:
        self._preview_scope_map: Dict[str, Hashable] = {}
        self._pending_preview_keys: Set[Hashable] = set()
        self._preview_update_timer = None  # QTimer for debouncing preview updates

        # Per-widget preview field configuration
        self._preview_fields: Dict[str, Callable] = {}  # field_path -> formatter function
        self._preview_field_roots: Dict[str, Optional[str]] = {}
        self._preview_field_index: Dict[str, Set[str]] = {self.ROOTLESS_SCOPE: set()}
        self._preview_field_fallbacks: Dict[str, Callable] = {}

        # Scope registration metadata
        self._preview_scope_handlers: list[Dict[str, Any]] = []
        self._preview_scope_aliases: Dict[str, str] = {}
        self._preview_scope_registry: Dict[str, Dict[str, Any]] = {}

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
    def register_preview_scope(
        self,
        root_name: str,
        editing_types: Iterable[Type],
        scope_resolver: Callable[[Any, Any], Optional[str]],
        *,
        aliases: Optional[Iterable[str]] = None,
        process_all_fields: bool = False,
    ) -> None:
        """Register how editing objects map to scope identifiers."""
        types_tuple: Tuple[Type, ...] = tuple(editing_types)
        entry = {
            "root": root_name,
            "types": types_tuple,
            "resolver": scope_resolver,
            "process_all_fields": process_all_fields,
        }
        self._preview_scope_handlers.append(entry)
        self._preview_scope_registry[root_name] = entry

        # Register canonical alias + provided aliases
        self._preview_scope_aliases[root_name] = root_name
        self._preview_scope_aliases[root_name.lower()] = root_name
        if aliases:
            for alias in aliases:
                self._preview_scope_aliases[alias] = root_name
                self._preview_scope_aliases[alias.lower()] = root_name

    def enable_preview_for_field(
        self,
        field_path: str,
        formatter: Optional[Callable[[Any], str]] = None,
        *,
        scope_root: Optional[str] = None,
        fallback_resolver: Optional[Callable[[Any, Dict[str, Any]], Any]] = None,
    ) -> None:
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

        canonical_root = self._canonicalize_root(scope_root) if scope_root else None
        self._preview_field_roots[field_path] = canonical_root

        index_key = canonical_root or self.ROOTLESS_SCOPE
        if index_key not in self._preview_field_index:
            self._preview_field_index[index_key] = set()
        self._preview_field_index[index_key].add(field_path)

        if fallback_resolver:
            self._preview_field_fallbacks[field_path] = fallback_resolver

    def disable_preview_for_field(self, field_path: str) -> None:
        """Disable preview label for a specific field.

        Args:
            field_path: Dot-separated field path to disable
        """
        self._preview_fields.pop(field_path, None)

        root = self._preview_field_roots.pop(field_path, None)
        index_key = root or self.ROOTLESS_SCOPE
        if index_key in self._preview_field_index:
            self._preview_field_index[index_key].discard(field_path)
            if not self._preview_field_index[index_key]:
                del self._preview_field_index[index_key]

        self._preview_field_fallbacks.pop(field_path, None)

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

    def enable_preview_fields_from_introspection(
        self,
        *,
        base_fields: Iterable[str],
        nested_configs: Optional[Iterable[Tuple[Optional[str], Type]]] = None,
        config_attrs: Optional[Iterable[str]] = None,
        sample_object_factory: Optional[Callable[[], Any]] = None,
        scope_root: Optional[str] = None,
    ) -> None:
        """
        Enable preview fields discovered via introspection instead of hardcoding paths.

        Args:
            base_fields: Iterable of explicit field paths to include.
            nested_configs: Iterable of (prefix, dataclass_type) pairs. Each dataclass'
                annotated fields will be registered with the optional prefix
                (e.g., ('processing_config', ProcessingConfig) -> processing_config.foo).
            config_attrs: Iterable of attribute names to include if present on the sample object.
            sample_object_factory: Optional callable returning an object used to probe which
                config attributes actually exist. Attributes missing on the sample object
                are skipped to avoid registering dead paths.
            scope_root: Scope root passed through to enable_preview_for_field.
        """
        field_paths: Set[str] = set(base_fields or [])

        for prefix, config_cls in nested_configs or []:
            annotations = getattr(config_cls, '__annotations__', {}) or {}
            for field_name in annotations.keys():
                if prefix:
                    field_paths.add(f"{prefix}.{field_name}")
                else:
                    field_paths.add(field_name)

        sample_obj = sample_object_factory() if sample_object_factory else None
        if sample_obj is not None:
            for attr in config_attrs or []:
                if hasattr(sample_obj, attr):
                    field_paths.add(attr)
        else:
            for attr in config_attrs or []:
                field_paths.add(attr)

        for field_path in sorted(field_paths):
            self.enable_preview_for_field(field_path, scope_root=scope_root)

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
        if scope_id == self.ALL_ITEMS_SCOPE:
            # Refresh ALL items (add all item keys to pending updates)
            # Generic: works with any item key type (int for steps, str for plates, etc.)
            all_item_keys = list(self._preview_scope_map.values())
            for item_key in all_item_keys:
                self._pending_preview_keys.add(item_key)
        elif scope_id == self.FULL_REFRESH_SCOPE:
            self._schedule_preview_update(full_refresh=True)
            return
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
        if scope_id == self.ALL_ITEMS_SCOPE:
            # Refresh ALL items
            all_item_keys = list(self._preview_scope_map.values())
            for item_key in all_item_keys:
                self._pending_preview_keys.add(item_key)
            logger.info(f"handle_cross_window_preview_refresh: Refreshing ALL items ({len(all_item_keys)} items)")
        elif scope_id == self.FULL_REFRESH_SCOPE:
            logger.info("handle_cross_window_preview_refresh: Forcing full refresh via resolver")
            self._schedule_preview_update(full_refresh=True)
            return
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
        if not field_path:
            return True

        if "__WINDOW_CLOSED__" in field_path:
            return True

        root_token, attr_path = self._split_field_path(field_path)
        canonical_root = self._canonicalize_root(root_token)

        if canonical_root is None:
            return self._matches_rootless_field(field_path)

        scope_entry = self._preview_scope_registry.get(canonical_root)
        if not scope_entry:
            return False

        if not attr_path:
            return True

        tracked_fields = self._preview_field_index.get(canonical_root, set())
        if not tracked_fields:
            return scope_entry.get("process_all_fields", False)

        for tracked_field in tracked_fields:
            if self._attr_path_matches(tracked_field, attr_path):
                return True

        return scope_entry.get("process_all_fields", False)

    def _extract_scope_id_for_preview(
        self, editing_object: Any, context_object: Any
    ) -> Optional[str]:
        """Extract the relevant scope identifier from the editing/context objects."""
        entry = self._find_scope_entry_for_object(editing_object)
        if not entry:
            return None

        resolver = entry.get("resolver")
        if not resolver:
            return None

        try:
            return resolver(editing_object, context_object)
        except Exception:
            logger.exception("Preview scope resolver failed", exc_info=True)
            return None

    def _process_pending_preview_updates(self) -> None:
        """Apply incremental updates for all pending preview keys."""
        raise NotImplementedError

    def _handle_full_preview_refresh(self) -> None:
        """Fallback handler when incremental updates are not possible."""
        raise NotImplementedError

    # --- Helper methods -------------------------------------------------------
    def _canonicalize_root(self, root: Optional[str]) -> Optional[str]:
        if root is None:
            return None
        if root in self._preview_scope_aliases:
            return self._preview_scope_aliases[root]
        lowered = root.lower()
        return self._preview_scope_aliases.get(lowered)

    def _split_field_path(self, field_path: str) -> Tuple[Optional[str], str]:
        parts = field_path.split(".", 1)
        if len(parts) == 1:
            return parts[0], ""
        return parts[0], parts[1]

    def _attr_path_matches(self, tracked_path: str, attr_path: str) -> bool:
        if not tracked_path:
            return True
        return attr_path == tracked_path or attr_path.startswith(f"{tracked_path}.")

    def _matches_rootless_field(self, field_path: str) -> bool:
        tracked_fields = self._preview_field_index.get(self.ROOTLESS_SCOPE, set())
        for tracked in tracked_fields:
            if field_path == tracked or field_path.startswith(f"{tracked}."):
                return True
        return False

    def _apply_preview_field_fallback(
        self,
        field_path: str,
        context: Optional[Dict[str, Any]] = None,
    ) -> Any:
        resolver = self._preview_field_fallbacks.get(field_path)
        if not resolver:
            return None
        try:
            return resolver(self, context or {})
        except Exception:
            logger.exception("Preview fallback resolver failed", exc_info=True)
            return None

    def _find_scope_entry_for_object(self, editing_object: Any) -> Optional[Dict[str, Any]]:
        if editing_object is None:
            return None

        for entry in self._preview_scope_handlers:
            for type_candidate in entry.get("types", ()):
                if isinstance(editing_object, type_candidate):
                    return entry

        return None
