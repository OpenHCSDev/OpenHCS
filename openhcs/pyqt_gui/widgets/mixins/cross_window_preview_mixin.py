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
    # Set to 0 for instant updates - coordinator handles batching
    PREVIEW_UPDATE_DEBOUNCE_MS = 0  # INSTANT: No lag

    # Scope resolver sentinels
    ALL_ITEMS_SCOPE = "__ALL_ITEMS_SCOPE__"
    FULL_REFRESH_SCOPE = "__FULL_REFRESH__"
    ROOTLESS_SCOPE = "__ROOTLESS__"

    def _init_cross_window_preview_mixin(self) -> None:
        self._preview_scope_map: Dict[str, Hashable] = {}
        self._pending_preview_keys: Set[Hashable] = set()
        self._pending_label_keys: Set[Hashable] = set()
        self._pending_changed_fields: Set[str] = set()  # Track which fields changed during debounce
        self._last_live_context_snapshot = None  # Last LiveContextSnapshot (becomes "before" for next change)
        self._preview_update_timer = None  # QTimer for debouncing preview updates

        # Window close event state (passed as parameters, stored temporarily for timer callback)
        self._pending_window_close_before_snapshot = None
        self._pending_window_close_after_snapshot = None
        self._pending_window_close_changed_fields = None

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

        # Capture initial snapshot so first change has a baseline for flash detection
        try:
            self._last_live_context_snapshot = ParameterFormManager.collect_live_context()
        except Exception:
            self._last_live_context_snapshot = None



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
        scope_id = self._extract_scope_id_for_preview(editing_object, context_object)
        target_keys, requires_full_refresh = self._resolve_scope_targets(scope_id)

        # Track which field changed (for flash logic - ALWAYS track, don't filter)
        if field_path:
            root_token, attr_path = self._split_field_path(field_path)
            canonical_root = self._canonicalize_root(root_token) or root_token
            identifiers: Set[str] = set()
            if attr_path:
                identifiers.add(attr_path)
                if "." in attr_path:
                    final_part = attr_path.split(".")[-1]
                    if final_part:
                        identifiers.add(final_part)
                if canonical_root:
                    identifiers.add(f"{canonical_root}.{attr_path}")
            else:
                final_part = field_path.split('.')[-1]
                if final_part:
                    identifiers.add(final_part)
                if canonical_root:
                    identifiers.add(canonical_root)

            for identifier in identifiers:
                self._pending_changed_fields.add(identifier)

        # Check if this change affects displayed text (for label updates)
        should_update_labels = self._should_process_preview_field(
            field_path, new_value, editing_object, context_object
        )

        logger.info(f"🔍 handle_cross_window_preview_change: target_keys={target_keys}, requires_full_refresh={requires_full_refresh}, should_update_labels={should_update_labels}")

        if requires_full_refresh:
            self._pending_preview_keys.clear()
            self._pending_label_keys.clear()
            self._pending_changed_fields.clear()
            logger.info(f"🔍 handle_cross_window_preview_change: Calling _schedule_preview_update(full_refresh=True)")
            self._schedule_preview_update(full_refresh=True)
            return

        if target_keys:
            self._pending_preview_keys.update(target_keys)
            if should_update_labels:
                self._pending_label_keys.update(target_keys)

        logger.info(f"🔍 handle_cross_window_preview_change: Calling _schedule_preview_update(full_refresh=False), _pending_preview_keys={self._pending_preview_keys}")
        # Schedule debounced update (always schedule to handle flash, even if no label updates)
        self._schedule_preview_update(full_refresh=False)

    def handle_window_close(
        self,
        editing_object: Any,
        context_object: Any,
        before_snapshot: Any,
        after_snapshot: Any,
        changed_fields: Set[str],
    ) -> None:
        """Handle window close events with dedicated snapshot parameters.

        This is called when a config editor window is closed without saving.
        Unlike incremental updates, this receives explicit before/after snapshots
        to compare the unsaved edits against the reverted state.

        Args:
            editing_object: The object being edited (e.g., PipelineConfig)
            context_object: The context object for resolution
            before_snapshot: LiveContextSnapshot with form manager (unsaved edits)
            after_snapshot: LiveContextSnapshot without form manager (reverted)
            changed_fields: Set of field identifiers that changed
        """
        import logging
        logger = logging.getLogger(__name__)

        logger.debug(f"🔍 {self.__class__.__name__}.handle_window_close: {len(changed_fields)} changed fields")

        scope_id = self._extract_scope_id_for_preview(editing_object, context_object)
        target_keys, requires_full_refresh = self._resolve_scope_targets(scope_id)

        # Add target keys to pending sets
        self._pending_preview_keys.update(target_keys)
        self._pending_label_keys.update(target_keys)

        # Window close always triggers full refresh with explicit snapshots
        self._schedule_preview_update(
            full_refresh=True,
            before_snapshot=before_snapshot,
            after_snapshot=after_snapshot,
            changed_fields=changed_fields,
        )

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

        logger.debug(f"🔥 handle_cross_window_preview_refresh: editing_object={type(editing_object).__name__}, context_object={type(context_object).__name__ if context_object else None}")

        # Extract scope ID to determine which item needs refresh
        scope_id = self._extract_scope_id_for_preview(editing_object, context_object)
        logger.debug(f"🔥 handle_cross_window_preview_refresh: scope_id={scope_id}")
        target_keys, requires_full_refresh = self._resolve_scope_targets(scope_id)
        logger.debug(f"🔥 handle_cross_window_preview_refresh: target_keys={target_keys}, requires_full_refresh={requires_full_refresh}")

        if requires_full_refresh:
            self._pending_preview_keys.clear()
            self._pending_label_keys.clear()
            self._pending_changed_fields.clear()
            self._schedule_preview_update(full_refresh=True)
            return

        if not target_keys:
            # Scope not in map - might be unrelated change
            logger.debug(f"handle_cross_window_preview_refresh: Scope {scope_id} not in map, skipping")
            return

        self._pending_preview_keys.update(target_keys)
        self._pending_label_keys.update(target_keys)

        # Schedule debounced update
        self._schedule_preview_update(full_refresh=False)

    def _schedule_preview_update(
        self,
        full_refresh: bool = False,
        before_snapshot: Any = None,
        after_snapshot: Any = None,
        changed_fields: Set[str] = None,
        use_coordinator: bool = True,
    ) -> None:
        """Schedule a debounced preview update.

        Trailing debounce: timer restarts on each call, only executes after
        calls stop for PREVIEW_UPDATE_DEBOUNCE_MS milliseconds.

        Args:
            full_refresh: If True, trigger full refresh instead of incremental
            before_snapshot: Optional before snapshot for window close events
            after_snapshot: Optional after snapshot for window close events
            changed_fields: Optional changed fields for window close events
            use_coordinator: If True, use central coordinator for synchronized updates (default)
        """
        logger.debug(f"🔥 _schedule_preview_update called: full_refresh={full_refresh}, use_coordinator={use_coordinator}")

        # Store window close snapshots if provided (for timer callback)
        if before_snapshot is not None and after_snapshot is not None:
            self._pending_window_close_before_snapshot = before_snapshot
            self._pending_window_close_after_snapshot = after_snapshot
            self._pending_window_close_changed_fields = changed_fields
            logger.debug(f"🔥 Stored window close snapshots: before={before_snapshot.token}, after={after_snapshot.token}")

        # PERFORMANCE: Use central coordinator for cross-window updates
        # This makes all listeners update simultaneously instead of sequentially
        if use_coordinator and not full_refresh:
            from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

            # Cancel any existing local timer
            if self._preview_update_timer is not None:
                logger.debug(f"🔥 Stopping existing timer (using coordinator)")
                self._preview_update_timer.stop()
                self._preview_update_timer = None

            # Register with coordinator for synchronized update
            ParameterFormManager.schedule_coordinated_update(self)
            return

        # Fallback to individual timer for full refreshes or when coordinator disabled
        from PyQt6.QtCore import QTimer

        # Cancel existing timer if any (trailing debounce - restart on each change)
        if self._preview_update_timer is not None:
            logger.debug(f"🔥 Stopping existing timer")
            self._preview_update_timer.stop()

        # Schedule new update after configured delay
        self._preview_update_timer = QTimer()
        self._preview_update_timer.setSingleShot(True)

        if full_refresh:
            logger.debug(f"🔥 Connecting to _handle_full_preview_refresh")
            self._preview_update_timer.timeout.connect(self._handle_full_preview_refresh)
        else:
            logger.debug(f"🔥 Connecting to _process_pending_preview_updates")
            self._preview_update_timer.timeout.connect(self._process_pending_preview_updates)

        delay = max(0, self.PREVIEW_UPDATE_DEBOUNCE_MS)
        self._preview_update_timer.start(delay)
        logger.debug(f"🔥 Timer started with {delay}ms delay")

    # --- Preview instance with live values (shared pattern) -------------------
    def _get_preview_instance_generic(
        self,
        obj: Any,
        obj_type: type,
        scope_id: Optional[str],
        live_context_snapshot: Optional[Any],
        use_global_values: bool = False
    ) -> Any:
        """
        Generic preview instance getter with scoped live values merged.

        This is the SINGLE SOURCE OF TRUTH for extracting and merging live values
        from LiveContextSnapshot. All preview instance methods use this.

        This implements the pattern from docs/source/development/scope_hierarchy_live_context.rst

        Args:
            obj: Original object to merge live values into
            obj_type: Type to look up in scoped_values or values dict
            scope_id: Scope identifier (e.g., "/path/to/plate::step_0" or "/path/to/plate")
                     Ignored if use_global_values=True
            live_context_snapshot: Live context snapshot with scoped values
            use_global_values: If True, use snapshot.values (for GlobalPipelineConfig)
                              If False, use snapshot.scoped_values[scope_id] (for scoped objects)

        Returns:
            Object with live values merged, or original object if no live values
        """
        if live_context_snapshot is None:
            return obj

        token = getattr(live_context_snapshot, 'token', None)
        if token is None:
            return obj

        # Extract live values from appropriate location
        if use_global_values:
            # For GlobalPipelineConfig: use global values dict
            values = getattr(live_context_snapshot, 'values', {}) or {}
            live_values = values.get(obj_type)
        else:
            # For scoped objects (PipelineConfig, FunctionStep): use scoped values
            if scope_id is None:
                return obj
            scoped_values = getattr(live_context_snapshot, 'scoped_values', {}) or {}
            scope_entries = scoped_values.get(scope_id)
            if not scope_entries:
                return obj
            live_values = scope_entries.get(obj_type)

        if not live_values:
            return obj

        # Merge live values into object (subclass implements merge strategy)
        merged_obj = self._merge_with_live_values(obj, live_values)
        return merged_obj

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
        return self._get_preview_instance_generic(
            obj=obj,
            obj_type=obj_type,
            scope_id=scope_id,
            live_context_snapshot=live_context_snapshot,
            use_global_values=False
        )

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
    def _resolve_scope_targets(self, scope_id: Optional[str]) -> Tuple[Optional[Set[Hashable]], bool]:
        """Map a scope identifier to concrete preview keys.

        Returns:
            (target_keys, requires_full_refresh)
        """
        if scope_id == self.ALL_ITEMS_SCOPE:
            return set(self._preview_scope_map.values()), False
        if scope_id == self.FULL_REFRESH_SCOPE:
            return None, True
        if scope_id and scope_id in self._preview_scope_map:
            return {self._preview_scope_map[scope_id]}, False
        if scope_id is None:
            return None, True
        return set(), False

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

    # OLD SEQUENTIAL METHOD REMOVED - Use _check_resolved_values_changed_batch() instead
    # This ensures all callers are updated to use the faster batch method

    def _check_resolved_values_changed_batch(
        self,
        obj_pairs: list[tuple[Any, Any]],
        changed_fields: Optional[Set[str]],
        *,
        live_context_before=None,
        live_context_after=None,
    ) -> list[bool]:
        """Check if resolved values changed for multiple objects in one batch.

        This is MUCH faster than calling _check_resolved_value_changed() for each object
        individually because it resolves all attributes in one context setup.

        Args:
            obj_pairs: List of (obj_before, obj_after) tuples to check
            changed_fields: Set of field identifiers that changed (None = check all enabled preview fields)
            live_context_before: Live context snapshot before changes (for resolution)
            live_context_after: Live context snapshot after changes (for resolution)

        Returns:
            List of boolean values indicating whether each object pair changed
        """
        logger.info(f"🔍 {self.__class__.__name__}._check_resolved_values_changed_batch START:")
        logger.info(f"  - Object pairs: {len(obj_pairs)}")
        logger.info(f"  - Changed fields: {changed_fields}")
        logger.info(f"  - live_context_before is None: {live_context_before is None}")
        logger.info(f"  - live_context_before token: {getattr(live_context_before, 'token', None)}")
        logger.info(f"  - live_context_after is None: {live_context_after is None}")
        logger.info(f"  - live_context_after token: {getattr(live_context_after, 'token', None)}")

        if not obj_pairs:
            logger.info(f"  - No object pairs, returning empty list")
            return []

        # CRITICAL: Use window close snapshots if available (passed via handle_window_close)
        # This ensures we compare the right snapshots:
        # before = with form manager (unsaved edits)
        # after = without form manager (reverted to saved)
        if (hasattr(self, '_pending_window_close_before_snapshot') and
            hasattr(self, '_pending_window_close_after_snapshot') and
            self._pending_window_close_before_snapshot is not None and
            self._pending_window_close_after_snapshot is not None):
            logger.info(f"  - Using window_close snapshots: before={self._pending_window_close_before_snapshot.token}, after={self._pending_window_close_after_snapshot.token}")
            logger.debug(f"🔍 {self.__class__.__name__}._check_resolved_values_changed_batch: before scoped_values keys: {list(self._pending_window_close_before_snapshot.scoped_values.keys()) if hasattr(self._pending_window_close_before_snapshot, 'scoped_values') else 'N/A'}")
            logger.debug(f"🔍 {self.__class__.__name__}._check_resolved_values_changed_batch: after scoped_values keys: {list(self._pending_window_close_after_snapshot.scoped_values.keys()) if hasattr(self._pending_window_close_after_snapshot, 'scoped_values') else 'N/A'}")
            live_context_before = self._pending_window_close_before_snapshot
            live_context_after = self._pending_window_close_after_snapshot
            # Use window close changed fields if provided
            if hasattr(self, '_pending_window_close_changed_fields') and self._pending_window_close_changed_fields is not None:
                changed_fields = self._pending_window_close_changed_fields
            # Clear the snapshots after use
            self._pending_window_close_before_snapshot = None
            self._pending_window_close_after_snapshot = None
            self._pending_window_close_changed_fields = None

        # If changed_fields is None, check ALL enabled preview fields (full refresh case)
        if changed_fields is None:
            logger.debug(f"🔍 {self.__class__.__name__}._check_resolved_values_changed_batch: changed_fields=None, checking ALL enabled preview fields")
            changed_fields = self.get_enabled_preview_fields()
            if not changed_fields:
                logger.debug(f"🔍 {self.__class__.__name__}._check_resolved_values_changed_batch: No enabled preview fields, returning all False")
                return [False] * len(obj_pairs)
        elif not changed_fields:
            logger.debug(f"🔍 {self.__class__.__name__}._check_resolved_values_changed_batch: Empty changed_fields, returning all False")
            return [False] * len(obj_pairs)

        logger.debug(f"🔍 {self.__class__.__name__}._check_resolved_values_changed_batch: Checking {len(obj_pairs)} objects with {len(changed_fields)} identifiers")

        # Use the first object to expand identifiers (they should all be the same type)
        # CRITICAL: Use live_context_before for expansion because it has the form manager's values
        # live_context_after might be empty (e.g., window close after unregistering form manager)
        if obj_pairs:
            _, first_obj_after = obj_pairs[0]
            logger.info(f"🔍 _check_resolved_values_changed_batch: BEFORE expansion: changed_fields={changed_fields}")
            expanded_identifiers = self._expand_identifiers_for_inheritance(
                first_obj_after, changed_fields, live_context_before
            )
            logger.info(f"🔍 _check_resolved_values_changed_batch: AFTER expansion: expanded_identifiers={expanded_identifiers}")
        else:
            expanded_identifiers = changed_fields

        logger.debug(f"🔍 _check_resolved_values_changed_batch: Expanded to {len(expanded_identifiers)} identifiers: {expanded_identifiers}")

        # Batch resolve all objects
        results = []
        for idx, (obj_before, obj_after) in enumerate(obj_pairs):
            # Log which object we're checking
            obj_name = getattr(obj_after, 'name', f'object_{idx}')
            logger.debug(f"🔍 _check_resolved_values_changed_batch: Checking object '{obj_name}' (index {idx})")

            # Use batch resolution for this object
            changed = self._check_single_object_with_batch_resolution(
                obj_before,
                obj_after,
                expanded_identifiers,
                live_context_before,
                live_context_after
            )
            logger.debug(f"🔍 _check_resolved_values_changed_batch: Object '{obj_name}' changed={changed}")
            results.append(changed)

        logger.debug(f"🔍 _check_resolved_values_changed_batch: Results: {sum(results)}/{len(results)} changed")
        return results

    def _check_single_object_with_batch_resolution(
        self,
        obj_before: Any,
        obj_after: Any,
        identifiers: Set[str],
        live_context_before,
        live_context_after
    ) -> bool:
        """Check if a single object changed using batch resolution.

        This resolves all identifiers in one context setup instead of individually.

        Args:
            obj_before: Object before changes
            obj_after: Object after changes
            identifiers: Set of field identifiers to check
            live_context_before: Live context snapshot before changes
            live_context_after: Live context snapshot after changes

        Returns:
            True if any identifier changed
        """
        import logging
        logger = logging.getLogger(__name__)
        logger.info(f"🔍 _check_single_object_with_batch_resolution: identifiers={identifiers}")

        # Try to use batch resolution if we have a context stack
        context_stack_before = self._build_flash_context_stack(obj_before, live_context_before)
        context_stack_after = self._build_flash_context_stack(obj_after, live_context_after)

        logger.info(f"🔍 _check_single_object_with_batch_resolution: context_stack_before={context_stack_before is not None}, context_stack_after={context_stack_after is not None}")

        if context_stack_before and context_stack_after:
            # Use batch resolution
            logger.info(f"🔍 _check_single_object_with_batch_resolution: Using BATCH resolution")
            result = self._check_with_batch_resolution(
                obj_before,
                obj_after,
                identifiers,
                context_stack_before,
                context_stack_after,
                live_context_before,
                live_context_after
            )
            logger.info(f"🔍 _check_single_object_with_batch_resolution: Batch resolution returned {result}")
            return result

        # Fallback to sequential resolution
        logger.info(f"🔍 _check_single_object_with_batch_resolution: Using FALLBACK sequential resolution")
        for identifier in identifiers:
            if not identifier:
                continue

            before_value = self._resolve_flash_field_value(
                obj_before, identifier, live_context_before
            )
            after_value = self._resolve_flash_field_value(
                obj_after, identifier, live_context_after
            )

            if before_value != after_value:
                return True

        return False

    def _check_with_batch_resolution(
        self,
        obj_before: Any,
        obj_after: Any,
        identifiers: Set[str],
        context_stack_before: list,
        context_stack_after: list,
        live_context_before,
        live_context_after
    ) -> bool:
        """Check if object changed using batch resolution through LiveContextResolver.

        This is MUCH faster than resolving each identifier individually because it:
        1. Groups identifiers by their parent object (e.g., 'fiji_streaming_config')
        2. Batch resolves ALL attributes on each parent object at once
        3. Only walks the object path once per parent object

        Args:
            obj_before: Object before changes
            obj_after: Object after changes
            identifiers: Set of field identifiers to check
            context_stack_before: Context stack before changes
            context_stack_after: Context stack after changes
            live_context_before: Live context snapshot before changes
            live_context_after: Live context snapshot after changes

        Returns:
            True if any identifier changed
        """
        from openhcs.config_framework import LiveContextResolver
        from dataclasses import is_dataclass

        # Get or create resolver instance
        resolver = getattr(self, '_live_context_resolver', None)
        if resolver is None:
            resolver = LiveContextResolver()
            self._live_context_resolver = resolver

        # Get cache tokens
        token_before = getattr(live_context_before, 'token', 0) if live_context_before else 0
        token_after = getattr(live_context_after, 'token', 0) if live_context_after else 0

        # CRITICAL: Use scoped values if available, otherwise fall back to global values
        # The scoped values are keyed by scope_id (e.g., plate_path), and we need to find
        # the right scope by checking which scope has values
        import logging
        logger = logging.getLogger(__name__)

        logger.info(f"🔍 _check_with_batch_resolution START:")
        logger.info(f"  - token_before: {token_before}")
        logger.info(f"  - token_after: {token_after}")
        logger.info(f"  - Identifiers to check: {len(identifiers)}")

        # Try to find the scope_id from scoped_values
        scope_id = None
        if live_context_before:
            scoped_before = getattr(live_context_before, 'scoped_values', {})
            if scoped_before:
                # Use the first scope (should only be one for plate-scoped operations)
                scope_id = list(scoped_before.keys())[0] if scoped_before else None

        # Extract live context dicts (scoped if available, otherwise global)
        if scope_id and live_context_before:
            scoped_before = getattr(live_context_before, 'scoped_values', {})
            live_ctx_before = scoped_before.get(scope_id, {})
            logger.info(f"  - Using SCOPED values for scope_id={scope_id}")
        else:
            live_ctx_before = getattr(live_context_before, 'values', {}) if live_context_before else {}
            logger.info(f"  - Using GLOBAL values (no scope)")

        if scope_id and live_context_after:
            scoped_after = getattr(live_context_after, 'scoped_values', {})
            live_ctx_after = scoped_after.get(scope_id, {})
        else:
            live_ctx_after = getattr(live_context_after, 'values', {}) if live_context_after else {}

        # DEBUG: Log what's in the live context values
        logger.debug(f"🔍 _check_with_batch_resolution: live_ctx_before types: {list(live_ctx_before.keys())}")
        logger.debug(f"🔍 _check_with_batch_resolution: live_ctx_after types: {list(live_ctx_after.keys())}")
        from openhcs.core.config import PipelineConfig

        # DEBUG: Log PipelineConfig values if present
        if PipelineConfig in live_ctx_before:
            pc_before = live_ctx_before[PipelineConfig]
            logger.debug(f"🔍 _check_with_batch_resolution: live_ctx_before[PipelineConfig]['well_filter_config'] = {pc_before.get('well_filter_config', 'NOT FOUND')}")
        if PipelineConfig in live_ctx_after:
            pc_after = live_ctx_after[PipelineConfig]
            logger.debug(f"🔍 _check_with_batch_resolution: live_ctx_after[PipelineConfig]['well_filter_config'] = {pc_after.get('well_filter_config', 'NOT FOUND')}")



        # Group identifiers by parent object path
        # e.g., {'fiji_streaming_config': ['well_filter'], 'napari_streaming_config': ['well_filter']}
        parent_to_attrs = {}
        simple_attrs = []

        for identifier in identifiers:
            if not identifier:
                continue

            parts = identifier.split('.')
            if len(parts) == 1:
                # Simple attribute on root object
                simple_attrs.append(parts[0])
            else:
                # Nested attribute - group by parent path
                parent_path = '.'.join(parts[:-1])
                attr_name = parts[-1]
                if parent_path not in parent_to_attrs:
                    parent_to_attrs[parent_path] = []
                parent_to_attrs[parent_path].append(attr_name)

        logger.debug(f"🔍 _check_with_batch_resolution: simple_attrs={simple_attrs}")
        logger.debug(f"🔍 _check_with_batch_resolution: parent_to_attrs={parent_to_attrs}")

        # Batch resolve simple attributes on root object
        # Use resolve_all_config_attrs() instead of resolve_all_lazy_attrs() to handle
        # inherited attributes (e.g., well_filter_config inherited from pipeline_config)
        if simple_attrs:
            before_attrs = resolver.resolve_all_config_attrs(
                obj_before, list(simple_attrs), context_stack_before, live_ctx_before, token_before
            )
            after_attrs = resolver.resolve_all_config_attrs(
                obj_after, list(simple_attrs), context_stack_after, live_ctx_after, token_after
            )

            # DEBUG: Log resolved values
            logger.debug(f"🔍 _check_with_batch_resolution: Resolved {len(before_attrs)} before attrs, {len(after_attrs)} after attrs")
            # Only log well_filter_config to reduce noise
            if 'well_filter_config' in simple_attrs:
                if 'well_filter_config' in before_attrs:
                    logger.debug(f"🔍 _check_with_batch_resolution: before[well_filter_config] = {before_attrs['well_filter_config']}")
                if 'well_filter_config' in after_attrs:
                    logger.debug(f"🔍 _check_with_batch_resolution: after[well_filter_config] = {after_attrs['well_filter_config']}")

            for attr_name in simple_attrs:
                if attr_name in before_attrs and attr_name in after_attrs:
                    logger.info(f"🔍 _check_with_batch_resolution: Comparing {attr_name}:")
                    logger.info(f"    before = {before_attrs[attr_name]}")
                    logger.info(f"    after  = {after_attrs[attr_name]}")
                    if before_attrs[attr_name] != after_attrs[attr_name]:
                        logger.info(f"    ✅ CHANGED!")
                        return True
                    else:
                        logger.info(f"    ❌ NO CHANGE")
                else:
                    logger.info(f"🔍 _check_with_batch_resolution: Skipping {attr_name} (not in both before/after)")

        # Batch resolve nested attributes grouped by parent
        for parent_path, attr_names in parent_to_attrs.items():
            logger.debug(f"🔍 _check_with_batch_resolution: Processing parent_path={parent_path}, attr_names={attr_names}")
            # Walk to parent object
            parent_before = obj_before
            parent_after = obj_after

            for part in parent_path.split('.'):
                parent_before = getattr(parent_before, part, None) if parent_before else None
                parent_after = getattr(parent_after, part, None) if parent_after else None

            if parent_before is None or parent_after is None:
                logger.debug(f"🔍 _check_with_batch_resolution: Skipping parent_path={parent_path} (parent is None)")
                continue

            # Batch resolve all attributes on this parent object
            before_attrs = resolver.resolve_all_lazy_attrs(
                parent_before, context_stack_before, live_ctx_before, token_before
            )
            after_attrs = resolver.resolve_all_lazy_attrs(
                parent_after, context_stack_after, live_ctx_after, token_after
            )

            logger.debug(f"🔍 _check_with_batch_resolution: Resolved {len(before_attrs)} before attrs, {len(after_attrs)} after attrs for parent_path={parent_path}")

            # Only log well_filter_config to reduce noise
            if 'well_filter_config' in attr_names:
                if 'well_filter_config' in before_attrs:
                    logger.debug(f"🔍 _check_with_batch_resolution: parent before[well_filter_config] = {before_attrs['well_filter_config']}")
                if 'well_filter_config' in after_attrs:
                    logger.debug(f"🔍 _check_with_batch_resolution: parent after[well_filter_config] = {after_attrs['well_filter_config']}")

            for attr_name in attr_names:
                if attr_name in before_attrs and attr_name in after_attrs:
                    logger.info(f"🔍 _check_with_batch_resolution: Comparing {parent_path}.{attr_name}:")
                    logger.info(f"    before = {before_attrs[attr_name]}")
                    logger.info(f"    after  = {after_attrs[attr_name]}")
                    if before_attrs[attr_name] != after_attrs[attr_name]:
                        logger.info(f"    ✅ CHANGED!")
                        return True
                    else:
                        logger.info(f"    ❌ NO CHANGE")
                else:
                    logger.info(f"🔍 _check_with_batch_resolution: Skipping {parent_path}.{attr_name} (not in both before/after)")

        logger.info(f"🔍 _check_with_batch_resolution: Final result = False (no changes detected)")
        return False

    def _expand_identifiers_for_inheritance(
        self,
        obj: Any,
        changed_fields: Set[str],
        live_context_snapshot,
    ) -> Set[str]:
        """Expand field identifiers to include fields that inherit from changed types.

        For example, if "well_filter_config.well_filter" changed, and obj has a field
        "step_well_filter_config" that is a subclass of WellFilterConfig, this will
        add "step_well_filter_config.well_filter" to the set.

        Only checks fields that could possibly be affected - i.e., dataclass fields on obj
        that are instances of (or subclasses of) the changed config type.

        Args:
            obj: Object to check for inheriting fields (e.g., Step preview instance)
            changed_fields: Original set of changed field identifiers
            live_context_snapshot: Live context for type resolution
            original_obj: Original object before live context merge (to check for override values)

        Returns:
            Expanded set of identifiers including inherited fields
        """
        from dataclasses import fields as dataclass_fields, is_dataclass

        expanded = set()

        logger.debug(f"🔍 _expand_identifiers_for_inheritance: obj type={type(obj).__name__}")
        logger.debug(f"🔍 _expand_identifiers_for_inheritance: changed_fields={changed_fields}")

        # For each changed field, check if it's a nested dataclass field
        for identifier in changed_fields:
            if "." not in identifier:
                # Simple field name - could be either:
                # 1. A dataclass attribute on obj (e.g., "napari_streaming_config")
                # 2. A simple field name (e.g., "well_filter", "enabled")

                # Case 1: Check if identifier is a direct attribute on obj
                # This includes both dataclass attributes AND simple fields like num_workers
                try:
                    attr_value = getattr(obj, identifier, None)
                    if attr_value is not None and is_dataclass(attr_value):
                        # This is a whole dataclass - keep it as-is
                        expanded.add(identifier)
                        continue
                    elif hasattr(obj, identifier):
                        # This is a direct field on obj (like num_workers on PipelineConfig)
                        expanded.add(identifier)
                        logger.debug(f"🔍 Added direct field '{identifier}' to expanded set")
                        continue
                except (AttributeError, Exception):
                    pass

                # Case 2: Check ALL dataclass attributes on obj for this simple field name
                # This expands simple field names like "well_filter" to "well_filter_config.well_filter"
                # We do NOT add the simple field name itself to expanded - only the expanded versions
                for attr_name in dir(obj):
                    if attr_name.startswith('_'):
                        continue
                    try:
                        attr_value = getattr(obj, attr_name, None)
                    except (AttributeError, Exception):
                        continue
                    if attr_value is None or not is_dataclass(attr_value):
                        continue
                    # Check if this dataclass has the simple field
                    if hasattr(attr_value, identifier):
                        expanded_identifier = f"{attr_name}.{identifier}"
                        if expanded_identifier not in expanded:
                            expanded.add(expanded_identifier)
                            logger.debug(f"🔍 Expanded '{identifier}' to include '{expanded_identifier}' (dataclass has field '{identifier}')")

                # NOTE: We do NOT add the simple field name to expanded if it's not a direct attribute
                # Simple field names like "well_filter" should only appear as nested fields like "well_filter_config.well_filter"
                continue

            # Parse identifier: could be "well_filter_config.well_filter" or "PipelineConfig.well_filter_config"
            parts = identifier.split(".")

            # Handle different cases:
            # 1. "well_filter_config" (1 part) - direct dataclass attribute
            # 2. "well_filter_config.well_filter" (2 parts) - nested field in dataclass
            # 3. "PipelineConfig.well_filter_config" (2 parts) - field from parent config type
            # 4. "pipeline_config.well_filter_config.well_filter" (3 parts) - nested field in parent config

            if len(parts) == 1:
                # Simple dataclass attribute - already handled above
                expanded.add(identifier)
                continue
            elif len(parts) == 2:
                # Could be either:
                # - "well_filter_config.well_filter" (dataclass.field)
                # - "PipelineConfig.well_filter_config" (ParentType.field)

                first_part = parts[0]
                second_part = parts[1]

                # Check if first_part is a type name (starts with uppercase) or canonical root name
                # Canonical root names are lowercase versions of type names (e.g., "pipeline_config" for "PipelineConfig")
                is_type_or_root = first_part[0].isupper() or first_part in self._preview_scope_aliases.values()

                if is_type_or_root:
                    # This is "ParentType.field" format (e.g., "PipelineConfig.well_filter_config")
                    # We need to find attributes on obj whose TYPE matches the field type
                    # For example: PipelineConfig.well_filter_config -> find step_well_filter_config (StepWellFilterConfig inherits from WellFilterConfig)

                    logger.debug(f"🔍 Processing ParentType.field format: {identifier}")

                    # CRITICAL: Always add the original identifier to expanded set
                    # This ensures scoped identifiers like "step.step_well_filter_config" are preserved
                    expanded.add(identifier)

                    # Get the type and value of the field from live context
                    field_type = None
                    field_value = None
                    if live_context_snapshot:
                        live_values = getattr(live_context_snapshot, 'values', {})
                        scoped_values = getattr(live_context_snapshot, 'scoped_values', {})

                        logger.debug(f"🔍   live_values types: {[t.__name__ for t in live_values.keys()]}")
                        logger.debug(f"🔍   scoped_values keys: {list(scoped_values.keys())}")

                        # Check both global and scoped values
                        all_values = dict(live_values)
                        for scope_dict in scoped_values.values():
                            all_values.update(scope_dict)

                        for type_key, values_dict in all_values.items():
                            if second_part in values_dict:
                                # Get the type of this field's value
                                field_value = values_dict[second_part]
                                logger.debug(f"🔍   Found field '{second_part}' in type {type_key.__name__}: {field_value}")
                                if field_value is not None and is_dataclass(field_value):
                                    field_type = type(field_value)
                                    logger.debug(f"🔍   field_type = {field_type.__name__}")
                                    break

                    # Find all dataclass attributes on obj whose TYPE inherits from field_type
                    # AND expand to include ALL fields inside the dataclass
                    if field_type:
                        from dataclasses import fields as dataclass_fields

                        # Get all field names from the dataclass
                        nested_field_names = []
                        if field_value is not None:
                            try:
                                nested_field_names = [f.name for f in dataclass_fields(field_value)]
                                logger.debug(f"🔍   nested_field_names = {nested_field_names}")
                            except Exception as e:
                                logger.debug(f"🔍   Failed to get nested fields: {e}")

                        for attr_name in dir(obj):
                            if attr_name.startswith('_'):
                                continue
                            try:
                                attr_value = getattr(obj, attr_name, None)
                            except (AttributeError, Exception):
                                continue
                            if attr_value is None or not is_dataclass(attr_value):
                                continue

                            attr_type = type(attr_value)
                            # Check if attr_type inherits from field_type
                            try:
                                if issubclass(attr_type, field_type) or issubclass(field_type, attr_type):
                                    # Add nested fields (e.g., step_well_filter_config.well_filter)
                                    # instead of just the dataclass attribute (step_well_filter_config)
                                    for nested_field in nested_field_names:
                                        nested_identifier = f"{attr_name}.{nested_field}"
                                        if nested_identifier not in expanded:
                                            expanded.add(nested_identifier)
                                            logger.debug(f"🔍 Expanded '{identifier}' to include '{nested_identifier}' ({attr_type.__name__} inherits from {field_type.__name__})")
                            except TypeError:
                                # issubclass can raise TypeError if types are not classes
                                pass
                    else:
                        logger.debug(f"🔍   field_type is None, skipping expansion")
                    continue
                else:
                    # This is "dataclass.field" format (e.g., "well_filter_config.well_filter")
                    config_field_name = first_part
                    nested_attr = second_part

                    # Try to get the config from obj
                    config_type = None
                    try:
                        config_value = getattr(obj, config_field_name, None)
                        if config_value is not None and is_dataclass(config_value):
                            config_type = type(config_value)
                            # Add the original identifier
                            expanded.add(identifier)
                    except (AttributeError, Exception):
                        pass

                    # Find ALL dataclass attributes on obj that have this nested attribute
                    # and whose TYPE inherits from config_type (if we know it)
                    for attr_name in dir(obj):
                        if attr_name.startswith('_'):
                            continue
                        try:
                            attr_value = getattr(obj, attr_name, None)
                        except (AttributeError, Exception):
                            continue
                        if attr_value is None or not is_dataclass(attr_value):
                            continue
                        if not hasattr(attr_value, nested_attr):
                            continue

                        attr_type = type(attr_value)
                        # If we know the config_type, check inheritance; otherwise just check if it has the field
                        if config_type is None or issubclass(attr_type, config_type) or issubclass(config_type, attr_type):
                            expanded_identifier = f"{attr_name}.{nested_attr}"
                            if expanded_identifier not in expanded:
                                expanded.add(expanded_identifier)
                                if config_type:
                                    logger.debug(f"🔍 Expanded '{identifier}' to include '{expanded_identifier}' ({attr_type.__name__} inherits from {config_type.__name__})")
                                else:
                                    logger.debug(f"🔍 Expanded '{identifier}' to include '{expanded_identifier}' (has field '{nested_attr}')")
            else:
                # 3+ parts - just keep the original identifier
                expanded.add(identifier)

        return expanded

    def _build_flash_context_stack(
        self,
        obj: Any,
        live_context_snapshot,
    ) -> Optional[list]:
        """Build context stack for flash resolution.

        Subclasses can override to provide context-aware resolution through
        config hierarchy (e.g., GlobalPipelineConfig → PipelineConfig → Step).

        Args:
            obj: Object to build context stack for (preview instance)
            live_context_snapshot: Live context snapshot for resolution

        Returns:
            List of context objects for resolution, or None to use simple walk
        """
        return None  # Base implementation: no context resolution

    def _resolve_flash_field_value(
        self,
        obj: Any,
        identifier: str,
        live_context_snapshot,
    ) -> Any:
        """Resolve a field identifier for flash detection.

        Uses context-aware resolution if subclass provides context stack,
        otherwise falls back to simple object graph walk.

        Args:
            obj: Object to resolve field from (preview instance)
            identifier: Dot-separated field path
            live_context_snapshot: Live context snapshot for resolution

        Returns:
            Resolved field value
        """
        # Try context-aware resolution first
        context_stack = self._build_flash_context_stack(obj, live_context_snapshot)

        if context_stack:
            # Resolve through context hierarchy
            return self._resolve_through_context_stack(
                obj, identifier, context_stack, live_context_snapshot
            )

        # Fallback to simple walk
        return self._walk_object_path(obj, identifier)

    def _resolve_through_context_stack(
        self,
        obj: Any,
        identifier: str,
        context_stack: list,
        live_context_snapshot,
    ) -> Any:
        """Resolve field through context stack using LiveContextResolver.

        Args:
            obj: Object to resolve field from
            identifier: Dot-separated field path (e.g., "napari_streaming_config.enabled")
            context_stack: List of context objects for resolution
            live_context_snapshot: Live context snapshot

        Returns:
            Resolved field value
        """
        from openhcs.config_framework import LiveContextResolver

        # Get or create resolver instance
        resolver = getattr(self, '_live_context_resolver', None)
        if resolver is None:
            resolver = LiveContextResolver()

        # Parse identifier into object path and attribute name
        # e.g., "napari_streaming_config.enabled" → walk to napari_streaming_config, resolve "enabled"
        parts = [p for p in identifier.split(".") if p]
        if not parts:
            return None

        # Walk to the config object (all parts except last)
        config_obj = obj
        for part in parts[:-1]:
            if config_obj is None:
                return None
            try:
                config_obj = getattr(config_obj, part)
            except AttributeError:
                return None

        # Resolve the final attribute through context
        attr_name = parts[-1]

        try:
            live_context_values = live_context_snapshot.values if hasattr(live_context_snapshot, 'values') else {}
            cache_token = live_context_snapshot.token if hasattr(live_context_snapshot, 'token') else 0

            resolved_value = resolver.resolve_config_attr(
                config_obj=config_obj,
                attr_name=attr_name,
                context_stack=context_stack,
                live_context=live_context_values,
                cache_token=cache_token
            )
            return resolved_value
        except Exception:
            # Fallback to simple getattr
            return self._walk_object_path(obj, identifier)

    def _walk_object_path(self, obj: Any, path: str) -> Any:
        """Walk object graph using dotted path notation.

        Simple getattr walk with no resolution logic. Used for comparing
        preview instances that are already fully resolved.

        Args:
            obj: Object to walk (should be a preview instance)
            path: Dot-separated path (e.g., "processing_config.num_workers")

        Returns:
            Value at the path, or None if path doesn't exist
        """
        if obj is None or not path:
            return None

        parts = [part for part in path.split(".") if part]
        if not parts:
            return obj

        target = obj
        for part in parts:
            if target is None:
                return None
            if isinstance(target, dict):
                target = target.get(part)
                continue
            try:
                target = getattr(target, part)
            except AttributeError:
                return None

        return target

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
