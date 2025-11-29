"""
Unified Field Change Dispatcher.

Centralizes all field change handling into a single event-driven dispatcher.
Replaces callback spaghetti with a clean architecture.
"""
from __future__ import annotations

import logging
from dataclasses import dataclass
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

logger = logging.getLogger(__name__)

# Debug flag for verbose dispatcher logging
DEBUG_DISPATCHER = True


@dataclass
class FieldChangeEvent:
    """Immutable event representing a field change."""
    field_name: str                        # Leaf field name
    value: Any                             # New value
    source_manager: 'ParameterFormManager' # Where change originated
    is_reset: bool = False                 # True if this is a reset operation (don't track as user-set)


class FieldChangeDispatcher:
    """Singleton dispatcher for all field changes. Stateless."""

    _instance = None

    @classmethod
    def instance(cls) -> 'FieldChangeDispatcher':
        if cls._instance is None:
            cls._instance = cls()
        return cls._instance

    def dispatch(self, event: FieldChangeEvent) -> None:
        """Handle a field change event."""
        # PERFORMANCE OPTIMIZATION: Wrap entire dispatch in dispatch_cycle
        # This allows sibling refreshes to share cached GLOBAL layer in build_context_stack
        from openhcs.config_framework.context_manager import dispatch_cycle

        with dispatch_cycle():
            self._dispatch_impl(event)

    def _dispatch_impl(self, event: FieldChangeEvent) -> None:
        """Implementation of dispatch (wrapped in dispatch_cycle)."""
        source = event.source_manager

        if DEBUG_DISPATCHER:
            reset_tag = " [RESET]" if event.is_reset else ""
            logger.info(f"🚀 DISPATCH{reset_tag}: {source.field_id}.{event.field_name} = {repr(event.value)[:50]}")

        # Reentrancy guard
        if getattr(source, '_dispatching', False):
            if DEBUG_DISPATCHER:
                logger.warning(f"🚫 DISPATCH BLOCKED: {source.field_id} already dispatching (reentrancy guard)")
            return
        source._dispatching = True

        try:
            if source._in_reset:
                if DEBUG_DISPATCHER:
                    logger.warning(f"🚫 DISPATCH BLOCKED: {source.field_id} has _in_reset=True")
                return

            # 1. Update source's data model
            source.parameters[event.field_name] = event.value
            # CRITICAL: Always add to _user_set_fields, even for reset
            # This ensures get_user_modified_values() includes None for reset fields,
            # so live context has the override and preview labels show same as placeholders.
            # Previously we discarded on reset, but that caused preview labels to show
            # the saved-on-disk value instead of the reset (None) value.
            source._user_set_fields.add(event.field_name)
            if DEBUG_DISPATCHER:
                reset_note = " (reset to None)" if event.is_reset else ""
                logger.info(f"  ✅ Updated source.parameters[{event.field_name}], ADDED to _user_set_fields{reset_note}")

            # PERFORMANCE OPTIMIZATION: Invalidate cache but DON'T notify listeners yet
            # This allows sibling refreshes to share the cached live context
            # (first sibling computes and caches, subsequent siblings get cache hits)
            # We notify listeners AFTER sibling refresh is complete
            root = source
            while root._parent_manager is not None:
                root = root._parent_manager

            from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService
            LiveContextService.increment_token(notify=False)  # Invalidate cache only
            if DEBUG_DISPATCHER:
                logger.info(f"  🔄 Incremented live context token to {LiveContextService.get_token()} (notify deferred)")

            # 2. Mark parent chain as modified BEFORE refreshing siblings
            # This ensures root.get_user_modified_values() includes this field on first keystroke
            self._mark_parents_modified(source)

            # 3. Refresh siblings that have the same field
            parent = source._parent_manager
            if parent:
                if DEBUG_DISPATCHER:
                    logger.info(f"  🔍 Looking for siblings with field '{event.field_name}' in {parent.field_id}")
                    logger.info(f"  🔍 Parent has {len(parent.nested_managers)} nested managers: {list(parent.nested_managers.keys())}")

                siblings_refreshed = 0
                for name, sibling in parent.nested_managers.items():
                    if sibling is source:
                        if DEBUG_DISPATCHER:
                            logger.debug(f"    ⏭️  Skipping {name} (is source)")
                        continue

                    # Check if sibling has the same field (simpler than isinstance for Lazy wrappers)
                    has_field = event.field_name in sibling.widgets

                    if DEBUG_DISPATCHER:
                        sibling_type = type(sibling.object_instance).__name__ if sibling.object_instance else 'None'
                        logger.info(f"    🔍 Sibling {name}: type={sibling_type}, has_field={has_field}")

                    if has_field:
                        self._refresh_single_field(sibling, event.field_name)
                        siblings_refreshed += 1

                if DEBUG_DISPATCHER:
                    logger.info(f"  ✅ Refreshed {siblings_refreshed} sibling(s)")
            else:
                if DEBUG_DISPATCHER:
                    logger.info(f"  ℹ️  No parent manager (root-level field)")

            # PERFORMANCE OPTIMIZATION: NOW notify listeners (after sibling refresh)
            # This allows sibling refreshes to share the cached live context
            root._block_cross_window_updates = True
            try:
                LiveContextService._notify_change()
                if DEBUG_DISPATCHER:
                    logger.info(f"  📣 Notified {len(LiveContextService._change_callbacks)} listeners")
            finally:
                root._block_cross_window_updates = False

            # 3. Handle 'enabled' field styling
            if event.field_name == 'enabled':
                source._enabled_field_styling_service.on_enabled_field_changed(
                    source, 'enabled', event.value
                )
                if DEBUG_DISPATCHER:
                    logger.info(f"  ✅ Applied enabled styling")

            # 4. Emit from ROOT with full path (for all listeners)
            # This ensures listeners connected to root get notified of ALL changes
            # (including nested) with full paths like "processing_config.group_by"
            root = self._get_root_manager(source)
            full_path = self._get_full_path(source, event.field_name)

            logger.info(f"🔔 DISPATCHER: Emitting parameter_changed from root")
            logger.info(f"  source.field_id={source.field_id}")
            logger.info(f"  root.field_id={root.field_id}")
            logger.info(f"  event.field_name={event.field_name}")
            logger.info(f"  full_path={full_path}")
            logger.info(f"  value type={type(event.value).__name__}")

            root.parameter_changed.emit(full_path, event.value)
            logger.info(f"  ✅ Emitted parameter_changed({full_path}, ...) from root")

            # 5. Emit cross-window signal from ROOT
            self._emit_cross_window(root, full_path, event.value)

        finally:
            source._dispatching = False

    def _mark_parents_modified(self, source: 'ParameterFormManager') -> None:
        """Mark parent chain as having modified nested config.

        This ensures get_user_modified_values() on root includes nested changes.
        Also updates parent.parameters with the nested dataclass value.
        """
        logger.info(f"  📝 MARK_PARENTS: Starting for {source.field_id}")

        current = source
        level = 0
        while current._parent_manager is not None:
            parent = current._parent_manager
            level += 1
            logger.info(f"    L{level}: parent={parent.field_id}")
            # Find the field name in parent that points to current
            for field_name, nested_mgr in parent.nested_managers.items():
                if nested_mgr is current:
                    logger.info(f"    L{level}: Found field_name={field_name} in parent")
                    # Collect nested value and update parent's parameters
                    nested_value = parent._value_collection_service.collect_nested_value(
                        parent, field_name, nested_mgr
                    )
                    logger.info(f"    L{level}: Collected nested_value type={type(nested_value).__name__}")
                    parent.parameters[field_name] = nested_value
                    parent._user_set_fields.add(field_name)
                    logger.info(f"    L{level}: ✅ {parent.field_id}.{field_name} marked modified")
                    break
            current = parent

        logger.info(f"  ✅ MARK_PARENTS: Complete")

    def _get_root_manager(self, manager: 'ParameterFormManager') -> 'ParameterFormManager':
        """Walk up to root manager."""
        current = manager
        while current._parent_manager is not None:
            current = current._parent_manager
        return current

    def _get_full_path(self, source: 'ParameterFormManager', field_name: str) -> str:
        """Build full path by walking up parent chain.

        Example: "GlobalPipelineConfig.pipeline_config.well_filter_config.well_filter"
        """
        parts = [field_name]
        current = source
        while current is not None:
            parts.insert(0, current.field_id)
            current = current._parent_manager
        return ".".join(parts)

    def _emit_cross_window(self, root_manager: 'ParameterFormManager', full_path: str, value: Any) -> None:
        """Emit context_value_changed from root with full field path."""
        if root_manager._should_skip_updates():
            if DEBUG_DISPATCHER:
                logger.warning(f"  🚫 Cross-window BLOCKED: _should_skip_updates()=True for {root_manager.field_id}")
            return
        if root_manager.config.is_global_config_editing:
            root_manager._update_thread_local_global_config()
            if DEBUG_DISPATCHER:
                logger.info(f"  🌐 Updated thread-local global config")

        if DEBUG_DISPATCHER:
            logger.info(f"  📡 Emitting cross-window: path={full_path}")

        root_manager.context_value_changed.emit(
            full_path,
            value,
            root_manager.object_instance,
            root_manager.context_obj,
            root_manager.scope_id
        )

    def _refresh_single_field(self, manager: 'ParameterFormManager', field_name: str) -> None:
        """Refresh just one field's placeholder in a sibling manager."""
        if DEBUG_DISPATCHER:
            logger.info(f"      🔄 _refresh_single_field: {manager.field_id}.{field_name}")

        if field_name not in manager.widgets:
            if DEBUG_DISPATCHER:
                logger.warning(f"      ⏭️  Field {field_name} not in widgets, skipping")
            return

        # FIX: Check current value instead of _user_set_fields.
        # Even if a field is in _user_set_fields, if its value is None it should
        # show a placeholder (inherited from parent). This is critical for code-mode
        # which sets all fields (adding them to _user_set_fields) but many have None
        # values that should display as placeholders.
        current_value = manager.parameters.get(field_name)
        if current_value is not None:
            if DEBUG_DISPATCHER:
                logger.info(f"      ⏭️  Field {field_name} has concrete value ({type(current_value).__name__}), skipping placeholder refresh")
            return

        if DEBUG_DISPATCHER:
            logger.info(f"      ✅ Refreshing placeholder for {manager.field_id}.{field_name}")

        manager._parameter_ops_service.refresh_single_placeholder(manager, field_name)

