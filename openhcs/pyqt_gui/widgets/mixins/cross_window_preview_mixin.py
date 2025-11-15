"""Mixin for widgets that consume cross-window ParameterFormManager updates."""

from __future__ import annotations

from typing import Any, Dict, Hashable, Optional, Set


class CrossWindowPreviewMixin:
    """Shared helpers for windows that respond to cross-window preview updates."""

    def _init_cross_window_preview_mixin(self) -> None:
        self._preview_scope_map: Dict[str, Hashable] = {}
        self._pending_preview_keys: Set[Hashable] = set()

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

    # --- Event routing ---------------------------------------------------------
    def handle_cross_window_preview_change(
        self,
        field_path: Optional[str],
        new_value: Any,
        editing_object: Any,
        context_object: Any,
    ) -> None:
        """Shared handler to route cross-window updates to incremental refreshes."""
        import logging
        logger = logging.getLogger(__name__)

        if not self._should_process_preview_field(
            field_path, new_value, editing_object, context_object
        ):
            return

        scope_id = self._extract_scope_id_for_preview(editing_object, context_object)

        # Special markers for config changes that affect all steps
        if scope_id in ("PIPELINE_CONFIG_CHANGE", "GLOBAL_CONFIG_CHANGE"):
            # Refresh ALL steps (add all indices to pending updates)
            all_indices = [idx for idx in self._preview_scope_map.values() if isinstance(idx, int)]
            for idx in all_indices:
                self._pending_preview_keys.add(idx)
            self._process_pending_preview_updates()
        elif scope_id and scope_id in self._preview_scope_map:
            item_key = self._preview_scope_map[scope_id]
            self._pending_preview_keys.add(item_key)
            self._process_pending_preview_updates()
        else:
            self._handle_full_preview_refresh()

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
