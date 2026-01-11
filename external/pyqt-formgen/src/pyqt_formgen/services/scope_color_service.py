"""Reactive service for scope-based colors with strategy support."""

from typing import Optional, Dict, Tuple
from PyQt6.QtCore import QObject, pyqtSignal
import logging

from pyqt_formgen.widgets.shared.scope_color_strategy import (
    ScopeColorStrategy,
    IndexBasedStrategy,
    MD5HashStrategy,
    ManualColorStrategy,
    ColorStrategyType,
)

logger = logging.getLogger(__name__)


class ScopeColorService(QObject):
    """Singleton service managing scope colors with caching and signals."""

    color_changed = pyqtSignal(str)
    all_colors_reset = pyqtSignal()

    _instance: Optional["ScopeColorService"] = None

    @classmethod
    def instance(cls) -> "ScopeColorService":
        if cls._instance is None:
            cls._instance = cls()
        return cls._instance

    @classmethod
    def reset_instance(cls) -> None:
        cls._instance = None

    def __init__(self):
        super().__init__()
        self._strategies: Dict[ColorStrategyType, ScopeColorStrategy] = {
            ColorStrategyType.INDEX_BASED: IndexBasedStrategy(),
            ColorStrategyType.MD5_HASH: MD5HashStrategy(),
            ColorStrategyType.MANUAL: ManualColorStrategy(),
        }
        self._active_strategy_type = ColorStrategyType.INDEX_BASED  # Use index-based by default
        self._scheme_cache: Dict = {}  # Mixed key types: str or (str, int)

    @property
    def active_strategy(self) -> ScopeColorStrategy:
        return self._strategies[self._active_strategy_type]

    def set_strategy(self, strategy_type: ColorStrategyType) -> None:
        if strategy_type != self._active_strategy_type:
            self._active_strategy_type = strategy_type
            self._invalidate_all()
            logger.info("Color strategy changed to %s", strategy_type.name)

    def register_strategy(self, strategy: ScopeColorStrategy) -> None:
        self._strategies[strategy.strategy_type] = strategy
        logger.info("Registered color strategy: %s", strategy.strategy_type.name)

    def get_color_scheme(
        self, scope_id: Optional[str], step_index: Optional[int] = None
    ) -> "ScopeColorScheme":
        """Get color scheme for scope.

        Args:
            scope_id: The scope identifier
            step_index: Optional explicit step index (position in pipeline).
                        If provided, uses this for border pattern instead of
                        extracting from scope_id. Cache key includes index.
        """
        from pyqt_formgen.widgets.shared.scope_color_utils import (
            _build_color_scheme_from_rgb,
            extract_orchestrator_scope,
        )
        from pyqt_formgen.widgets.shared.scope_visual_config import ScopeColorScheme

        if scope_id is None:
            return self._get_neutral_scheme()

        # For orchestrator-level scopes (no "::"), ignore step_index in cache key
        # since orchestrator-level uses fixed tint regardless of step_index.
        # This ensures plate list items and their config windows share the same scheme.
        is_orchestrator_level = "::" not in (scope_id or "")
        if is_orchestrator_level:
            cache_key = scope_id
        else:
            cache_key = (scope_id, step_index) if step_index is not None else scope_id

        if cache_key not in self._scheme_cache:
            orchestrator_scope = extract_orchestrator_scope(scope_id) or scope_id
            # Pass step_index (used by some strategies, ignored by orchestrator-based)
            rgb = self.active_strategy.generate_color(orchestrator_scope, step_index=step_index)
            self._scheme_cache[cache_key] = _build_color_scheme_from_rgb(
                rgb, scope_id, step_index=step_index
            )
        return self._scheme_cache[cache_key]

    def _get_neutral_scheme(self) -> "ScopeColorScheme":
        from pyqt_formgen.widgets.shared.scope_visual_config import ScopeColorScheme

        return ScopeColorScheme(
            scope_id=None,
            hue=0,
            orchestrator_item_bg_rgb=(240, 240, 240),
            orchestrator_item_border_rgb=(180, 180, 180),
            step_window_border_rgb=(128, 128, 128),
            step_item_bg_rgb=(245, 245, 245),
            step_border_width=0,
        )

    def set_manual_color(self, scope_id: str, rgb: Tuple[int, int, int]) -> None:
        manual = self._strategies[ColorStrategyType.MANUAL]
        if isinstance(manual, ManualColorStrategy):
            manual.set_color(scope_id, rgb)
            self._invalidate(scope_id)

    def clear_manual_color(self, scope_id: str) -> None:
        manual = self._strategies[ColorStrategyType.MANUAL]
        if isinstance(manual, ManualColorStrategy):
            manual.clear_color(scope_id)
            self._invalidate(scope_id)

    def _invalidate(self, scope_id: str) -> None:
        keys_to_remove = [
            k for k in self._scheme_cache if k == scope_id or k.startswith(f"{scope_id}::")
        ]
        for key in keys_to_remove:
            self._scheme_cache.pop(key, None)
        self.color_changed.emit(scope_id)

    def _invalidate_all(self) -> None:
        self._scheme_cache.clear()
        self.all_colors_reset.emit()
