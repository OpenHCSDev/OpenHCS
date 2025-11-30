"""Reactive service for scope-based colors with strategy support.

Singleton service that:
- Manages color generation strategies (pluggable)
- Caches color schemes for performance
- Emits signals when colors change (reactive updates)
- Supports manual color overrides for future right-click menu
"""

from typing import Optional, Dict, Tuple
from PyQt6.QtCore import QObject, pyqtSignal
import logging

from openhcs.pyqt_gui.widgets.shared.scope_color_strategy import (
    ScopeColorStrategy, MD5HashStrategy, ManualColorStrategy, ColorStrategyType
)

logger = logging.getLogger(__name__)


class ScopeColorService(QObject):
    """Singleton service managing scope colors with reactive updates.

    Emits signals when colors change, allowing widgets to update reactively.
    Supports pluggable strategies and manual overrides.
    
    Usage:
        service = ScopeColorService.instance()
        scheme = service.get_color_scheme(scope_id)
        
        # Subscribe to changes
        service.color_changed.connect(my_widget.on_color_changed)
        
        # Manual color override (future right-click menu)
        service.set_manual_color(scope_id, (255, 0, 0))
    """

    # Signals for reactive updates
    color_changed = pyqtSignal(str)     # scope_id changed
    all_colors_reset = pyqtSignal()     # bulk reset (strategy change)

    _instance: Optional['ScopeColorService'] = None

    @classmethod
    def instance(cls) -> 'ScopeColorService':
        """Get singleton instance."""
        if cls._instance is None:
            cls._instance = cls()
        return cls._instance

    @classmethod
    def reset_instance(cls) -> None:
        """Reset singleton (for testing)."""
        cls._instance = None

    def __init__(self):
        super().__init__()
        self._strategies: Dict[ColorStrategyType, ScopeColorStrategy] = {
            ColorStrategyType.MD5_HASH: MD5HashStrategy(),
            ColorStrategyType.MANUAL: ManualColorStrategy(),
        }
        self._active_strategy_type = ColorStrategyType.MD5_HASH
        self._scheme_cache: Dict[str, 'ScopeColorScheme'] = {}

    # === Strategy Management ===

    @property
    def active_strategy(self) -> ScopeColorStrategy:
        """Get currently active strategy."""
        return self._strategies[self._active_strategy_type]

    def set_strategy(self, strategy_type: ColorStrategyType) -> None:
        """Switch active color generation strategy."""
        if strategy_type != self._active_strategy_type:
            self._active_strategy_type = strategy_type
            self._invalidate_all()
            logger.info(f"Color strategy changed to {strategy_type.name}")

    def register_strategy(self, strategy: ScopeColorStrategy) -> None:
        """Register custom strategy."""
        self._strategies[strategy.strategy_type] = strategy
        logger.info(f"Registered color strategy: {strategy.strategy_type.name}")

    # === Color Access (cached) ===

    def get_color_scheme(self, scope_id: Optional[str]) -> 'ScopeColorScheme':
        """Get color scheme for scope. Cached and reactive."""
        # Import here to avoid circular dependency
        from openhcs.pyqt_gui.widgets.shared.scope_color_utils import (
            _build_color_scheme_from_rgb,
            extract_orchestrator_scope,
        )

        if scope_id is None:
            return self._get_neutral_scheme()

        if scope_id not in self._scheme_cache:
            # Get base color from strategy
            orchestrator_scope = extract_orchestrator_scope(scope_id)
            rgb = self.active_strategy.generate_color(orchestrator_scope)
            # Build full scheme with all derived colors
            self._scheme_cache[scope_id] = _build_color_scheme_from_rgb(rgb, scope_id)

        return self._scheme_cache[scope_id]

    def _get_neutral_scheme(self) -> 'ScopeColorScheme':
        """Get neutral gray scheme for None scope."""
        from openhcs.pyqt_gui.widgets.shared.scope_visual_config import ScopeColorScheme
        return ScopeColorScheme(
            scope_id=None,
            hue=0,
            orchestrator_item_bg_rgb=(240, 240, 240),
            orchestrator_item_border_rgb=(180, 180, 180),
            step_window_border_rgb=(128, 128, 128),
            step_item_bg_rgb=(245, 245, 245),
            step_border_width=0,
        )

    # === Manual Color API ===

    def set_manual_color(self, scope_id: str, rgb: Tuple[int, int, int]) -> None:
        """Set manual color override for scope."""
        manual = self._strategies[ColorStrategyType.MANUAL]
        if isinstance(manual, ManualColorStrategy):
            manual.set_color(scope_id, rgb)
            self._invalidate(scope_id)
            logger.debug(f"Set manual color for {scope_id}: {rgb}")

    def clear_manual_color(self, scope_id: str) -> None:
        """Clear manual override, revert to generated color."""
        manual = self._strategies[ColorStrategyType.MANUAL]
        if isinstance(manual, ManualColorStrategy):
            manual.clear_color(scope_id)
            self._invalidate(scope_id)
            logger.debug(f"Cleared manual color for {scope_id}")

    # === Cache Invalidation + Signals ===

    def _invalidate(self, scope_id: str) -> None:
        """Invalidate cache and emit change signal."""
        # Invalidate this scope and any step scopes derived from it
        keys_to_remove = [k for k in self._scheme_cache if k == scope_id or k.startswith(f"{scope_id}::")]
        for key in keys_to_remove:
            self._scheme_cache.pop(key, None)
        self.color_changed.emit(scope_id)

    def _invalidate_all(self) -> None:
        """Invalidate all and emit reset signal."""
        self._scheme_cache.clear()
        self.all_colors_reset.emit()

