# plan_06_animation_system.md
## Component: Animation System

### Objective
Extract the game-engine inspired flash animation system into `pyqt_formgen/animation/`. This provides visual feedback for value changes with O(1) per-window performance.

### Plan

1. **Extract FlashConfig** (`flash_config.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/flash_config.py`
   - Target: `pyqt_formgen/animation/flash_config.py`
   - Changes: None expected - review for OpenHCS imports
   - Contains:
     - `FlashConfig` dataclass with animation parameters
     - `get_flash_config()` singleton accessor
     - Color interpolation utilities

2. **Extract FlashMixin** (`flash_mixin.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/flash_mixin.py`
   - Target: `pyqt_formgen/animation/flash_mixin.py`
   - This is a large file (~1700 lines) with complex architecture
   - Changes:
     - Update import for flash_config
     - Ensure no OpenHCS-specific imports
   - Key classes:
     - `FlashMixin` - Mixin for widgets that support flash
     - `WindowFlashOverlay` - Per-window overlay for rendering
     - `GlobalFlashCoordinator` - 60fps tick coordinator
     - `OverlayGeometryCache` - Geometry caching

3. **Extract FlashOverlayOpenGL** (`flash_overlay_opengl.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/flash_overlay_opengl.py`
   - Target: `pyqt_formgen/animation/flash_overlay_opengl.py`
   - OpenGL-accelerated rendering for flash effects
   - Dependencies: PyQt6.QtOpenGL (optional)

4. **Define FlashableWidget protocol** (in protocols layer):
   - Add to `pyqt_formgen/protocols/widget_protocols.py`:
   ```python
   class FlashableWidget(ABC):
       @abstractmethod
       def trigger_flash(self, color: Optional[QColor] = None) -> None:
           """Trigger flash animation on this widget."""
           pass
   ```

5. **Update animation/__init__.py**:
   ```python
   from .flash_config import FlashConfig, get_flash_config
   from .flash_mixin import (
       FlashMixin, WindowFlashOverlay,
       GlobalFlashCoordinator, OverlayGeometryCache,
   )
   # Optional OpenGL support
   try:
       from .flash_overlay_opengl import FlashOverlayOpenGL
   except ImportError:
       FlashOverlayOpenGL = None
   ```

6. **Delete original files from OpenHCS**:
   - Delete `openhcs/pyqt_gui/widgets/shared/flash_config.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/flash_mixin.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/flash_overlay_opengl.py`

7. **Update all imports in OpenHCS**:
   - Replace `from openhcs.pyqt_gui.widgets.shared.flash_mixin import FlashMixin`
   - With `from pyqt_formgen.animation import FlashMixin`

8. **Write tests** in `tests/test_animation.py`:
   - Test FlashConfig color interpolation
   - Test FlashMixin flash triggering
   - Test GlobalFlashCoordinator tick timing

### Findings

**flash_config.py**:
- Need to review for imports

**flash_mixin.py** (1713 lines):
- Complex game-engine style architecture
- Imports flash_config from same directory
- Need to verify no OpenHCS-specific imports
- Key architectural features:
  - O(1) per window rendering
  - Batch color computation at 60fps
  - Unified geometry cache

**Architecture note**: This is a sophisticated animation system that could be a standalone package. For now, keeping it in pyqt_formgen as the animation subpackage.

### Implementation Draft
<!-- Only write code here AFTER smell loop passes -->

