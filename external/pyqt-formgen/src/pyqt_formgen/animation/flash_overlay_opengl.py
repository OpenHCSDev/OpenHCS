"""OpenGL-accelerated flash overlay implementation (EXPERIMENTAL).

GPU-accelerated rendering for WindowFlashOverlay using QOpenGLWidget.

STATUS: EXPERIMENTAL - Actually slower than QPainter in practice.
The overhead of GL context switching and buffer uploads exceeds the benefit
of instanced rendering for our typical workload (few rectangles, simple shapes).
QPainter's software rendering is already highly optimized for 2D overlays.

Keep use_opengl=False in FlashConfig unless explicitly benchmarking.
This module is preserved for future optimization attempts or workloads
with many more flash elements where instanced rendering may pay off.
"""

import logging
import struct
from typing import Dict, List, Optional, Set
import numpy as np

try:
    from PyQt6.QtWidgets import QWidget, QMainWindow, QDialog, QApplication
    from PyQt6.QtOpenGLWidgets import QOpenGLWidget
    from PyQt6.QtOpenGL import QOpenGLShaderProgram, QOpenGLShader, QOpenGLBuffer, QOpenGLVertexArrayObject
    from PyQt6.QtGui import QSurfaceFormat, QOpenGLContext, QMatrix4x4, QOffscreenSurface
    from PyQt6.QtCore import Qt, QRect
    from OpenGL import GL as gl
    OPENGL_AVAILABLE = True
except ImportError:
    OPENGL_AVAILABLE = False
    QOpenGLWidget = object  # Dummy for type checking

from .flash_mixin import FlashElement, OverlayGeometryCache

logger = logging.getLogger(__name__)


# ==================== SHARED GL CONTEXT POOL ====================
# Pre-warm OpenGL at app startup so window creation has zero delay

class _SharedGLContextManager:
    """Manages a pre-warmed shared OpenGL context.

    Benefits:
    - Driver initialization happens once at app startup (background)
    - All overlay widgets share this context (compiled shaders are cached)
    - New windows have zero GL initialization delay
    """
    _instance: Optional['_SharedGLContextManager'] = None

    @classmethod
    def get(cls) -> '_SharedGLContextManager':
        if cls._instance is None:
            cls._instance = cls()
        return cls._instance

    @classmethod
    def prewarm(cls) -> None:
        """Call at app startup to initialize GL in background."""
        if not OPENGL_AVAILABLE:
            return
        try:
            mgr = cls.get()
            if mgr._shared_context is None:
                mgr._initialize()
        except Exception as e:
            logger.warning(f"[OpenGL] Prewarm failed (non-fatal): {e}")

    def __init__(self):
        self._shared_context: Optional[QOpenGLContext] = None
        self._offscreen_surface: Optional[QOffscreenSurface] = None
        self._format: Optional[QSurfaceFormat] = None

    def _initialize(self):
        """Create shared context and compile shaders."""
        if not OPENGL_AVAILABLE:
            return

        # Create surface format
        self._format = QSurfaceFormat()
        self._format.setVersion(3, 3)
        self._format.setProfile(QSurfaceFormat.OpenGLContextProfile.CoreProfile)
        self._format.setSwapBehavior(QSurfaceFormat.SwapBehavior.DoubleBuffer)

        # Create offscreen surface for context
        self._offscreen_surface = QOffscreenSurface()
        self._offscreen_surface.setFormat(self._format)
        self._offscreen_surface.create()

        # Create shared context
        self._shared_context = QOpenGLContext()
        self._shared_context.setFormat(self._format)
        if not self._shared_context.create():
            logger.warning("[OpenGL] Failed to create shared context")
            self._shared_context = None
            return

        # Make current and do initial GL setup (warms up driver)
        if self._shared_context.makeCurrent(self._offscreen_surface):
            # Just making current warms up the driver
            self._shared_context.doneCurrent()
            logger.info("[OpenGL] Shared context pre-warmed successfully")
        else:
            logger.warning("[OpenGL] Could not make shared context current")

    def get_shared_context(self) -> Optional[QOpenGLContext]:
        """Get the shared context for context sharing."""
        if self._shared_context is None:
            self._initialize()
        return self._shared_context

    def get_format(self) -> Optional[QSurfaceFormat]:
        """Get the pre-configured surface format."""
        if self._format is None:
            self._initialize()
        return self._format


def prewarm_opengl() -> None:
    """Pre-warm OpenGL at app startup. Call from main window init."""
    _SharedGLContextManager.prewarm()

# Vertex shader: Transform rectangle corners
VERTEX_SHADER = """
#version 330 core

// Per-vertex data (quad corners: 0,0  1,0  0,1  1,1)
layout(location = 0) in vec2 corner;

// Per-instance data (one rectangle)
layout(location = 1) in vec4 rect;     // x, y, width, height
layout(location = 2) in vec4 color;    // r, g, b, a
layout(location = 3) in float radius;  // corner radius

// Output to fragment shader
out vec4 fragColor;
out vec2 fragPos;     // Position within rectangle (0,0 to width,height)
out vec2 fragSize;    // Rectangle size
out float fragRadius; // Corner radius

uniform mat4 projection;  // Window coords → normalized device coords

void main() {
    // Transform corner (0-1) to world position
    vec2 pos = rect.xy + corner * rect.zw;
    gl_Position = projection * vec4(pos, 0.0, 1.0);

    // Pass to fragment shader
    fragColor = color;
    fragPos = corner * rect.zw;
    fragSize = rect.zw;
    fragRadius = radius;
}
"""

# Fragment shader: Draw rounded rectangle with anti-aliasing
FRAGMENT_SHADER = """
#version 330 core

in vec4 fragColor;
in vec2 fragPos;
in vec2 fragSize;
in float fragRadius;

out vec4 outputColor;

void main() {
    // Signed distance field for rounded rectangle
    // https://iquilezles.org/articles/distfunctions2d/
    vec2 center = fragSize * 0.5;
    vec2 d = abs(fragPos - center) - (center - fragRadius);
    float dist = length(max(d, 0.0)) + min(max(d.x, d.y), 0.0) - fragRadius;

    // Anti-aliased edge (sub-pixel precision)
    float alpha = 1.0 - smoothstep(-0.5, 0.5, dist);

    outputColor = vec4(fragColor.rgb, fragColor.a * alpha);
}
"""


class WindowFlashOverlayGL(QOpenGLWidget if OPENGL_AVAILABLE else object):
    """GPU-accelerated flash overlay using OpenGL.

    Renders all flash rectangles in a single instanced draw call for maximum performance.
    Supports 144Hz+ refresh rates with negligible CPU overhead.

    Architecture:
    - One QOpenGLWidget per window (Qt manages context automatically)
    - Shaders compiled once on initialization
    - Rectangle data uploaded to GPU each frame
    - Single instanced draw call for all rectangles
    - Hardware alpha blending and anti-aliasing
    """

    # Class-level registry (same as WindowFlashOverlay)
    _overlays: Dict[int, 'WindowFlashOverlayGL'] = {}

    @classmethod
    def get_for_window(cls, widget: QWidget) -> Optional['WindowFlashOverlayGL']:
        """Get or create OpenGL overlay for window."""
        try:
            top_window = widget.window()

            if not isinstance(top_window, (QMainWindow, QDialog)):
                return None

            window_id = id(top_window)

            if window_id not in cls._overlays:
                overlay = cls(top_window)
                cls._overlays[window_id] = overlay
                logger.debug(f"[OpenGL] Created WindowFlashOverlayGL for window {window_id}")

            return cls._overlays[window_id]
        except RuntimeError:
            return None

    @classmethod
    def cleanup_window(cls, window: QWidget) -> None:
        """Remove overlay for window."""
        window_id = id(window.window())
        overlay = cls._overlays.pop(window_id, None)
        if overlay:
            elements_count = sum(len(v) for v in overlay._elements.values())
            overlay._elements.clear()
            overlay.deleteLater()
            logger.debug(f"[OpenGL] Cleaned up overlay for window {window_id}, cleared {elements_count} elements")

    def __init__(self, window: QWidget):
        # Use pre-warmed format if available, else create new
        mgr = _SharedGLContextManager.get()
        fmt = mgr.get_format()
        if fmt is None:
            fmt = QSurfaceFormat()
            fmt.setVersion(3, 3)
            fmt.setProfile(QSurfaceFormat.OpenGLContextProfile.CoreProfile)
            fmt.setSwapBehavior(QSurfaceFormat.SwapBehavior.DoubleBuffer)

        # Call parent constructor first
        super().__init__(window)

        # Set format and enable context sharing with pre-warmed context
        self.setFormat(fmt)
        shared_ctx = mgr.get_shared_context()
        if shared_ctx:
            # Share resources (compiled shaders, textures) with pre-warmed context
            self.context().setShareContext(shared_ctx) if self.context() else None

        self._window = window
        self._elements: Dict[str, List[FlashElement]] = {}
        self._cache = OverlayGeometryCache()

        # OpenGL resources (created in initializeGL)
        self._shader_program: Optional[QOpenGLShaderProgram] = None
        self._vao: Optional[QOpenGLVertexArrayObject] = None
        self._quad_vbo: Optional[QOpenGLBuffer] = None  # Quad corners (reused)
        self._instance_vbo: Optional[QOpenGLBuffer] = None  # Rectangle data (per frame)
        self._projection_matrix = QMatrix4x4()

        # Pre-allocated buffer for instance data (avoids per-frame allocation)
        self._max_instances = 256  # Max rectangles per frame
        self._instance_array = np.zeros(self._max_instances * 9, dtype=np.float32)
        self._instance_buffer_size = 0  # Current allocated GPU buffer size

        # Make overlay transparent and pass mouse events through
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        self.setAttribute(Qt.WidgetAttribute.WA_AlwaysStackOnTop)

        # Cover entire window
        self.setGeometry(window.rect())
        self.raise_()
        self.show()

        # Install event filters (same as QPainter version)
        self._install_scroll_event_filters()

        # Force early OpenGL initialization to avoid first-paint glitches
        # makeCurrent() triggers initializeGL if not yet called
        try:
            self.makeCurrent()
            self.doneCurrent()
            logger.debug("[OpenGL] Forced early GL initialization")
        except Exception as e:
            logger.warning(f"[OpenGL] Early init failed (non-fatal): {e}")

    def initializeGL(self):
        """Initialize OpenGL resources (called once on first show)."""
        logger.info("[OpenGL] Initializing flash overlay shaders")

        # Create shader program
        self._shader_program = QOpenGLShaderProgram(self)

        if not self._shader_program.addShaderFromSourceCode(
            QOpenGLShader.ShaderTypeBit.Vertex, VERTEX_SHADER
        ):
            logger.error(f"[OpenGL] Vertex shader compile failed: {self._shader_program.log()}")
            return

        if not self._shader_program.addShaderFromSourceCode(
            QOpenGLShader.ShaderTypeBit.Fragment, FRAGMENT_SHADER
        ):
            logger.error(f"[OpenGL] Fragment shader compile failed: {self._shader_program.log()}")
            return

        if not self._shader_program.link():
            logger.error(f"[OpenGL] Shader link failed: {self._shader_program.log()}")
            return

        logger.info("[OpenGL] Shaders compiled successfully")

        # Create VAO
        self._vao = QOpenGLVertexArrayObject(self)
        self._vao.create()
        self._vao.bind()

        # Create quad VBO (corners: 0,0  1,0  0,1  1,1)
        quad_data = np.array([
            0.0, 0.0,
            1.0, 0.0,
            0.0, 1.0,
            1.0, 1.0
        ], dtype=np.float32)

        self._quad_vbo = QOpenGLBuffer(QOpenGLBuffer.Type.VertexBuffer)
        self._quad_vbo.create()
        self._quad_vbo.bind()
        self._quad_vbo.allocate(quad_data.tobytes(), quad_data.nbytes)

        # Setup vertex attribute (location 0: corner)
        self._shader_program.bind()
        self._shader_program.enableAttributeArray(0)
        self._shader_program.setAttributeBuffer(0, gl.GL_FLOAT, 0, 2)

        # Create instance VBO with pre-allocated capacity
        self._instance_vbo = QOpenGLBuffer(QOpenGLBuffer.Type.VertexBuffer)
        self._instance_vbo.create()
        self._instance_vbo.bind()
        self._instance_vbo.setUsagePattern(QOpenGLBuffer.UsagePattern.DynamicDraw)
        # Pre-allocate with max capacity (9 floats per instance * 4 bytes * max_instances)
        self._instance_buffer_size = self._max_instances * 9 * 4
        self._instance_vbo.allocate(self._instance_buffer_size)

        # Setup instance attributes in VAO (done ONCE, not per frame!)
        # Stride = 36 bytes (9 floats * 4 bytes)
        stride = 36

        # Location 1: rect (vec4) - x, y, width, height
        self._shader_program.enableAttributeArray(1)
        gl.glVertexAttribPointer(1, 4, gl.GL_FLOAT, gl.GL_FALSE, stride, None)
        gl.glVertexAttribDivisor(1, 1)  # One per instance

        # Location 2: color (vec4) - r, g, b, a (offset 16 bytes)
        self._shader_program.enableAttributeArray(2)
        gl.glVertexAttribPointer(2, 4, gl.GL_FLOAT, gl.GL_FALSE, stride, gl.ctypes.c_void_p(16))
        gl.glVertexAttribDivisor(2, 1)

        # Location 3: radius (float) - corner radius (offset 32 bytes)
        self._shader_program.enableAttributeArray(3)
        gl.glVertexAttribPointer(3, 1, gl.GL_FLOAT, gl.GL_FALSE, stride, gl.ctypes.c_void_p(32))
        gl.glVertexAttribDivisor(3, 1)

        self._instance_vbo.release()
        self._vao.release()

        # Enable blending for transparency
        gl.glEnable(gl.GL_BLEND)
        gl.glBlendFunc(gl.GL_SRC_ALPHA, gl.GL_ONE_MINUS_SRC_ALPHA)

        logger.info("[OpenGL] Flash overlay initialized successfully")

    def resizeGL(self, w: int, h: int):
        """Update projection matrix on resize."""
        gl.glViewport(0, 0, w, h)

        # Orthographic projection: window coords (0,0 top-left) → NDC (-1,1)
        self._projection_matrix.setToIdentity()
        self._projection_matrix.ortho(0, w, h, 0, -1, 1)

        if self._shader_program:
            self._shader_program.bind()
            self._shader_program.setUniformValue("projection", self._projection_matrix)

        # Invalidate geometry cache on resize
        self._invalidate_geometry_cache()

    def paintGL(self):
        """GPU-accelerated paint - single draw call for ALL rectangles."""
        if self._shader_program is None or self._vao is None or self._instance_vbo is None:
            return

        gl.glClear(gl.GL_COLOR_BUFFER_BIT)

        # Get pre-computed colors from coordinator
        from .flash_mixin import _GlobalFlashCoordinator
        coordinator = _GlobalFlashCoordinator.get()
        if not coordinator._computed_colors:
            return

        # Rebuild geometry cache if invalidated
        if not self._cache.valid:
            clip_rects = self._get_scroll_area_clip_rects()
            self._rebuild_geometry_cache(clip_rects)

        # Fill pre-allocated array directly (no Python list, no allocation)
        idx = 0
        for key, color in coordinator._computed_colors.items():
            if key not in self._elements:
                continue

            cached_rects = self._cache.element_rects.get(key, [])
            for rect_tuple in cached_rects:
                if rect_tuple is None:
                    continue
                rect, radius = rect_tuple
                if rect is None or not rect.isValid():
                    continue

                # Check capacity
                if idx >= self._max_instances:
                    break

                # Pack directly into pre-allocated array
                base = idx * 9
                self._instance_array[base] = rect.x()
                self._instance_array[base + 1] = rect.y()
                self._instance_array[base + 2] = rect.width()
                self._instance_array[base + 3] = rect.height()
                self._instance_array[base + 4] = color.redF()
                self._instance_array[base + 5] = color.greenF()
                self._instance_array[base + 6] = color.blueF()
                self._instance_array[base + 7] = color.alphaF()
                self._instance_array[base + 8] = radius
                idx += 1

        if idx == 0:
            return

        num_instances = idx
        data_size = num_instances * 9 * 4  # 9 floats × 4 bytes

        # Bind VAO (attribute pointers already set up in initializeGL)
        self._vao.bind()
        self._shader_program.bind()
        self._instance_vbo.bind()

        # Upload instance data - numpy array is C-contiguous so this is fast
        # glBufferSubData accepts numpy array directly via PyOpenGL
        gl.glBufferSubData(gl.GL_ARRAY_BUFFER, 0, data_size, self._instance_array)

        # Draw ALL rectangles in ONE call
        gl.glDrawArraysInstanced(gl.GL_TRIANGLE_STRIP, 0, 4, num_instances)

    # ==================== CACHE AND ELEMENT MANAGEMENT ====================
    # Same methods as WindowFlashOverlay

    def register_element(self, element: FlashElement) -> None:
        """Register flashable element."""
        if element.key not in self._elements:
            self._elements[element.key] = []

        # Deduplicate by source_id
        if element.source_id is not None:
            for i, existing in enumerate(self._elements[element.key]):
                if existing.source_id == element.source_id:
                    self._elements[element.key][i] = element
                    return

        self._elements[element.key].append(element)

    def unregister_element(self, key: str) -> None:
        """Unregister element."""
        self._elements.pop(key, None)

    def _install_scroll_event_filters(self):
        """Install event filters on scroll areas."""
        from PyQt6.QtWidgets import QAbstractScrollArea
        self._window.installEventFilter(self)
        scroll_areas = self._window.findChildren(QAbstractScrollArea)
        for scroll_area in scroll_areas:
            if scroll_area.viewport():
                scroll_area.viewport().installEventFilter(self)

    def eventFilter(self, obj, event):
        """Catch scroll/resize events to invalidate cache."""
        from PyQt6.QtCore import QEvent
        if event.type() in (QEvent.Type.Resize, QEvent.Type.Wheel, QEvent.Type.Move, QEvent.Type.LayoutRequest):
            self._invalidate_geometry_cache()
            if obj is self._window and event.type() == QEvent.Type.Resize:
                self.setGeometry(self._window.rect())
        return super().eventFilter(obj, event)

    def _invalidate_geometry_cache(self):
        """Invalidate cached geometry."""
        self._cache.invalidate()

    def invalidate_cache(self):
        """Public method to invalidate cache."""
        self._invalidate_geometry_cache()

    def get_visible_keys_for(self, keys: Set[str]) -> Set[str]:
        """Get visible keys (same logic as WindowFlashOverlay)."""
        visible: Set[str] = set()

        if self._cache.valid:
            for key in keys:
                cached_rects = self._cache.element_rects.get(key, [])
                for rect_tuple in cached_rects:
                    if rect_tuple is None:
                        continue
                    rect, _ = rect_tuple
                    if rect is not None and rect.isValid() and rect.intersects(self.rect()):
                        visible.add(key)
                        break
        else:
            for key in keys:
                elements = self._elements.get(key)
                if not elements:
                    continue
                for element in elements:
                    try:
                        rect = element.get_rect_in_window(self._window)
                    except RuntimeError:
                        continue
                    if rect is not None and rect.isValid() and rect.intersects(self.rect()):
                        visible.add(key)
                        break
        return visible

    def _get_scroll_area_clip_rects(self) -> List[QRect]:
        """Get scroll area clip rects (same as WindowFlashOverlay)."""
        if self._cache.valid and self._cache.scroll_clip_rects:
            return self._cache.scroll_clip_rects

        from PyQt6.QtWidgets import QScrollArea
        clip_rects = []
        scroll_areas = self._window.findChildren(QScrollArea)
        for scroll_area in scroll_areas:
            viewport = scroll_area.viewport()
            if viewport and viewport.isVisible():
                viewport_rect = viewport.rect()
                global_pos = viewport.mapToGlobal(viewport_rect.topLeft())
                window_pos = self._window.mapFromGlobal(global_pos)
                clip_rects.append(QRect(window_pos, viewport_rect.size()))

        self._cache.scroll_clip_rects = clip_rects
        return clip_rects

    def _rebuild_geometry_cache(self, clip_rects: List[QRect]):
        """Rebuild geometry cache (same logic as WindowFlashOverlay)."""
        self._cache.element_rects.clear()
        self._cache.element_regions.clear()

        for key, elements in self._elements.items():
            rects = []
            regions = []

            for element in elements:
                if element.skip_overlay_paint:
                    rects.append(None)
                    regions.append(None)
                    continue

                rect = element.get_rect_in_window(self._window)
                if rect is None or not rect.isValid():
                    rects.append(None)
                    regions.append(None)
                    continue

                radius = element.corner_radius
                rects.append((rect, radius))
                regions.append(None)  # OpenGL doesn't use QPainterPath

            self._cache.element_rects[key] = rects
            self._cache.element_regions[key] = regions

        self._cache.valid = True


def can_use_opengl() -> bool:
    """Check if OpenGL 3.3+ is available."""
    if not OPENGL_AVAILABLE:
        return False

    try:
        fmt = QSurfaceFormat()
        fmt.setVersion(3, 3)
        fmt.setProfile(QSurfaceFormat.OpenGLContextProfile.CoreProfile)

        test_ctx = QOpenGLContext()
        test_ctx.setFormat(fmt)
        if not test_ctx.create():
            return False

        version = test_ctx.format().version()
        return version >= (3, 3)
    except Exception as e:
        logger.warning(f"[OpenGL] Availability check failed: {e}")
        return False
