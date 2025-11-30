Scope-Based Visual Feedback System
===================================

Overview
--------

The scope visual feedback system provides visual cues to help users understand
which scope (orchestrator or step) a window belongs to. It uses MD5-based color
generation to create consistent, WCAG AA compliant colors for each scope.

Architecture
------------

The system consists of several components:

**ScopeColorService** (``services/scope_color_service.py``)
    Singleton service that manages scope-to-color mappings. Generates colors
    using MD5 hashing of scope_id strings to ensure consistency across sessions.

**ScopeColorScheme** (``scope_visual_config.py``)
    Dataclass holding all derived colors for a scope:
    
    - ``base_rgb``: The primary scope color
    - ``orchestrator_border_rgb``: Border color for orchestrator windows
    - ``orchestrator_item_border_rgb``: Border color for list items
    - ``step_background_rgb``: Background tint for step windows
    - ``flash_color_rgb``: Color used for flash animations

**ScopedBorderMixin** (``scoped_border_mixin.py``)
    Mixin for QDialog/QWidget that renders scope-based borders:
    
    - Simple solid borders for orchestrator-level scopes
    - Layered patterned borders for step-level scopes
    - Reactive updates via signal connections

**Flash Animation System**
    Smooth flash animations for visual feedback when values change:
    
    - ``SmoothFlashAnimatorBase``: Base class using QVariantAnimation
    - ``WidgetFlashAnimator``: Flashes QWidget backgrounds
    - ``TreeItemFlashAnimator``: Flashes QTreeWidgetItem backgrounds
    - ``ListItemFlashAnimator``: Flashes QListWidgetItem backgrounds

**TreeFormFlashMixin** (``tree_form_flash_mixin.py``)
    Mixin for windows with tree + form that provides:
    
    - GroupBox flashing when navigating to sections
    - Tree item flashing when placeholder values change cross-window

Usage
-----

Windows declare their scope via ``scope_id`` attribute:

.. code-block:: python

    class MyWindow(ScopedBorderMixin, TreeFormFlashMixin, QDialog):
        def __init__(self, scope_id: str):
            super().__init__()
            self.scope_id = scope_id
            
            # Initialize form_manager, tree_widget, etc.
            self.setup_ui()
            
            # Initialize scope border rendering
            self._init_scope_border()
            
            # Register flash hooks for placeholder changes
            self._register_placeholder_flash_hook()

Color Generation
----------------

Colors are generated using MD5 hashing to ensure:

1. **Consistency**: Same scope_id always produces same color
2. **Uniqueness**: Different scopes get visually distinct colors
3. **Accessibility**: Colors meet WCAG AA contrast requirements

The algorithm:

1. Hash scope_id with MD5
2. Extract hue from first 2 bytes (0-360°)
3. Use fixed saturation (0.65) and lightness (0.45) for WCAG compliance
4. Convert HSL to RGB

Flash Animation Timing
----------------------

The smooth flash animation uses QVariantAnimation for 60fps transitions:

- **Fade-in**: 100ms with OutQuad easing (quick snap to flash color)
- **Hold**: 150ms at max intensity while rapid updates continue
- **Fade-out**: 350ms with InOutCubic easing (smooth return to original)

This creates a natural "pulse" effect that's noticeable but not jarring.

Integration Points
------------------

The system integrates with:

- ``ParameterFormManager``: Provides ``_on_placeholder_changed_callbacks`` hook
- ``ParameterOpsService``: Fires callbacks when placeholder values actually change
- ``AbstractManagerWidget``: Applies scope colors to list items
- ``ListItemDelegate``: Renders scope-colored borders on list items

Files
-----

New files added:

- ``scope_color_utils.py``: Utility functions for scope color access
- ``scope_color_strategy.py``: Strategy pattern for color scheme derivation
- ``scope_visual_config.py``: Configuration dataclasses
- ``services/scope_color_service.py``: Core service implementation
- ``scoped_border_mixin.py``: Window border rendering mixin
- ``smooth_flash_base.py``: Base class for flash animations
- ``widget_flash_animation.py``: Widget flash animator
- ``tree_item_flash_animation.py``: Tree item flash animator
- ``list_item_flash_animation.py``: List item flash animator
- ``tree_form_flash_mixin.py``: Combined tree+form flash mixin

