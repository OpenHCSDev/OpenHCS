====================================
Visual Feedback and Flash Animations
====================================

Overview
========

OpenHCS provides real-time visual feedback when you edit configuration values across multiple windows. The system uses color-coded borders and flash animations to help you understand:

- **Which orchestrator (plate) you're working with** - Each plate gets a unique color
- **Which step belongs to which plate** - Steps inherit their plate's color
- **When configuration values change** - Flash animations indicate updates
- **Hierarchical relationships** - Layered borders show step positions

This visual feedback helps you stay oriented when working with multiple plates and complex pipelines.

Color-Coded Borders
===================

Orchestrator (Plate) Colors
---------------------------

Each plate in the Plate Manager gets a unique, perceptually distinct color:

- **Background**: Subtle colored background (15% opacity)
- **Border**: Solid 3px border in the plate's color
- **Underlined name**: Plate names are underlined for emphasis

**Example**: If you have 3 plates open, each will have a different color (e.g., blue, orange, green) making it easy to distinguish them at a glance.

Step Colors
-----------

Steps in the Pipeline Editor inherit their orchestrator's color:

- **Background**: Very subtle colored background (5% opacity)
- **Borders**: Layered borders with different tints and patterns

**Layered Borders**: Steps use multiple border layers to show their position:

- **Step 0-2**: 1 border with solid pattern, different tints (dark, neutral, bright)
- **Step 3-5**: 1 border with dashed pattern, different tints
- **Step 6-8**: 1 border with dotted pattern, different tints
- **Step 9+**: Multiple border layers for additional differentiation

This pattern ensures that even if you have 20+ steps, each one has a visually distinct appearance.

Window Borders
--------------

When you open a step editor window, it gets a colored border matching the step's color. This helps you quickly identify which step you're editing, especially when multiple step editors are open.

Flash Animations
================

What Triggers a Flash
---------------------

Flash animations provide immediate visual feedback when configuration values change:

**List Items Flash** when:

- You edit a step's configuration and the **resolved value** changes
- You edit a pipeline config and it affects steps
- You edit a global config and it affects pipelines or steps

**Form Widgets Flash** when:

- An inherited value updates (e.g., step inherits new value from pipeline config)
- A placeholder value changes due to context updates

Resolved vs Raw Values
----------------------

**Important**: Flash animations only trigger when the **effective value** changes, not just the raw field value.

**Example**:

.. code-block:: python

   # Pipeline config
   pipeline.well_filter = 4
   
   # Step config (overrides pipeline)
   step.well_filter = 3
   
   # User changes pipeline.well_filter from 4 to 5
   # Step does NOT flash because its effective value is still 3

This prevents false positives where steps would flash even though their actual behavior didn't change.

Visual Indicators
-----------------

**List Item Flash**:

- Background color briefly increases to 100% opacity
- Returns to normal after 300ms
- Helps you see which items were affected by your change

**Widget Flash**:

- Form widgets (text fields, dropdowns) briefly show a light green background
- Returns to normal after 300ms
- Helps you see which inherited values updated

Understanding the Visual System
================================

Scope Hierarchy
---------------

The visual system uses a hierarchical scope system:

.. code-block:: text

   Orchestrator (Plate)
   ├── Step 0 (inherits plate color)
   ├── Step 1 (inherits plate color)
   └── Step 2 (inherits plate color)

Each scope gets a unique identifier:

- **Orchestrator scope**: ``"/path/to/plate"``
- **Step scope**: ``"/path/to/plate::step_0@5"``

The ``@5`` suffix indicates the step's position within that orchestrator, enabling independent numbering per plate.

Color Consistency
-----------------

Colors are **deterministic** - the same plate always gets the same color:

- Colors are generated using MD5 hashing of the scope ID
- 50 perceptually distinct colors are available
- Colors meet WCAG AA accessibility standards (4.5:1 contrast ratio)

This means if you close and reopen OpenHCS, your plates will have the same colors as before.

Practical Examples
==================

Example 1: Editing a Step
--------------------------

1. Open Plate Manager - see 3 plates with different colored borders
2. Select a plate and open Pipeline Editor - steps inherit the plate's color
3. Double-click a step to open Step Editor - window border matches step color
4. Edit a parameter - the step item in Pipeline Editor flashes
5. If the change affects other steps, they flash too

Example 2: Editing Pipeline Config
-----------------------------------

1. Open Plate Manager
2. Click "Edit Config" for a plate
3. Change ``num_workers`` from 4 to 8
4. The plate item in Plate Manager flashes
5. All steps in Pipeline Editor flash (they inherit the new value)

Example 3: Multiple Plates
---------------------------

1. Open 2 plates: ``/data/plate_A`` (blue) and ``/data/plate_B`` (orange)
2. Open Pipeline Editor for plate_A - steps have blue borders
3. Open Pipeline Editor for plate_B - steps have orange borders
4. Edit a step in plate_A - only blue items flash
5. Edit a step in plate_B - only orange items flash

This visual separation prevents confusion when working with multiple plates simultaneously.

Configuration
=============

The visual feedback system is enabled by default. If you want to disable flash animations:

.. code-block:: python

   from openhcs.pyqt_gui.widgets.shared.scope_visual_config import ScopeVisualConfig
   
   config = ScopeVisualConfig()
   config.LIST_ITEM_FLASH_ENABLED = False  # Disable list item flashing
   config.WIDGET_FLASH_ENABLED = False     # Disable widget flashing

See Also
========

- :doc:`../architecture/scope_visual_feedback_system` - Technical architecture and implementation
- :doc:`../architecture/gui_performance_patterns` - Cross-window preview system
- :doc:`../architecture/configuration_framework` - Lazy configuration and inheritance

