Composition Detection System
============================

**Mathematical alternative to inheritance detection using composition patterns.**

*Status: STABLE*
*Module: openhcs.core.composition_detection*

Overview
--------

Traditional field path detection relies on inheritance relationships between dataclasses. The composition detection system provides equivalent functionality through mathematical analysis of dataclass composition patterns, enabling field resolution in systems that use composition over inheritance.

.. code-block:: python

   # Inheritance pattern (traditional)
   class StepConfig(GlobalConfig):
       step_name: str = "default"
   
   # Composition pattern (new capability)
   @dataclass
   class StepConfig:
       global_config: GlobalConfig
       step_name: str = "default"

The composition detection system automatically discovers these relationships and provides the same field resolution capabilities as inheritance-based systems.

Mathematical Composition Discovery
----------------------------------

The system uses breadth-first traversal to discover composition hierarchies automatically without requiring explicit relationship declarations.

.. literalinclude:: ../../../openhcs/core/composition_detection.py
   :language: python
   :lines: 21-38
   :caption: Auto-discover composition relationships and field paths

This mathematical approach discovers all composition relationships automatically, providing complete field path mapping for any nesting level.

Composition-Aware Field Resolution
----------------------------------

Field resolution works through composition hierarchies using the same breadth-first then depth-first pattern as inheritance systems.

.. literalinclude:: ../../../openhcs/core/composition_detection.py
   :language: python
   :lines: 51-77
   :caption: Auto-resolve field through composition hierarchy

This provides equivalent functionality to inheritance-based field resolution while working with composition patterns.

Unified Detection System
------------------------

The system provides unified field path detection that works with both inheritance and composition patterns simultaneously.

.. literalinclude:: ../../../openhcs/core/field_path_detection.py
   :language: python
   :lines: 149-180
   :caption: Find ALL relationships - both inheritance AND composition

This enables the same lazy resolution system to work with mixed inheritance/composition architectures, providing maximum flexibility for configuration design patterns.

Environment-Based Detection Mode
--------------------------------

The system supports runtime switching between detection modes through environment configuration.

.. code-block:: python

   # Configuration flag for switching detection approaches
   USE_COMPOSITION_DETECTION = os.getenv('OPENHCS_USE_COMPOSITION_DETECTION', 'false').lower() == 'true'
   
   # Unified field path detection respects environment setting
   if USE_COMPOSITION_DETECTION:
       paths = find_all_composition_paths_for_type(root_type, target_type)
   else:
       paths = FieldPathDetector.find_all_field_paths_for_type(root_type, target_type)

This enables gradual migration from inheritance to composition patterns without breaking existing functionality.

Integration with Lazy Resolution
--------------------------------

The composition detection system integrates seamlessly with the lazy configuration system to provide composition-aware field providers.

.. literalinclude:: ../../../openhcs/core/composition_detection.py
   :language: python
   :lines: 79-100
   :caption: Create composition-based field provider for lazy resolution

This enables lazy dataclasses to resolve fields through composition hierarchies with the same performance and functionality as inheritance-based resolution.
