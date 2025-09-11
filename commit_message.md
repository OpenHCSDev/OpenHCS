refactor: Major configuration system overhaul with lazy resolution, composition detection, and streaming backends

Comprehensive architectural refactoring that consolidates configuration management, eliminates redundant pipeline config layer, introduces composition-based field detection, and adds Fiji streaming capabilities. This change unifies the configuration system around a single GlobalPipelineConfig with automatic decorator injection and lazy resolution.

Changes by functional area:

* **Core Configuration System**: Complete overhaul with extensible global config pattern
  - **ELIMINATE ENTIRE MODULE**: Delete openhcs/core/pipeline_config.py - entire architectural layer removed through auto-generation
  - Introduce @auto_create_decorator system enabling creation of ANY global config class with automatic field inheritance
  - Enable future global config domains (GlobalAnalysisConfig, GlobalVisualizationConfig) through same decorator pattern
  - Consolidate all config classes (ZarrConfig, VFSConfig, WellFilterConfig) under unified @global_pipeline_config decorator
  - **MODULE REORGANIZATION**: Move context management to dedicated openhcs/core/context/global_config.py with generic thread-local storage
  - Replace hardcoded config relationships with mathematical composition detection
  - Establish extensible foundation for domain-specific global configurations beyond pipeline processing

* **Lazy Configuration & Resolution**: New lazy dataclass system with composition awareness and critical stability fixes
  - Add comprehensive lazy_placeholder.py service for UI placeholder resolution
  - Implement composition-aware field resolution supporting both inheritance and composition patterns
  - Add automatic Optional field default factory creation to eliminate UI introspection complexity
  - **CRITICAL BUG FIXES**: Fix recursion bugs in lazy __getattribute__ using object.__getattribute__ for method access
  - Support method delegation from lazy configs to base configs (e.g., get_streaming_kwargs)
  - Eliminate infinite recursion potential in nested lazy dataclass resolution

* **Composition Detection System**: Mathematical alternative to inheritance detection
  - Add openhcs/core/composition_detection.py for discovering dataclass composition relationships
  - Implement breadth-first and depth-first traversal for nested composition discovery
  - Add unified field resolution that works with both inheritance and composition patterns
  - Support environment variable toggle (OPENHCS_USE_COMPOSITION_DETECTION) for switching detection modes
  - Extend FieldPathDetector with find_all_relationships() and find_all_field_paths_unified() methods

* **Streaming & Visualization Backends**: New Fiji streaming infrastructure with comprehensive process management
  - Add openhcs/io/fiji_stream.py backend for direct PyImageJ integration with automatic metaclass registration
  - **PROCESS LIFECYCLE MANAGEMENT**: Add openhcs/runtime/fiji_stream_visualizer.py with global process tracking, cleanup, and executable detection
  - Extend streaming system to support multiple visualizer backends with unified configuration
  - Replace step-level stream_to_napari boolean with comprehensive StreamingConfig dataclass
  - Add visualizer requirement collection in pipeline compiler for orchestrator setup
  - Implement automatic Fiji process management with graceful termination and resource cleanup

* **Pipeline Compilation & Orchestration**: Streamlined execution with architectural guarantee enforcement
  - **ELIMINATE DEFENSIVE PROGRAMMING**: Replace defensive step.name access with architectural guarantee using frozen_context.step_plans
  - Eliminate redundant get_effective_config() calls in orchestrator - reuse config from initialization (Smart Implementation pattern)
  - Add visualizer_config to ProcessingContext during compilation for orchestrator access
  - Update zarr backend configuration to use zarr_config field name for consistency
  - **IMPORT PATH REORGANIZATION**: Fix import paths throughout orchestrator to use new context/global_config module structure

* **UI Components & Parameter Management**: Mathematical dispatch consolidation and robustness improvements
  - **MATHEMATICAL DISPATCH TABLES**: Consolidate widget update/get operations using dispatch tables (WIDGET_UPDATE_DISPATCH, WIDGET_GET_DISPATCH)
  - Eliminate duplicate placeholder application logic - use single LazyDefaultPlaceholderService.get_lazy_resolved_placeholder()
  - Add signal blocking wrapper (_execute_with_signal_blocking) for stateless widget operations
  - **ROBUSTNESS IMPROVEMENTS**: Fix magicgui widget creation fallbacks for unsupported types (List[T], tuple[T, ...])
  - Implement unified parameter extraction for both lazy and regular dataclasses in from_dataclass_instance()
  - Add comprehensive error handling and fallback widget strategies for UI stability

* **Test Infrastructure**: Enhanced integration testing with timing and field modification
  - Add comprehensive reset placeholder bug scenarios for both materialization and direct field testing
  - Increase timing delays (ACTION_DELAY, WINDOW_DELAY, SAVE_DELAY from 0.5s to 1.5s) for GUI stability
  - Add reset_field_to_test parameter to TestScenario for testing field-specific reset behavior
  - Update test imports to use new context/global_config module and dynamically generated PipelineConfig
  - Add generic configuration builder for automatic detection of direct vs nested config fields

* **Documentation & Architecture**: Comprehensive architectural documentation updates
  - Add "Smart Implementation Through Information Reuse" section to respecting_codebase_architecture.rst
  - Create new composition_detection_system.rst documenting mathematical composition detection
  - Create new context_management_system.rst documenting generic thread-local context management
  - Update configuration_system_architecture.rst with automatic decorator injection system
  - Update lazy_class_system.rst with composition awareness and method delegation
  - Update napari_streaming_system.rst to unified streaming system with multiple backends
  - Update pipeline_compilation_system.rst with streaming detection and visualizer requirements
  - Update field_path_detection.rst with unified inheritance/composition detection
  - Update architecture/index.rst to reflect new documentation structure and cross-references

This refactoring eliminates the dual config system complexity, provides mathematical composition detection as an alternative to inheritance, and establishes a unified streaming backend architecture. The lazy resolution system now supports both inheritance and composition patterns while maintaining UI placeholder functionality.

**Key Architectural Innovation**: The @auto_create_decorator pattern establishes an extensible foundation for creating multiple global configuration domains (GlobalAnalysisConfig, GlobalVisualizationConfig, etc.) beyond the current GlobalPipelineConfig. Each domain can have its own field inheritance patterns and thread-local context management, enabling OpenHCS to expand into new functional areas while maintaining consistent configuration architecture.

All changes preserve existing API contracts while significantly reducing architectural complexity and providing a clear path for future extensibility.
