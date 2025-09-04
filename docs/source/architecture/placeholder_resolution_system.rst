Placeholder Resolution System
============================

**Dynamic placeholder text generation for lazy dataclass fields with thread-local context awareness.**

*Status: STABLE*
*Module: openhcs.core.lazy_placeholder*

Overview
--------
UI forms need to show meaningful placeholder text when fields are None, but traditional systems show static defaults that don't reflect actual runtime context. The placeholder resolution system generates dynamic placeholder text by resolving lazy dataclass fields against current thread-local context.

The core entry point :py:meth:`~openhcs.core.lazy_placeholder.LazyDefaultPlaceholderService.get_lazy_resolved_placeholder` works by creating a temporary lazy dataclass instance, then asking that instance to resolve the specific field value. The instance looks first at thread-local context (current pipeline config), then falls back to global defaults. This creates placeholders that show what the field would actually resolve to at runtime.

This enables placeholders like "Pipeline default: 4" that reflect actual inheritance chains rather than hardcoded static values.

LazyDefaultPlaceholderService
-----------------------------
The service provides context-aware placeholder generation with composition-aware field resolution.

Core Resolution Logic
~~~~~~~~~~~~~~~~~~~~~
The service uses :py:func:`~openhcs.core.lazy_placeholder._resolve_field_with_composition_awareness` to find field values. This function first checks if the field exists directly on the dataclass (like `num_workers` on `PipelineConfig`). If not found, it recursively searches through nested dataclasses (like looking for `output_dir_suffix` inside `materialization_defaults`). This unified approach handles both inheritance patterns (field exists on current class) and composition patterns (field exists in nested class).

Thread-Local Context Integration
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The service manipulates thread-local context using :py:func:`~openhcs.core.context.global_config.set_current_global_config` and :py:func:`~openhcs.core.context.global_config.get_current_global_config` for different resolution modes. For static defaults, it temporarily clears context to get base class values. For app config mode, it temporarily sets the provided config as context. For normal mode, it uses whatever context is currently active.

Composition-Aware Field Resolution
----------------------------------
The system handles both direct fields and nested dataclass field resolution through unified composition awareness.

:py:func:`~openhcs.core.lazy_placeholder._resolve_field_with_composition_awareness` works like a smart field finder. Given a dataclass instance and a field name, it first checks if the field exists directly on the instance (using `dataclasses.fields()`). If found, it gets the value using `getattr()`. If not found, it loops through all fields looking for nested dataclasses, then recursively searches inside each one. This handles cases where `output_dir_suffix` might be inside `materialization_defaults` rather than directly on `PipelineConfig`.

Reset Placeholder Bug Prevention
--------------------------------
The reset placeholder bug occurs when thread-local context contains stale values after field reset. The fix ensures context synchronization.

:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.reset_parameter` fixes this by updating thread-local context immediately after resetting a field to None. It gets the current context, creates a copy with the reset field set to None using :py:func:`~dataclasses.replace`, then updates the thread-local storage. This ensures that when placeholders are generated later, they resolve against the correct context instead of stale values.

UI Context Hierarchy
--------------------
Different UI components require different placeholder resolution contexts.

Step Editor Context
~~~~~~~~~~~~~~~~~~~
Step editors show step configurations with isolated context that reflects their parent pipeline configuration. :py:meth:`~openhcs.core.lazy_config.LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy` creates step-specific lazy configs with custom context providers that resolve against their parent pipeline config instead of global thread-local context.

Pipeline Editor Context
~~~~~~~~~~~~~~~~~~~~~~~
Pipeline editors (plate manager style) handle pipeline-level configuration editing. These use the standard thread-local context resolution where pipeline configs resolve against global config defaults.

Pipeline Config Context
~~~~~~~~~~~~~~~~~~~~~~~
Pipeline config editing (accessed from plate manager) uses thread-local context with the current pipeline configuration, allowing fields to show "Pipeline default: X" values that reflect the specific pipeline's settings.

Global Config Context
~~~~~~~~~~~~~~~~~~~~~
Global config editing (accessed from main window) shows static defaults since there's no higher-level context to resolve against. Fields display their base class default values.

See Also
--------
- :doc:`parameter_form_lifecycle` - Form lifecycle and context synchronization
- :doc:`context_management_system` - Thread-local context management
- :doc:`lazy_class_system` - Lazy dataclass resolution that powers placeholders
