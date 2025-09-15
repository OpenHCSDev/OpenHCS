Parameter Form Lifecycle Management
===================================

**Complete lifecycle of parameter forms from creation to context synchronization.**

*Status: STABLE*
*Module: openhcs.pyqt_gui.widgets.shared.parameter_form_manager*

Overview
--------
Parameter forms must maintain consistency between widget state, internal parameters, and thread-local context. Traditional forms lose this synchronization during operations like reset, causing placeholder bugs. The lifecycle management system ensures all three states remain synchronized.

:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.reset_parameter` orchestrates the complete reset lifecycle. It first determines the reset value (None for lazy configs), updates the internal parameter dictionary, updates the thread-local context to match, then updates the widget display and applies placeholder logic. This four-step process ensures that form state, context state, and widget display all stay in sync.

This prevents the reset placeholder bug where forms show stale values instead of current defaults.

Widget State Management
-----------------------
The form manager coordinates widget updates with context behavior application.

Value Update Coordination
~~~~~~~~~~~~~~~~~~~~~~~~~
:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.update_widget_value` acts as the central coordinator for widget updates. It first blocks signals to prevent infinite loops, updates the widget's displayed value using type-specific dispatch, then applies context behavior (like placeholder text for None values). This ensures widgets show the right value without triggering cascading updates.

Context Behavior Application
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._apply_context_behavior` decides whether to show placeholder text. If the value is None and we're in a lazy dataclass context, it calls the placeholder resolution system. If the value is not None, it clears any existing placeholder state. This creates the dynamic "Pipeline default: X" behavior.

Parameter Change Propagation
----------------------------
Changes flow from widgets through internal state to context synchronization.

:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._emit_parameter_change` handles the flow when users change widget values. It converts the raw widget value to the correct type, updates the internal parameter dictionary, then emits a signal so other components can react. This is the normal path for user edits (as opposed to programmatic updates like reset).

Thread-Local Context Synchronization
------------------------------------
Critical synchronization patterns ensure context reflects current form state.

Reset Context Update Pattern
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.reset_parameter` updates thread-local context during reset using :py:func:`~dataclasses.replace` to prevent placeholder bugs.

UI Component Lifecycle Patterns
-------------------------------
Different UI components have different form lifecycle requirements.

Step Editor Lifecycle
~~~~~~~~~~~~~~~~~~~~~
Step editors show step configurations with isolated context. Forms are created with custom context providers that resolve against their parent pipeline configuration. Reset operations update the step-specific context without affecting other UI components.

Pipeline Editor Lifecycle
~~~~~~~~~~~~~~~~~~~~~~~~~
Pipeline editors (plate manager style) handle pipeline-level configuration editing. Forms use standard thread-local context resolution and coordinate with the plate manager's save/load operations.

Pipeline Config Lifecycle
~~~~~~~~~~~~~~~~~~~~~~~~~
Pipeline config editing (accessed from plate manager) creates forms that resolve against the current pipeline's thread-local context. Save operations update both the pipeline configuration and the thread-local context to maintain consistency.

Global Config Lifecycle
~~~~~~~~~~~~~~~~~~~~~~~
Global config editing (accessed from main window) creates forms that show static defaults. Reset operations restore base class default values since there's no higher-level context to resolve against.

Form State Synchronization
--------------------------
The three-state synchronization pattern ensures consistency across all UI components.

Internal Parameter State
~~~~~~~~~~~~~~~~~~~~~~~~
:py:attr:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.parameters` stores the form's internal parameter dictionary. This represents the current user edits and serves as the source of truth for widget display.

Thread-Local Context State
~~~~~~~~~~~~~~~~~~~~~~~~~~
:py:class:`~openhcs.core.context.global_config._global_config_contexts` maintains thread-local context that affects placeholder resolution. This must be kept synchronized with form state during operations like reset.

Widget Display State
~~~~~~~~~~~~~~~~~~~~
Widget values and placeholder text reflect the combination of internal parameters and context resolution. The form manager ensures widgets always display the correct state based on current parameters and context.

See Also
--------
- :doc:`placeholder_resolution_system` - Placeholder generation using form context
- :doc:`context_management_system` - Thread-local context management patterns
- :doc:`service-layer-architecture` - Service layer integration with forms
