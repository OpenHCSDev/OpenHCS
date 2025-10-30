Parameter Form Lifecycle Management
===================================

**Complete lifecycle of parameter forms from creation to context synchronization.**

*Status: STABLE (describes main branch implementation)*
*Module: openhcs.pyqt_gui.widgets.shared.parameter_form_manager*

.. note::
   This document describes the **main branch** monolithic implementation. For the refactored service-oriented architecture currently in development, see :doc:`parameter_form_service_architecture`.

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

Cross-Window Placeholder Updates
---------------------------------
When multiple configuration dialogs are open simultaneously, they share live values for placeholder resolution. This enables real-time preview of configuration changes across windows.

Live Context Collection
~~~~~~~~~~~~~~~~~~~~~~~~
:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._collect_live_context_from_other_windows` gathers current user-modified values from all active form managers. When a user types in one window, other windows immediately see the updated value in their placeholders. This creates a live preview system where configuration changes are visible before saving.

Active Manager Registry
~~~~~~~~~~~~~~~~~~~~~~~~
:py:attr:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._active_form_managers` maintains a class-level list of all active form manager instances. When a form manager is created, it registers itself in this list. When a dialog closes, it must unregister to prevent ghost references that cause infinite refresh loops.

Signal-Based Synchronization
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Form managers emit :py:attr:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.context_value_changed` and :py:attr:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.context_refreshed` signals when values change. Other active managers listen to these signals and refresh their placeholders accordingly. This creates a reactive system where all windows stay synchronized.

Dialog Lifecycle Management
----------------------------
Proper dialog cleanup is critical to prevent ghost form managers that cause infinite refresh loops and runaway CPU usage.

The Ghost Manager Problem
~~~~~~~~~~~~~~~~~~~~~~~~~~
When a dialog closes without unregistering its form manager, it remains in the ``_active_form_managers`` registry as a "ghost". When a new dialog opens and the user types, the system collects context from the ghost manager, which triggers a refresh in the ghost, which collects context from the new manager, creating an infinite ping-pong loop.

Qt Dialog Lifecycle Quirk
~~~~~~~~~~~~~~~~~~~~~~~~~~
Qt's ``QDialog.accept()`` and ``QDialog.reject()`` methods do NOT trigger ``closeEvent()`` - they just hide the dialog and emit signals. This means cleanup code in ``closeEvent()`` is never called when users click Save or Cancel buttons. Dialogs must explicitly unregister in ``accept()``, ``reject()``, and ``closeEvent()`` to ensure cleanup happens regardless of how the dialog closes.

BaseFormDialog Pattern
~~~~~~~~~~~~~~~~~~~~~~
:py:class:`~openhcs.pyqt_gui.windows.base_form_dialog.BaseFormDialog` solves the cleanup problem by providing a base class that automatically handles unregistration. It overrides ``accept()``, ``reject()``, and ``closeEvent()`` to call ``_unregister_all_form_managers()`` before closing. Subclasses implement ``_get_form_managers()`` to return their form manager instances, and the base class handles all cleanup automatically.

This pattern ensures that every dialog using ParameterFormManager properly cleans up, preventing ghost manager bugs without requiring developers to remember manual cleanup in multiple methods.

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

Example: BaseFormDialog Usage
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: python

   from openhcs.pyqt_gui.windows.base_form_dialog import BaseFormDialog
   from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

   class MyConfigDialog(BaseFormDialog):
       """Configuration dialog with automatic cleanup."""

       def __init__(self, config, parent=None):
           super().__init__(parent)

           # Create form manager
           self.form_manager = ParameterFormManager(
               field_id="my_config",
               dataclass_type=type(config),
               initial_values=config
           )

       def _get_form_managers(self):
           """Return form managers to unregister (required by BaseFormDialog)."""
           return [self.form_manager]

       # No need to override accept(), reject(), or closeEvent()
       # BaseFormDialog handles all cleanup automatically!

This pattern ensures proper cleanup regardless of how the dialog closes (Save button → ``accept()``, Cancel button → ``reject()``, X button → ``closeEvent()``).

See Also
--------
- :doc:`parameter_form_service_architecture` - Refactored service-oriented architecture (in development)
- :doc:`context_system` - Thread-local context management patterns
- :doc:`service-layer-architecture` - Service layer integration with forms
- :doc:`code_ui_interconversion` - Code/UI interconversion patterns
- :py:class:`~openhcs.pyqt_gui.windows.base_form_dialog.BaseFormDialog` - Base class for dialog cleanup
- :py:class:`~openhcs.pyqt_gui.windows.config_window.ConfigWindow` - Example BaseFormDialog implementation
- :py:class:`~openhcs.pyqt_gui.windows.dual_editor_window.DualEditorWindow` - Example BaseFormDialog implementation
