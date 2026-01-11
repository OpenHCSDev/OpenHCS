"""
CheckboxGroupWidget for List[Enum] parameters.

Provides explicit type-based dispatch instead of duck typing with monkey-patched methods.
"""

from typing import List, Optional, Type
from enum import Enum

from PyQt6.QtWidgets import QGroupBox, QVBoxLayout
from PyQt6.QtCore import pyqtSignal

from pyqt_formgen.widgets import NoneAwareCheckBox


class CheckboxGroupWidget(QGroupBox):
    """
    Multi-selection checkbox group for List[Enum] parameters.

    Uses NoneAwareCheckBox pattern consistently with bool parameters:
    - Initialize all checkboxes with set_value(None) for placeholder state
    - Use set_value() instead of setChecked() to properly track placeholder state
    - Use get_value() in get_selected_values() to distinguish placeholder vs concrete
    """

    # Signal emitted when selection changes
    selection_changed = pyqtSignal()

    def __init__(self, param_name: str, enum_type: Type[Enum], current_value: Optional[List[Enum]] = None, parent=None):
        """
        Initialize checkbox group widget.

        Args:
            param_name: Parameter name for display
            enum_type: Enum type for checkbox options
            current_value: Initial selected values (None for placeholder state)
            parent: Parent widget
        """
        super().__init__(param_name.replace('_', ' ').title(), parent)

        self._checkboxes = {}
        self._enum_type = enum_type

        layout = QVBoxLayout(self)
        layout.setContentsMargins(8, 8, 8, 8)
        layout.setSpacing(4)

        # Create checkbox for each enum value
        for enum_val in enum_type:
            checkbox = NoneAwareCheckBox()
            checkbox.setText(enum_val.name.replace('_', ' ').title())

            # Initialize with None (placeholder state) or concrete value
            if current_value is None:
                checkbox.set_value(None)
            else:
                checkbox.set_value(enum_val in current_value)

            # Connect signal to emit selection_changed
            checkbox.stateChanged.connect(self._on_checkbox_changed)

            layout.addWidget(checkbox)
            self._checkboxes[enum_val] = checkbox

    def _on_checkbox_changed(self):
        """Handle checkbox state change - convert all checkboxes from placeholder to concrete."""
        # When ANY checkbox is clicked, convert ALL checkboxes from placeholder to concrete
        # This ensures consistent behavior: either all inherit (None) or all are explicit
        for checkbox in self._checkboxes.values():
            if checkbox._is_placeholder:
                # Convert from placeholder to concrete value
                checkbox._is_placeholder = False
                checkbox.setProperty("is_placeholder_state", False)

        self.selection_changed.emit()

    def get_selected_values(self) -> Optional[List[Enum]]:
        """
        Get selected enum values, returning None if all checkboxes are in placeholder state.

        Treats List[Enum] like a list of independent bools:
        - If ALL checkboxes are in placeholder state → return None (inherit from parent)
        - If ANY checkbox has been clicked → ALL become concrete, return list of checked items

        Note: The signal handler ensures that clicking ANY checkbox converts ALL to concrete,
        so we should never have a mixed state (some placeholder, some concrete).
        """
        # Check if any checkbox has a concrete value (not placeholder)
        has_concrete_value = any(
            checkbox.get_value() is not None
            for checkbox in self._checkboxes.values()
        )

        if not has_concrete_value:
            # All checkboxes are in placeholder state - return None to inherit from parent
            return None

        # All checkboxes are concrete (signal handler converted them)
        # Return list of enum values where checkbox is checked
        return [
            enum_val for enum_val, checkbox in self._checkboxes.items()
            if checkbox.get_value() == True
        ]

    def set_selected_values(self, values: Optional[List[Enum]]) -> None:
        """
        Set selected values.

        Args:
            values: List of enum values to select, or None for placeholder state
        """
        if values is None:
            # Set all checkboxes to placeholder state
            for checkbox in self._checkboxes.values():
                checkbox.set_value(None)
        else:
            # Set concrete values
            for enum_val, checkbox in self._checkboxes.items():
                checkbox.set_value(enum_val in values)

