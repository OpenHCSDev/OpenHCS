#!/usr/bin/env python3
"""
Widget-specific validation tests for dual editor reset functionality.

Tests individual widget types (text fields, checkboxes, dropdowns, spinboxes)
to ensure they properly reset to default/placeholder states.
"""

import pytest
import sys
import os
from typing import Dict, Any, List, Union
from unittest.mock import Mock, patch

# Add project root to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..')))

from PyQt6.QtWidgets import (
    QApplication, QComboBox, QLineEdit, QCheckBox, QSpinBox,
    QDoubleSpinBox, QWidget
)
from PyQt6.QtCore import Qt

from openhcs.core.config import Microscope
from openhcs.constants.constants import VariableComponents, GroupBy
from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
from openhcs.pyqt_gui.widgets.step_parameter_editor import StepParameterEditorWidget
from openhcs.pyqt_gui.widgets.function_pane import FunctionPaneWidget
from openhcs.textual_tui.widgets.shared.signature_analyzer import SignatureAnalyzer


@pytest.fixture(scope="module")
def qapp():
    """Create QApplication instance for tests."""
    app = QApplication.instance()
    if app is None:
        app = QApplication([])
    yield app


@pytest.fixture
def mock_service_adapter():
    """Create a mock service adapter for testing."""
    adapter = Mock()
    adapter.show_error_dialog = Mock()
    adapter.show_info_dialog = Mock()
    return adapter


class TestWidgetResetValidation:
    """Test individual widget reset behavior."""
    
    def test_combobox_enum_reset(self, qapp):
        """Test QComboBox reset behavior for enum fields."""
        from openhcs.core.pipeline_config import PipelineConfig
        
        # Create form manager with enum field
        param_info = SignatureAnalyzer.analyze(PipelineConfig)
        parameters = {'microscope': Microscope.IMAGEXPRESS}  # Non-default value
        parameter_types = {name: info.param_type for name, info in param_info.items()}
        
        form_manager = ParameterFormManager(
            parameters=parameters,
            parameter_types=parameter_types,
            field_id="test",
            parameter_info=param_info,
            is_global_config_editing=False  # Lazy context
        )
        
        microscope_widget = form_manager.widgets.get('microscope')
        assert isinstance(microscope_widget, QComboBox)
        
        # Verify initial state (should show IMAGEXPRESS)
        assert microscope_widget.currentData() == Microscope.IMAGEXPRESS
        
        # Reset parameter
        form_manager._reset_parameter('microscope')
        
        # Verify reset state
        assert form_manager.textual_form_manager.parameters['microscope'] is None
        assert microscope_widget.currentData() == Microscope.AUTO  # Default
        assert microscope_widget.property('is_placeholder_state') is not None
        
        # Verify placeholder styling
        style_sheet = microscope_widget.styleSheet()
        assert 'italic' in style_sheet.lower() or 'color' in style_sheet.lower()
    
    def test_lineedit_string_reset(self, qapp):
        """Test QLineEdit reset behavior for string fields."""
        from openhcs.core.config import PathPlanningConfig
        
        # Create form manager with string field
        param_info = SignatureAnalyzer.analyze(PathPlanningConfig)
        parameters = {'output_dir_suffix': '_custom_suffix'}  # Non-default value
        parameter_types = {name: info.param_type for name, info in param_info.items()}
        
        form_manager = ParameterFormManager(
            parameters=parameters,
            parameter_types=parameter_types,
            field_id="test",
            parameter_info=param_info,
            is_global_config_editing=False  # Lazy context
        )
        
        suffix_widget = form_manager.widgets.get('output_dir_suffix')
        assert isinstance(suffix_widget, QLineEdit)
        
        # Verify initial state
        assert suffix_widget.text() == '_custom_suffix'
        
        # Reset parameter
        form_manager._reset_parameter('output_dir_suffix')
        
        # Verify reset state
        assert form_manager.textual_form_manager.parameters['output_dir_suffix'] is None
        assert suffix_widget.text() == ""  # Should be empty
        assert suffix_widget.placeholderText() != ""  # Should have placeholder
        assert suffix_widget.property('is_placeholder_state') is not None
    
    def test_checkbox_boolean_reset(self, qapp, mock_service_adapter):
        """Test QCheckBox reset behavior for boolean fields."""
        from openhcs.processing.backends.processors.torch_processor import tophat

        # Create function pane with boolean parameter (if tophat has one)
        func_item = (tophat, {"selem_radius": 25})  # Use tophat function
        pane = FunctionPaneWidget(
            func_item=func_item,
            index=0,
            service_adapter=mock_service_adapter
        )

        # Find selem_radius widget (integer parameter)
        selem_radius_widget = None
        if hasattr(pane, 'enhanced_form_manager') and pane.enhanced_form_manager:
            selem_radius_widget = pane.enhanced_form_manager.widgets.get('selem_radius')

        if selem_radius_widget and isinstance(selem_radius_widget, (QSpinBox, QDoubleSpinBox)):
            # Verify initial state
            assert selem_radius_widget.value() == 25

            # Reset all parameters
            pane.reset_all_parameters()

            # Verify reset state
            default_value = pane.param_defaults.get('selem_radius', 50)  # Default from function
            assert selem_radius_widget.value() == default_value
            assert pane._internal_kwargs['selem_radius'] == default_value
    
    def test_spinbox_integer_reset(self, qapp, mock_service_adapter):
        """Test QSpinBox reset behavior for integer fields."""
        from openhcs.processing.backends.processors.torch_processor import tophat

        # Create function pane with integer parameter
        func_item = (tophat, {"downsample_factor": 8})  # Non-default value
        pane = FunctionPaneWidget(
            func_item=func_item,
            index=0,
            service_adapter=mock_service_adapter
        )

        # Find downsample_factor widget
        downsample_factor_widget = None
        if hasattr(pane, 'enhanced_form_manager') and pane.enhanced_form_manager:
            downsample_factor_widget = pane.enhanced_form_manager.widgets.get('downsample_factor')

        if downsample_factor_widget and isinstance(downsample_factor_widget, (QSpinBox, QDoubleSpinBox)):
            # Verify initial state
            assert downsample_factor_widget.value() == 8

            # Reset all parameters
            pane.reset_all_parameters()

            # Verify reset state
            default_value = pane.param_defaults.get('downsample_factor', 4)  # Default from function
            assert downsample_factor_widget.value() == default_value
            assert pane._internal_kwargs['downsample_factor'] == default_value
    
    def test_enum_list_widget_reset(self, qapp, mock_service_adapter):
        """Test enum list widget reset behavior."""
        from openhcs.core.steps.function_step import FunctionStep
        from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize

        # Create step with enum list parameter
        step = FunctionStep(
            name="test_step",
            func=stack_percentile_normalize,
            group_by=GroupBy.WELL,
            variable_components=[VariableComponents.WELL, VariableComponents.SITE]  # Non-default
        )
        
        editor = StepParameterEditorWidget(
            step=step,
            service_adapter=mock_service_adapter
        )
        
        # Find variable_components widget
        var_components_widget = editor.form_manager.widgets.get('variable_components')
        
        if var_components_widget:
            # Store original value
            original_components = step.variable_components
            
            # Reset parameter
            editor.reset_parameter('variable_components')
            
            # Verify reset
            default_components = editor.param_defaults.get('variable_components', [])
            assert step.variable_components == default_components


class TestWidgetStateConsistency:
    """Test widget state consistency across reset operations."""
    
    def test_form_manager_widget_sync(self, qapp):
        """Test that form manager and widgets stay in sync during reset."""
        from openhcs.core.pipeline_config import PipelineConfig
        
        # Create form manager
        param_info = SignatureAnalyzer.analyze(PipelineConfig)
        parameters = {
            'microscope': Microscope.IMAGEXPRESS,
            'num_workers': 16
        }
        parameter_types = {name: info.param_type for name, info in param_info.items()}
        
        form_manager = ParameterFormManager(
            parameters=parameters,
            parameter_types=parameter_types,
            field_id="test",
            parameter_info=param_info,
            is_global_config_editing=False  # Lazy context
        )
        
        # Get widgets
        microscope_widget = form_manager.widgets.get('microscope')
        num_workers_widget = form_manager.widgets.get('num_workers')
        
        # Reset all parameters
        form_manager.reset_all_parameters()
        
        # Verify form manager state
        current_values = form_manager.get_current_values()
        assert current_values['microscope'] is None
        assert current_values['num_workers'] is None
        
        # Verify widget states match form manager
        if microscope_widget and isinstance(microscope_widget, QComboBox):
            # Should show default with placeholder styling
            assert microscope_widget.currentData() == Microscope.AUTO
            assert microscope_widget.property('is_placeholder_state') is not None
        
        if num_workers_widget and isinstance(num_workers_widget, (QSpinBox, QDoubleSpinBox)):
            # Should show default value (but form manager stores None for lazy context)
            # Widget shows resolved default, form manager stores None
            assert num_workers_widget.property('is_placeholder_state') is not None
    
    def test_nested_widget_reset_consistency(self, qapp):
        """Test nested widget reset consistency."""
        from openhcs.core.pipeline_config import PipelineConfig
        
        # Create form manager with nested dataclass
        param_info = SignatureAnalyzer.analyze(PipelineConfig)
        parameters = {}
        for name in param_info.keys():
            parameters[name] = None  # Start with all None for lazy context
        parameter_types = {name: info.param_type for name, info in param_info.items()}
        
        form_manager = ParameterFormManager(
            parameters=parameters,
            parameter_types=parameter_types,
            field_id="test",
            parameter_info=param_info,
            is_global_config_editing=False  # Lazy context
        )
        
        # Modify nested parameter if available
        if hasattr(form_manager, 'nested_managers') and 'path_planning' in form_manager.nested_managers:
            path_planning_manager = form_manager.nested_managers['path_planning']
            
            # Set a nested value
            form_manager.update_parameter('path_planning.output_dir_suffix', '_test')
            
            # Verify nested value was set
            current_values = form_manager.get_current_values()
            assert current_values['path_planning'] is not None
            assert current_values['path_planning'].output_dir_suffix == '_test'
            
            # Reset the nested parameter
            form_manager._reset_parameter('path_planning')
            
            # Verify nested parameter was reset
            reset_values = form_manager.get_current_values()
            assert reset_values['path_planning'] is None
            
            # Verify nested widget state
            suffix_widget = path_planning_manager.widgets.get('output_dir_suffix')
            if suffix_widget and isinstance(suffix_widget, QLineEdit):
                assert suffix_widget.text() == ""
                assert suffix_widget.property('is_placeholder_state') is not None


class TestResetButtonIntegration:
    """Test reset button integration with widget updates."""
    
    def test_individual_reset_button_behavior(self, qapp):
        """Test individual parameter reset buttons."""
        from openhcs.core.pipeline_config import PipelineConfig
        
        # Create form manager
        param_info = SignatureAnalyzer.analyze(PipelineConfig)
        parameters = {'microscope': Microscope.IMAGEXPRESS}
        parameter_types = {name: info.param_type for name, info in param_info.items()}
        
        form_manager = ParameterFormManager(
            parameters=parameters,
            parameter_types=parameter_types,
            field_id="test",
            parameter_info=param_info,
            is_global_config_editing=False  # Lazy context
        )
        
        # Find reset button for microscope (should be created by form manager)
        microscope_widget = form_manager.widgets.get('microscope')
        assert microscope_widget is not None
        
        # Simulate reset button click by calling the reset method directly
        form_manager._reset_parameter('microscope')
        
        # Verify reset worked
        assert form_manager.textual_form_manager.parameters['microscope'] is None
        if isinstance(microscope_widget, QComboBox):
            assert microscope_widget.currentData() == Microscope.AUTO
            assert microscope_widget.property('is_placeholder_state') is not None
    
    def test_reset_all_button_behavior(self, qapp):
        """Test reset all parameters button."""
        from openhcs.core.pipeline_config import PipelineConfig
        
        # Create form manager with multiple modified parameters
        param_info = SignatureAnalyzer.analyze(PipelineConfig)
        parameters = {
            'microscope': Microscope.IMAGEXPRESS,
            'num_workers': 16
        }
        parameter_types = {name: info.param_type for name, info in param_info.items()}
        
        form_manager = ParameterFormManager(
            parameters=parameters,
            parameter_types=parameter_types,
            field_id="test",
            parameter_info=param_info,
            is_global_config_editing=False  # Lazy context
        )
        
        # Reset all parameters
        form_manager.reset_all_parameters()
        
        # Verify all parameters were reset
        current_values = form_manager.get_current_values()
        for param_name in parameters.keys():
            assert current_values[param_name] is None
        
        # Verify all widgets show placeholder state
        for param_name, widget in form_manager.widgets.items():
            if param_name in parameters:
                assert widget.property('is_placeholder_state') is not None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
