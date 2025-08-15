#!/usr/bin/env python3
"""
Comprehensive tests for dual editor reset functionality.

Tests both step editor and function pattern editor reset behavior,
including widget state validation, placeholder text display, and
enum dropdown functionality.
"""

import pytest
import sys
import os
from typing import Dict, Any, List
from unittest.mock import Mock, patch

# Add project root to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..')))

from PyQt6.QtWidgets import QApplication, QComboBox, QLineEdit, QCheckBox, QSpinBox
from PyQt6.QtCore import Qt
from PyQt6.QtTest import QTest

from openhcs.core.config import Microscope
from openhcs.core.pipeline_config import PipelineConfig
from openhcs.core.steps.function_step import FunctionStep
from openhcs.constants.constants import VariableComponents, GroupBy
from openhcs.pyqt_gui.widgets.step_parameter_editor import StepParameterEditorWidget
from openhcs.pyqt_gui.widgets.function_pane import FunctionPaneWidget
from openhcs.pyqt_gui.windows.dual_editor_window import DualEditorWindow
from openhcs.textual_tui.widgets.shared.signature_analyzer import SignatureAnalyzer


@pytest.fixture(scope="module")
def qapp():
    """Create QApplication instance for tests."""
    app = QApplication.instance()
    if app is None:
        app = QApplication([])
    yield app
    # Don't quit the app here as it might be used by other tests


@pytest.fixture
def mock_service_adapter():
    """Create a mock service adapter for testing."""
    adapter = Mock()
    adapter.show_error_dialog = Mock()
    adapter.show_info_dialog = Mock()
    return adapter


@pytest.fixture
def sample_function_step():
    """Create a sample function step for testing."""
    from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize

    step = FunctionStep(
        name="test_step",
        func=stack_percentile_normalize,
        group_by=GroupBy.WELL,
        variable_components=[VariableComponents.WELL],
        kwargs={"low_percentile": 1.0, "high_percentile": 99.0, "target_max": 65535.0}
    )
    return step


@pytest.fixture
def sample_pipeline_config():
    """Create a sample pipeline config for testing."""
    return PipelineConfig(
        microscope=Microscope.OPERAPHENIX,
        num_workers=8
    )


class TestStepParameterEditorReset:
    """Test step parameter editor reset functionality."""
    
    def test_step_editor_individual_parameter_reset(self, qapp, mock_service_adapter, sample_function_step):
        """Test individual parameter reset in step editor."""
        editor = StepParameterEditorWidget(
            step=sample_function_step,
            service_adapter=mock_service_adapter
        )
        
        # Modify a parameter
        original_low_percentile = editor.step.low_percentile
        editor.step.low_percentile = 5.0
        editor.form_manager.update_parameter('low_percentile', 5.0)

        # Verify parameter was changed
        assert editor.step.low_percentile == 5.0

        # Reset the parameter
        editor.reset_parameter('low_percentile')

        # Verify parameter was reset to default
        assert editor.step.low_percentile == original_low_percentile

        # Verify form manager was updated
        current_values = editor.form_manager.get_current_values()
        assert current_values['low_percentile'] == original_low_percentile
    
    def test_step_editor_reset_all_parameters(self, qapp, mock_service_adapter, sample_function_step):
        """Test reset all parameters in step editor."""
        editor = StepParameterEditorWidget(
            step=sample_function_step,
            service_adapter=mock_service_adapter
        )
        
        # Store original values
        original_values = {}
        for param_name in editor.param_defaults.keys():
            original_values[param_name] = getattr(editor.step, param_name)
        
        # Modify multiple parameters
        if hasattr(editor.step, 'low_percentile'):
            editor.step.low_percentile = 5.0
            editor.form_manager.update_parameter('low_percentile', 5.0)

        if hasattr(editor.step, 'high_percentile'):
            editor.step.high_percentile = 95.0
            editor.form_manager.update_parameter('high_percentile', 95.0)
        
        # Reset all parameters
        editor.reset_all_parameters()
        
        # Verify all parameters were reset
        for param_name, original_value in original_values.items():
            current_value = getattr(editor.step, param_name)
            assert current_value == original_value, f"Parameter {param_name} not reset correctly"
    
    def test_step_editor_enum_widget_reset(self, qapp, mock_service_adapter, sample_function_step):
        """Test enum widget reset behavior in step editor."""
        editor = StepParameterEditorWidget(
            step=sample_function_step,
            service_adapter=mock_service_adapter
        )
        
        # Find enum widgets (GroupBy, VariableComponents)
        group_by_widget = None
        variable_components_widget = None
        
        for param_name, widget in editor.form_manager.widgets.items():
            if param_name == 'group_by' and isinstance(widget, QComboBox):
                group_by_widget = widget
            elif param_name == 'variable_components' and isinstance(widget, QComboBox):
                variable_components_widget = widget
        
        if group_by_widget:
            # Change group_by value
            original_group_by = editor.step.group_by
            new_group_by = GroupBy.SITE if original_group_by != GroupBy.SITE else GroupBy.WELL
            
            # Find the index for the new value
            for i in range(group_by_widget.count()):
                if group_by_widget.itemData(i) == new_group_by:
                    group_by_widget.setCurrentIndex(i)
                    break
            
            editor.step.group_by = new_group_by
            
            # Reset the parameter
            editor.reset_parameter('group_by')
            
            # Verify widget shows original value
            assert group_by_widget.currentData() == original_group_by
            assert editor.step.group_by == original_group_by


class TestFunctionPaneReset:
    """Test function pane reset functionality."""
    
    def test_function_pane_reset_all_parameters(self, qapp, mock_service_adapter):
        """Test reset all parameters in function pane."""
        from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize

        func_item = (stack_percentile_normalize, {"low_percentile": 5.0, "high_percentile": 95.0})
        pane = FunctionPaneWidget(
            func_item=func_item,
            index=0,
            service_adapter=mock_service_adapter
        )
        
        # Store original defaults
        original_defaults = pane.param_defaults.copy()
        
        # Modify parameters
        pane._internal_kwargs['low_percentile'] = 10.0
        pane._internal_kwargs['high_percentile'] = 90.0
        
        # Reset all parameters
        pane.reset_all_parameters()
        
        # Verify parameters were reset to defaults
        for param_name, default_value in original_defaults.items():
            assert pane._internal_kwargs[param_name] == default_value
    
    def test_function_pane_enhanced_form_manager_reset(self, qapp, mock_service_adapter):
        """Test that function pane uses enhanced form manager for reset."""
        from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize

        func_item = (stack_percentile_normalize, {"low_percentile": 1.0})
        pane = FunctionPaneWidget(
            func_item=func_item,
            index=0,
            service_adapter=mock_service_adapter
        )
        
        # Verify enhanced form manager exists
        assert hasattr(pane, 'enhanced_form_manager')
        assert pane.enhanced_form_manager is not None
        
        # Mock the enhanced form manager's reset method
        with patch.object(pane.enhanced_form_manager, 'reset_all_parameters') as mock_reset:
            pane.reset_all_parameters()
            
            # Verify enhanced form manager reset was called
            mock_reset.assert_called_once()
    
    def test_function_pane_widget_state_after_reset(self, qapp, mock_service_adapter):
        """Test widget state consistency after reset in function pane."""
        from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize

        func_item = (stack_percentile_normalize, {"low_percentile": 5.0, "target_max": 32767.0})
        pane = FunctionPaneWidget(
            func_item=func_item,
            index=0,
            service_adapter=mock_service_adapter
        )

        # Find widgets
        low_percentile_widget = None
        target_max_widget = None

        if hasattr(pane, 'enhanced_form_manager') and pane.enhanced_form_manager:
            widgets = pane.enhanced_form_manager.widgets
            low_percentile_widget = widgets.get('low_percentile')
            target_max_widget = widgets.get('target_max')

        # Test float widget reset
        if low_percentile_widget and isinstance(low_percentile_widget, (QSpinBox, QDoubleSpinBox)):
            # Change value
            low_percentile_widget.setValue(10.0)

            # Reset
            pane.reset_all_parameters()

            # Verify widget state matches default
            expected_state = pane.param_defaults.get('low_percentile', 1.0)
            assert low_percentile_widget.value() == expected_state

        # Test target_max widget reset
        if target_max_widget and isinstance(target_max_widget, (QSpinBox, QDoubleSpinBox)):
            # Change value
            target_max_widget.setValue(99999.0)

            # Reset
            pane.reset_all_parameters()

            # Verify widget state matches default
            expected_value = pane.param_defaults.get('target_max', 65535.0)
            assert target_max_widget.value() == expected_value


class TestDualEditorIntegration:
    """Test dual editor window integration."""
    
    def test_dual_editor_step_tab_reset(self, qapp, mock_service_adapter, sample_function_step):
        """Test reset functionality in dual editor step tab."""
        # Note: This test may need to be adjusted based on actual DualEditorWindow implementation
        # For now, we'll test the step editor component directly
        
        step_editor = StepParameterEditorWidget(
            step=sample_function_step,
            service_adapter=mock_service_adapter
        )
        
        # Modify parameters
        original_low_percentile = getattr(sample_function_step, 'low_percentile', 1.0)
        step_editor.step.low_percentile = 10.0

        # Reset all
        step_editor.reset_all_parameters()

        # Verify reset
        assert step_editor.step.low_percentile == original_low_percentile
    
    def test_dual_editor_function_tab_reset(self, qapp, mock_service_adapter):
        """Test reset functionality in dual editor function tab."""
        from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize

        func_item = (stack_percentile_normalize, {"low_percentile": 1.0})
        function_pane = FunctionPaneWidget(
            func_item=func_item,
            index=0,
            service_adapter=mock_service_adapter
        )

        # Modify parameters
        function_pane._internal_kwargs['low_percentile'] = 10.0

        # Reset all
        function_pane.reset_all_parameters()

        # Verify reset
        expected_default = function_pane.param_defaults.get('low_percentile', 1.0)
        assert function_pane._internal_kwargs['low_percentile'] == expected_default


class TestPlaceholderTextBehavior:
    """Test placeholder text behavior after reset operations."""
    
    def test_lazy_dataclass_placeholder_after_reset(self, qapp, sample_pipeline_config):
        """Test placeholder text display for lazy dataclass fields after reset."""
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        
        # Create form manager for lazy config editing
        param_info = SignatureAnalyzer.analyze(PipelineConfig)
        parameters = {}
        for name in param_info.keys():
            parameters[name] = getattr(sample_pipeline_config, name, None)
        parameter_types = {name: info.param_type for name, info in param_info.items()}
        
        form_manager = ParameterFormManager(
            parameters=parameters,
            parameter_types=parameter_types,
            field_id="config",
            parameter_info=param_info,
            is_global_config_editing=False  # Lazy context
        )
        
        # Find microscope widget
        microscope_widget = form_manager.widgets.get('microscope')
        
        if microscope_widget and isinstance(microscope_widget, QComboBox):
            # Change microscope value
            for i in range(microscope_widget.count()):
                if microscope_widget.itemData(i) == Microscope.IMAGEXPRESS:
                    microscope_widget.setCurrentIndex(i)
                    break
            
            # Reset parameter
            form_manager._reset_parameter('microscope')
            
            # Verify placeholder behavior
            assert form_manager.textual_form_manager.parameters['microscope'] is None
            assert microscope_widget.property('is_placeholder_state') is not None
            
            # Should show AUTO (the resolved default) with placeholder styling
            assert microscope_widget.currentData() == Microscope.AUTO
    
    def test_string_field_placeholder_after_reset(self, qapp, sample_pipeline_config):
        """Test string field placeholder behavior after reset."""
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        
        # Create form manager
        param_info = SignatureAnalyzer.analyze(PipelineConfig)
        parameters = {}
        for name in param_info.keys():
            parameters[name] = getattr(sample_pipeline_config, name, None)
        parameter_types = {name: info.param_type for name, info in param_info.items()}
        
        form_manager = ParameterFormManager(
            parameters=parameters,
            parameter_types=parameter_types,
            field_id="config",
            parameter_info=param_info,
            is_global_config_editing=False  # Lazy context
        )
        
        # Test nested string field if available
        if hasattr(form_manager, 'nested_managers') and 'path_planning' in form_manager.nested_managers:
            path_planning_manager = form_manager.nested_managers['path_planning']
            output_dir_suffix_widget = path_planning_manager.widgets.get('output_dir_suffix')
            
            if output_dir_suffix_widget and isinstance(output_dir_suffix_widget, QLineEdit):
                # Set a value
                output_dir_suffix_widget.setText("_test_value")
                path_planning_manager.textual_form_manager.parameters['output_dir_suffix'] = "_test_value"
                
                # Reset
                path_planning_manager._reset_parameter('output_dir_suffix')
                
                # Verify placeholder behavior
                assert path_planning_manager.textual_form_manager.parameters['output_dir_suffix'] is None
                assert output_dir_suffix_widget.text() == ""
                assert output_dir_suffix_widget.placeholderText() != ""
                assert output_dir_suffix_widget.property('is_placeholder_state') is not None


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
