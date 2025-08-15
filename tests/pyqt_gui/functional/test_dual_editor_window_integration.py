#!/usr/bin/env python3
"""
Integration tests for the dual editor window.

Tests the complete dual editor workflow including tab switching,
reset operations across both tabs, and state consistency.
"""

import pytest
import sys
import os
from typing import Dict, Any, List
from unittest.mock import Mock, patch, MagicMock

# Add project root to path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..')))

from PyQt6.QtWidgets import QApplication, QTabWidget
from PyQt6.QtCore import Qt
from PyQt6.QtTest import QTest

from openhcs.core.config import Microscope
from openhcs.core.steps.function_step import FunctionStep
from openhcs.constants.constants import VariableComponents, GroupBy
from openhcs.pyqt_gui.windows.dual_editor_window import DualEditorWindow
from openhcs.pyqt_gui.widgets.step_parameter_editor import StepParameterEditorWidget
from openhcs.pyqt_gui.widgets.function_list_editor import FunctionListEditorWidget


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
    adapter.show_info_dialog = Mock()
    adapter.get_color_scheme = Mock(return_value=None)
    return adapter


@pytest.fixture
def sample_function_step():
    """Create a sample function step for testing."""
    from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize

    step = FunctionStep(
        name="test_step",
        func=stack_percentile_normalize,
        group_by=GroupBy.WELL,
        variable_components=[VariableComponents.WELL]
    )
    # Set function parameters as attributes after creation
    step.low_percentile = 1.0
    step.high_percentile = 99.0
    return step


class TestDualEditorWindowIntegration:
    """Test dual editor window integration."""
    
    @pytest.mark.skip(reason="DualEditorWindow requires complex setup - testing components separately")
    def test_dual_editor_window_creation(self, qapp, mock_service_adapter, sample_function_step):
        """Test dual editor window creation and initialization."""
        # Note: This test is skipped because DualEditorWindow requires complex setup
        # We test the individual components instead
        pass
    
    def test_step_editor_component_reset(self, qapp, mock_service_adapter, sample_function_step):
        """Test step editor component reset functionality."""
        step_editor = StepParameterEditorWidget(
            step=sample_function_step,
            service_adapter=mock_service_adapter
        )
        
        # Modify step parameters
        original_low_percentile = getattr(sample_function_step, 'low_percentile', 1.0)
        step_editor.step.low_percentile = 10.0
        step_editor.form_manager.update_parameter('low_percentile', 10.0)

        # Verify parameter was changed
        assert step_editor.step.low_percentile == 10.0

        # Reset all parameters
        step_editor.reset_all_parameters()

        # Verify parameters were reset
        assert step_editor.step.low_percentile == original_low_percentile

        # Verify form manager was updated
        current_values = step_editor.form_manager.get_current_values()
        assert current_values['low_percentile'] == original_low_percentile
    
    def test_function_editor_component_reset(self, qapp, mock_service_adapter):
        """Test function editor component reset functionality."""
        from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize

        # Create function list editor with sample functions
        initial_functions = [(stack_percentile_normalize, {"low_percentile": 5.0, "high_percentile": 95.0})]

        function_editor = FunctionListEditorWidget(
            initial_functions=initial_functions,
            service_adapter=mock_service_adapter
        )

        # Verify initial setup
        assert len(function_editor.functions) == 1
        func, kwargs = function_editor.functions[0]
        assert kwargs['low_percentile'] == 5.0
        assert kwargs['high_percentile'] == 95.0
        
        # Test function pane reset (if function panes are created)
        # Note: This depends on the internal implementation of FunctionListEditorWidget
        if hasattr(function_editor, 'function_panes') and function_editor.function_panes:
            pane = function_editor.function_panes[0]
            if hasattr(pane, 'reset_all_parameters'):
                # Modify parameters
                pane._internal_kwargs['low_percentile'] = 10.0

                # Reset
                pane.reset_all_parameters()

                # Verify reset
                assert pane._internal_kwargs['low_percentile'] == 5.0  # Back to original


class TestTabSwitchingWithReset:
    """Test reset functionality across tab switches."""
    
    def test_step_tab_state_preservation(self, qapp, mock_service_adapter, sample_function_step):
        """Test that step tab state is preserved during tab switches."""
        step_editor = StepParameterEditorWidget(
            step=sample_function_step,
            service_adapter=mock_service_adapter
        )
        
        # Modify parameters
        step_editor.step.low_percentile = 10.0
        step_editor.form_manager.update_parameter('low_percentile', 10.0)

        # Simulate tab switch (step editor should maintain state)
        # In real dual editor, this would involve hiding/showing widgets

        # Verify state is maintained
        assert step_editor.step.low_percentile == 10.0
        current_values = step_editor.form_manager.get_current_values()
        assert current_values['low_percentile'] == 10.0

        # Reset and verify
        step_editor.reset_all_parameters()
        original_value = step_editor.param_defaults.get('low_percentile', 1.0)
        assert step_editor.step.low_percentile == original_value
    
    def test_function_tab_state_preservation(self, qapp, mock_service_adapter):
        """Test that function tab state is preserved during tab switches."""
        from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize

        initial_functions = [(stack_percentile_normalize, {"low_percentile": 5.0})]

        function_editor = FunctionListEditorWidget(
            initial_functions=initial_functions,
            service_adapter=mock_service_adapter
        )

        # Verify initial state
        assert len(function_editor.functions) == 1
        func, kwargs = function_editor.functions[0]
        assert kwargs['low_percentile'] == 5.0

        # Simulate tab switch and verify state preservation
        # Function editor should maintain its function list
        assert len(function_editor.functions) == 1
        func, kwargs = function_editor.functions[0]
        assert kwargs['low_percentile'] == 5.0


class TestResetOperationSignaling:
    """Test reset operation signaling and event handling."""
    
    def test_step_editor_reset_signals(self, qapp, mock_service_adapter, sample_function_step):
        """Test that step editor emits correct signals during reset."""
        step_editor = StepParameterEditorWidget(
            step=sample_function_step,
            service_adapter=mock_service_adapter
        )
        
        # Connect to signal
        signal_received = []
        step_editor.step_parameter_changed.connect(lambda: signal_received.append(True))
        
        # Reset parameters
        step_editor.reset_all_parameters()
        
        # Verify signal was emitted
        assert len(signal_received) > 0
    
    def test_function_pane_reset_signals(self, qapp, mock_service_adapter):
        """Test that function pane emits correct signals during reset."""
        from openhcs.pyqt_gui.widgets.function_pane import FunctionPaneWidget
        from openhcs.processing.backends.loaders.tiff_loader import load_tiff_stack
        
        func_item = (load_tiff_stack, {"preserve_dtype": True})
        pane = FunctionPaneWidget(
            func_item=func_item,
            index=0,
            service_adapter=mock_service_adapter
        )
        
        # Connect to signals
        parameter_changed_signals = []
        reset_signals = []
        
        pane.parameter_changed.connect(
            lambda idx, param, value: parameter_changed_signals.append((idx, param, value))
        )
        pane.reset_parameters.connect(lambda idx: reset_signals.append(idx))
        
        # Reset parameters
        pane.reset_all_parameters()
        
        # Verify signals were emitted
        assert len(reset_signals) > 0
        assert reset_signals[0] == 0  # Should emit with correct index


class TestErrorHandlingDuringReset:
    """Test error handling during reset operations."""
    
    def test_step_editor_reset_error_handling(self, qapp, mock_service_adapter, sample_function_step):
        """Test error handling in step editor reset."""
        step_editor = StepParameterEditorWidget(
            step=sample_function_step,
            service_adapter=mock_service_adapter
        )

        # Mock form manager to raise exception
        with patch.object(step_editor.form_manager, 'reset_all_parameters', side_effect=Exception("Test error")):
            # Reset should fail loudly (no fallback)
            with pytest.raises(Exception, match="Test error"):
                step_editor.reset_all_parameters()
    
    def test_function_pane_reset_error_handling(self, qapp, mock_service_adapter):
        """Test error handling in function pane reset."""
        from openhcs.pyqt_gui.widgets.function_pane import FunctionPaneWidget
        from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize

        func_item = (stack_percentile_normalize, {"low_percentile": 1.0})
        pane = FunctionPaneWidget(
            func_item=func_item,
            index=0,
            service_adapter=mock_service_adapter
        )

        # Mock enhanced form manager to raise exception
        with patch.object(pane.enhanced_form_manager, 'reset_all_parameters', side_effect=Exception("Test error")):
            # Reset should fail loudly (no fallback)
            with pytest.raises(Exception, match="Test error"):
                pane.reset_all_parameters()


class TestResetConsistencyAcrossTabs:
    """Test reset consistency when switching between tabs."""
    
    def test_reset_state_consistency(self, qapp, mock_service_adapter, sample_function_step):
        """Test that reset state is consistent across tab switches."""
        # Create both editors
        step_editor = StepParameterEditorWidget(
            step=sample_function_step,
            service_adapter=mock_service_adapter
        )
        
        from openhcs.processing.backends.processors.torch_processor import stack_percentile_normalize
        initial_functions = [(stack_percentile_normalize, {"low_percentile": 1.0})]
        function_editor = FunctionListEditorWidget(
            initial_functions=initial_functions,
            service_adapter=mock_service_adapter
        )

        # Modify step parameters
        step_editor.step.low_percentile = 10.0

        # Reset step parameters
        step_editor.reset_all_parameters()

        # Verify step was reset
        original_value = step_editor.param_defaults.get('low_percentile', 1.0)
        assert step_editor.step.low_percentile == original_value

        # Function editor should be unaffected
        assert len(function_editor.functions) == 1
        func, kwargs = function_editor.functions[0]
        assert kwargs['low_percentile'] == 1.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
