"""
Test inheritance hierarchy behavior in parameter form managers.

This test verifies that placeholder inheritance works correctly:
1. step_well_filter_config changes should update step_materialization_config placeholders
2. path_planning_config changes should NOT affect step_materialization_config placeholders
3. Inheritance hierarchy is respected, not just field name matching
"""

import pytest
from unittest.mock import Mock, patch
from PyQt6.QtWidgets import QApplication, QWidget, QLineEdit
from PyQt6.QtCore import QTimer

from openhcs.core.config import GlobalPipelineConfig, StepWellFilterConfig, StepMaterializationConfig, PathPlanningConfig, WellFilterMode
from openhcs.core.lazy_config import LazyStepWellFilterConfig, LazyStepMaterializationConfig, LazyPathPlanningConfig
from openhcs.core.context.global_config import set_current_global_config, get_current_global_config
from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme


@pytest.fixture
def qtapp():
    """Ensure QApplication exists for PyQt6 tests."""
    app = QApplication.instance()
    if app is None:
        app = QApplication([])
    yield app


@pytest.fixture
def sample_global_config():
    """Create a sample global configuration for testing."""
    return GlobalPipelineConfig(
        num_workers=1,
        step_well_filter_config=StepWellFilterConfig(
            well_filter=1,  # This is the source value for inheritance
            well_filter_mode=WellFilterMode.INCLUDE
        ),
        step_materialization_config=StepMaterializationConfig(
            well_filter=None,  # This should inherit from step_well_filter_config
            well_filter_mode=WellFilterMode.INCLUDE,
            output_dir_suffix='_openhcs',
            global_output_folder=None,
            sub_dir='checkpoints'
        ),
        path_planning_config=PathPlanningConfig(
            well_filter=None,  # This should inherit from step_well_filter_config
            well_filter_mode=WellFilterMode.INCLUDE,
            output_dir_suffix='_openhcs',
            global_output_folder=None,
            sub_dir='images'
        )
    )


@pytest.fixture
def step_well_filter_manager(qtapp, sample_global_config):
    """Create a parameter form manager for step_well_filter_config."""
    set_current_global_config(GlobalPipelineConfig, sample_global_config)
    
    # Create lazy dataclass instance
    lazy_config = LazyStepWellFilterConfig()
    
    # Extract parameters
    parameters = {
        'well_filter': lazy_config.well_filter,
        'well_filter_mode': lazy_config.well_filter_mode
    }
    
    parameter_types = {
        'well_filter': int,
        'well_filter_mode': WellFilterMode
    }
    
    manager = ParameterFormManager(
        parameters=parameters,
        parameter_types=parameter_types,
        field_id="step_well_filter_config",
        dataclass_type=LazyStepWellFilterConfig,
        parameter_info=None,
        parent=None,
        use_scroll_area=False,
        function_target=None,
        color_scheme=PyQt6ColorScheme(),
        placeholder_prefix="Pipeline default"
    )
    
    return manager


@pytest.fixture
def step_materialization_manager(qtapp, sample_global_config):
    """Create a parameter form manager for step_materialization_config."""
    set_current_global_config(GlobalPipelineConfig, sample_global_config)
    
    # Create lazy dataclass instance
    lazy_config = LazyStepMaterializationConfig()
    
    # Extract parameters
    parameters = {
        'well_filter': lazy_config.well_filter,
        'well_filter_mode': lazy_config.well_filter_mode,
        'output_dir_suffix': lazy_config.output_dir_suffix,
        'global_output_folder': lazy_config.global_output_folder,
        'sub_dir': lazy_config.sub_dir
    }
    
    parameter_types = {
        'well_filter': int,
        'well_filter_mode': WellFilterMode,
        'output_dir_suffix': str,
        'global_output_folder': str,
        'sub_dir': str
    }
    
    manager = ParameterFormManager(
        parameters=parameters,
        parameter_types=parameter_types,
        field_id="step_materialization_config",
        dataclass_type=LazyStepMaterializationConfig,
        parameter_info=None,
        parent=None,
        use_scroll_area=False,
        function_target=None,
        color_scheme=PyQt6ColorScheme(),
        placeholder_prefix="Pipeline default"
    )
    
    return manager


@pytest.fixture
def path_planning_manager(qtapp, sample_global_config):
    """Create a parameter form manager for path_planning_config."""
    set_current_global_config(GlobalPipelineConfig, sample_global_config)
    
    # Create lazy dataclass instance
    lazy_config = LazyPathPlanningConfig()
    
    # Extract parameters
    parameters = {
        'well_filter': lazy_config.well_filter,
        'well_filter_mode': lazy_config.well_filter_mode,
        'output_dir_suffix': lazy_config.output_dir_suffix,
        'global_output_folder': lazy_config.global_output_folder,
        'sub_dir': lazy_config.sub_dir
    }
    
    parameter_types = {
        'well_filter': int,
        'well_filter_mode': WellFilterMode,
        'output_dir_suffix': str,
        'global_output_folder': str,
        'sub_dir': str
    }
    
    manager = ParameterFormManager(
        parameters=parameters,
        parameter_types=parameter_types,
        field_id="path_planning_config",
        dataclass_type=LazyPathPlanningConfig,
        parameter_info=None,
        parent=None,
        use_scroll_area=False,
        function_target=None,
        color_scheme=PyQt6ColorScheme(),
        placeholder_prefix="Pipeline default"
    )
    
    return manager


class TestParameterFormInheritance:
    """Test inheritance hierarchy behavior in parameter form managers."""
    
    def test_step_well_filter_inheritance_to_step_materialization(
        self, step_well_filter_manager, step_materialization_manager, sample_global_config
    ):
        """
        Test that changing step_well_filter_config.well_filter updates 
        step_materialization_config.well_filter placeholder.
        """
        # Setup: Create a mock sibling relationship
        step_well_filter_manager.nested_managers = {
            'step_materialization_config': step_materialization_manager
        }
        
        # Get initial placeholder text for step_materialization_config.well_filter
        initial_placeholder = step_materialization_manager.widgets['well_filter'].placeholderText()
        print(f"Initial step_materialization placeholder: '{initial_placeholder}'")
        
        # Should show inheritance from step_well_filter_config (value=1)
        assert "Pipeline default: 1" in initial_placeholder
        
        # Change step_well_filter_config.well_filter to a new value
        new_value = LazyStepWellFilterConfig(well_filter=42, well_filter_mode=WellFilterMode.INCLUDE)
        
        # Simulate the parameter change that triggers sibling updates
        step_well_filter_manager._update_sibling_placeholders_with_updated_context(
            'step_well_filter_config', new_value
        )
        
        # Check that step_materialization_config.well_filter placeholder updated
        updated_placeholder = step_materialization_manager.widgets['well_filter'].placeholderText()
        print(f"Updated step_materialization placeholder: '{updated_placeholder}'")
        
        # Should now show inheritance from the new step_well_filter_config value
        assert "Pipeline default: 42" in updated_placeholder
        assert "Pipeline default: 1" not in updated_placeholder
    
    def test_path_planning_does_not_affect_step_materialization(
        self, path_planning_manager, step_materialization_manager, sample_global_config
    ):
        """
        Test that changing path_planning_config.well_filter does NOT affect 
        step_materialization_config.well_filter placeholder.
        """
        # Setup: Create a mock sibling relationship
        path_planning_manager.nested_managers = {
            'step_materialization_config': step_materialization_manager
        }
        
        # Get initial placeholder text for step_materialization_config.well_filter
        initial_placeholder = step_materialization_manager.widgets['well_filter'].placeholderText()
        print(f"Initial step_materialization placeholder: '{initial_placeholder}'")
        
        # Should show inheritance from step_well_filter_config (value=1)
        assert "Pipeline default: 1" in initial_placeholder
        
        # Change path_planning_config.well_filter to a different value
        new_value = LazyPathPlanningConfig(well_filter=99, well_filter_mode=WellFilterMode.INCLUDE)
        
        # Simulate the parameter change that triggers sibling updates
        path_planning_manager._update_sibling_placeholders_with_updated_context(
            'path_planning_config', new_value
        )
        
        # Check that step_materialization_config.well_filter placeholder DID NOT change
        unchanged_placeholder = step_materialization_manager.widgets['well_filter'].placeholderText()
        print(f"Unchanged step_materialization placeholder: '{unchanged_placeholder}'")
        
        # Should still show inheritance from step_well_filter_config (value=1), not path_planning (value=99)
        assert "Pipeline default: 1" in unchanged_placeholder
        assert "Pipeline default: 99" not in unchanged_placeholder
    
    def test_inheritance_hierarchy_sequence(
        self, step_well_filter_manager, step_materialization_manager, path_planning_manager, sample_global_config
    ):
        """
        Test the complete sequence:
        1. step_well_filter changes -> step_materialization updates
        2. path_planning changes -> step_materialization stays the same
        """
        # Setup sibling relationships
        step_well_filter_manager.nested_managers = {
            'step_materialization_config': step_materialization_manager
        }
        path_planning_manager.nested_managers = {
            'step_materialization_config': step_materialization_manager
        }
        
        # Step 1: Change step_well_filter_config.well_filter
        step_well_filter_value = LazyStepWellFilterConfig(well_filter=55, well_filter_mode=WellFilterMode.INCLUDE)
        step_well_filter_manager._update_sibling_placeholders_with_updated_context(
            'step_well_filter_config', step_well_filter_value
        )
        
        # Verify step_materialization_config inherits from step_well_filter_config
        placeholder_after_step_change = step_materialization_manager.widgets['well_filter'].placeholderText()
        print(f"After step_well_filter change: '{placeholder_after_step_change}'")
        assert "Pipeline default: 55" in placeholder_after_step_change
        
        # Step 2: Change path_planning_config.well_filter to a different value
        path_planning_value = LazyPathPlanningConfig(well_filter=77, well_filter_mode=WellFilterMode.INCLUDE)
        path_planning_manager._update_sibling_placeholders_with_updated_context(
            'path_planning_config', path_planning_value
        )
        
        # Verify step_materialization_config STILL inherits from step_well_filter_config (not path_planning)
        placeholder_after_path_change = step_materialization_manager.widgets['well_filter'].placeholderText()
        print(f"After path_planning change: '{placeholder_after_path_change}'")
        assert "Pipeline default: 55" in placeholder_after_path_change  # Still from step_well_filter
        assert "Pipeline default: 77" not in placeholder_after_path_change  # Not from path_planning

    def test_reset_inheritance_behavior(self, step_well_filter_manager, step_materialization_manager, sample_global_config):
        """
        Test reset behavior for inheritance:
        1. Modify step_well_filter_config.well_filter to 999
        2. Reset step_materialization_config.well_filter (should work - inherits from step_well_filter)
        3. Reset step_well_filter_config.well_filter (should work - inherits from well_filter_config)
        """
        # Setup sibling relationship for inheritance
        step_well_filter_manager.nested_managers = {
            'step_materialization_config': step_materialization_manager
        }

        # Step 1: Modify step_well_filter_config.well_filter to 999
        step_well_filter_manager.update_parameter('well_filter', 999)
        assert step_well_filter_manager.parameters['well_filter'] == 999
        print(f"✅ Set step_well_filter_config.well_filter = 999")

        # Step 2: Reset step_materialization_config.well_filter (should work - inherits from step_well_filter)
        step_materialization_manager.reset_parameter('well_filter')
        reset_value_materialization = step_materialization_manager.parameters['well_filter']

        # Should reset to None and inherit from step_well_filter_config
        assert reset_value_materialization is None, f"Expected None for inheritance, got: {reset_value_materialization}"
        print("✅ step_materialization_config.well_filter reset to None (inheritance works)")

        # Step 3: Reset step_well_filter_config.well_filter (FIXED - should now work with multiple inheritance)
        step_well_filter_manager.reset_parameter('well_filter')
        reset_value_step_filter = step_well_filter_manager.parameters['well_filter']

        # FIXED: step_well_filter should reset to None and show inheritance placeholder from WellFilterConfig
        assert reset_value_step_filter is None, f"Expected None for inheritance, got: {reset_value_step_filter}"
        print("✅ step_well_filter_config.well_filter reset to None (multiple inheritance fixed!)")

        print("✅ MULTIPLE INHERITANCE RESET: Fixed! All fields reset to None and show proper inheritance!")
