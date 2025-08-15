"""
Unit tests for the generic component framework.

This module tests the new generic component system including ComponentConfiguration,
MultiprocessingCoordinator, GenericValidator, and GenericPatternEngine.
"""

import pytest
from enum import Enum
from unittest.mock import Mock, MagicMock

from openhcs.core.components.framework import ComponentConfiguration, ComponentConfigurationFactory
from openhcs.core.components.multiprocessing import MultiprocessingCoordinator, Task
from openhcs.core.components.validation import GenericValidator, ValidationResult


class MockComponents(Enum):
    """Mock component enum for testing."""
    WELL = "well"
    CHANNEL = "channel"
    SITE = "site"
    Z_INDEX = "z_index"


class TestComponentConfiguration:
    """Test ComponentConfiguration class."""
    
    def test_valid_configuration(self):
        """Test creating a valid configuration."""
        config = ComponentConfiguration(
            all_components={MockComponents.WELL, MockComponents.CHANNEL, MockComponents.SITE},
            multiprocessing_axis=MockComponents.WELL,
            default_variable=[MockComponents.SITE],
            default_group_by=MockComponents.CHANNEL
        )
        
        assert config.multiprocessing_axis == MockComponents.WELL
        assert config.default_variable == [MockComponents.SITE]
        assert config.default_group_by == MockComponents.CHANNEL
    
    def test_invalid_multiprocessing_axis(self):
        """Test that invalid multiprocessing axis raises error."""
        with pytest.raises(ValueError, match="multiprocessing_axis.*must be in all_components"):
            ComponentConfiguration(
                all_components={MockComponents.CHANNEL, MockComponents.SITE},
                multiprocessing_axis=MockComponents.WELL,  # Not in all_components
                default_variable=[MockComponents.SITE],
                default_group_by=MockComponents.CHANNEL
            )
    
    def test_invalid_default_variable(self):
        """Test that invalid default variable raises error."""
        with pytest.raises(ValueError, match="default_variable component.*must be in all_components"):
            ComponentConfiguration(
                all_components={MockComponents.WELL, MockComponents.CHANNEL},
                multiprocessing_axis=MockComponents.WELL,
                default_variable=[MockComponents.SITE],  # Not in all_components
                default_group_by=MockComponents.CHANNEL
            )
    
    def test_invalid_default_group_by(self):
        """Test that invalid default group_by raises error."""
        with pytest.raises(ValueError, match="default_group_by.*must be in all_components"):
            ComponentConfiguration(
                all_components={MockComponents.WELL, MockComponents.SITE},
                multiprocessing_axis=MockComponents.WELL,
                default_variable=[MockComponents.SITE],
                default_group_by=MockComponents.CHANNEL  # Not in all_components
            )
    
    def test_validate_combination_valid(self):
        """Test valid component combination validation."""
        config = ComponentConfiguration(
            all_components={MockComponents.WELL, MockComponents.CHANNEL, MockComponents.SITE},
            multiprocessing_axis=MockComponents.WELL,
            default_variable=[MockComponents.SITE],
            default_group_by=MockComponents.CHANNEL
        )
        
        # Should not raise
        config.validate_combination([MockComponents.SITE], MockComponents.CHANNEL)
    
    def test_validate_combination_invalid(self):
        """Test invalid component combination validation."""
        config = ComponentConfiguration(
            all_components={MockComponents.WELL, MockComponents.CHANNEL, MockComponents.SITE},
            multiprocessing_axis=MockComponents.WELL,
            default_variable=[MockComponents.SITE],
            default_group_by=MockComponents.CHANNEL
        )
        
        with pytest.raises(ValueError, match="group_by.*cannot be in variable_components"):
            config.validate_combination([MockComponents.CHANNEL], MockComponents.CHANNEL)


class TestComponentConfigurationFactory:
    """Test ComponentConfigurationFactory class."""
    
    def test_create_configuration(self):
        """Test creating configuration via factory."""
        config = ComponentConfigurationFactory.create_configuration(
            MockComponents,
            multiprocessing_axis=MockComponents.WELL,
            default_variable=[MockComponents.SITE],
            default_group_by=MockComponents.CHANNEL
        )
        
        assert config.all_components == set(MockComponents)
        assert config.multiprocessing_axis == MockComponents.WELL
        assert config.default_variable == [MockComponents.SITE]
        assert config.default_group_by == MockComponents.CHANNEL
    
    def test_create_openhcs_default_configuration(self):
        """Test creating default OpenHCS configuration."""
        config = ComponentConfigurationFactory.create_openhcs_default_configuration()
        
        # Test the configuration values by their string values to avoid enum instance comparison issues
        assert config.multiprocessing_axis.value == "well"
        assert len(config.default_variable) == 1
        assert config.default_variable[0].value == "site"
        assert config.default_group_by.value == "channel"

        # Test that all expected components are present
        component_values = {comp.value for comp in config.all_components}
        expected_values = {"well", "site", "channel", "z_index"}
        assert component_values == expected_values


class TestMultiprocessingCoordinator:
    """Test MultiprocessingCoordinator class."""
    
    def test_initialization(self):
        """Test coordinator initialization."""
        config = ComponentConfiguration(
            all_components={MockComponents.WELL, MockComponents.CHANNEL, MockComponents.SITE},
            multiprocessing_axis=MockComponents.WELL,
            default_variable=[MockComponents.SITE],
            default_group_by=MockComponents.CHANNEL
        )
        
        coordinator = MultiprocessingCoordinator(config)
        assert coordinator.config == config
        assert coordinator.axis == MockComponents.WELL
    
    def test_create_tasks(self):
        """Test task creation."""
        config = ComponentConfiguration(
            all_components={MockComponents.WELL, MockComponents.CHANNEL, MockComponents.SITE},
            multiprocessing_axis=MockComponents.WELL,
            default_variable=[MockComponents.SITE],
            default_group_by=MockComponents.CHANNEL
        )
        
        coordinator = MultiprocessingCoordinator(config)
        
        # Mock orchestrator
        mock_orchestrator = Mock()
        mock_orchestrator.get_component_keys.return_value = ["well1", "well2"]
        mock_orchestrator.create_context.side_effect = lambda x: Mock(well_id=x)
        
        tasks = coordinator.create_tasks(mock_orchestrator, [], None)
        
        assert len(tasks) == 2
        assert "well1" in tasks
        assert "well2" in tasks
        assert isinstance(tasks["well1"], Task)
        assert tasks["well1"].axis_value == "well1"


class TestGenericValidator:
    """Test GenericValidator class."""
    
    def test_initialization(self):
        """Test validator initialization."""
        config = ComponentConfiguration(
            all_components={MockComponents.WELL, MockComponents.CHANNEL, MockComponents.SITE},
            multiprocessing_axis=MockComponents.WELL,
            default_variable=[MockComponents.SITE],
            default_group_by=MockComponents.CHANNEL
        )
        
        validator = GenericValidator(config)
        assert validator.config == config
    
    def test_validate_step_valid(self):
        """Test valid step validation."""
        config = ComponentConfiguration(
            all_components={MockComponents.WELL, MockComponents.CHANNEL, MockComponents.SITE},
            multiprocessing_axis=MockComponents.WELL,
            default_variable=[MockComponents.SITE],
            default_group_by=MockComponents.CHANNEL
        )
        
        validator = GenericValidator(config)
        result = validator.validate_step(
            [MockComponents.SITE], MockComponents.CHANNEL, lambda x: x, "test_step"
        )
        
        assert result.is_valid
        assert result.error_message is None
    
    def test_validate_step_invalid_combination(self):
        """Test invalid step validation."""
        config = ComponentConfiguration(
            all_components={MockComponents.WELL, MockComponents.CHANNEL, MockComponents.SITE},
            multiprocessing_axis=MockComponents.WELL,
            default_variable=[MockComponents.SITE],
            default_group_by=MockComponents.CHANNEL
        )
        
        validator = GenericValidator(config)
        result = validator.validate_step(
            [MockComponents.CHANNEL], MockComponents.CHANNEL, lambda x: x, "test_step"
        )
        
        assert not result.is_valid
        assert "cannot be in variable_components" in result.error_message
    
    def test_validate_step_dict_without_group_by(self):
        """Test dict pattern without group_by validation."""
        config = ComponentConfiguration(
            all_components={MockComponents.WELL, MockComponents.CHANNEL, MockComponents.SITE},
            multiprocessing_axis=MockComponents.WELL,
            default_variable=[MockComponents.SITE],
            default_group_by=MockComponents.CHANNEL
        )
        
        validator = GenericValidator(config)
        result = validator.validate_step(
            [MockComponents.SITE], None, {"key": lambda x: x}, "test_step"
        )
        
        assert not result.is_valid
        assert "Dict pattern requires group_by" in result.error_message


# Note: GenericPatternEngine tests removed as the class doesn't exist in the current implementation
# Pattern functionality is handled by PatternDiscoveryEngine in openhcs.formats.pattern.pattern_discovery
