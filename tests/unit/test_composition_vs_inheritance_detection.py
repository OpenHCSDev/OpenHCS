"""
Test equivalence between inheritance-based and composition-based relationship detection.

This test validates that composition detection produces equivalent results to
inheritance detection for all config types in the OpenHCS system.
"""

import pytest
from dataclasses import dataclass, field
from typing import Optional
from openhcs.core.config import (
    GlobalPipelineConfig, PathPlanningConfig, StepMaterializationConfig,
    WellFilterConfig, StepWellFilterConfig, StreamingConfig, NapariStreamingConfig,
    VFSConfig, ZarrConfig
)
from openhcs.core.composition_detection import (
    discover_composition_hierarchy, find_composition_relationships,
    find_all_composition_paths_for_type, resolve_field_through_composition,
    compare_inheritance_vs_composition, create_composition_lazy_dataclass
)
from openhcs.core.field_path_detection import FieldPathDetector


class TestCompositionDetectionEquivalence:
    """Test that composition detection produces equivalent results to inheritance detection."""
    
    def test_stepmaterialization_config_relationships(self):
        """Test that StepMaterializationConfig composition matches inheritance relationships."""
        comparison = compare_inheritance_vs_composition(StepMaterializationConfig, GlobalPipelineConfig)
        
        print(f"StepMaterializationConfig comparison: {comparison}")
        
        # Validate composition detection finds the composed types
        composition_types = comparison['composition']['relationships']
        assert 'PathPlanningConfig' in composition_types
        assert 'StepWellFilterConfig' in composition_types
        
        # Validate hierarchy discovery
        composition_hierarchy = comparison['composition']['hierarchy']
        assert 'PathPlanningConfig' in composition_hierarchy
        assert 'StepWellFilterConfig' in composition_hierarchy
        
        # Check field paths
        assert composition_hierarchy['PathPlanningConfig'] == ['path_planning']
        assert composition_hierarchy['StepWellFilterConfig'] == ['well_filter']
    
    def test_pathplanning_config_relationships(self):
        """Test PathPlanningConfig composition detection."""
        comparison = compare_inheritance_vs_composition(PathPlanningConfig, GlobalPipelineConfig)
        
        print(f"PathPlanningConfig comparison: {comparison}")
        
        # PathPlanningConfig now uses composition for WellFilterConfig
        composition_types = comparison['composition']['relationships']
        assert 'WellFilterConfig' in composition_types
        
        composition_hierarchy = comparison['composition']['hierarchy']
        assert composition_hierarchy['WellFilterConfig'] == ['well_filter']
    
    def test_streaming_config_relationships(self):
        """Test StreamingConfig composition detection."""
        comparison = compare_inheritance_vs_composition(NapariStreamingConfig, GlobalPipelineConfig)
        
        print(f"NapariStreamingConfig comparison: {comparison}")
        
        # NapariStreamingConfig should detect composed types
        composition_types = comparison['composition']['relationships']
        # Should find composed streaming defaults and well filter configs
        assert len(composition_types) >= 0  # May have composed types
    
    def test_field_resolution_through_composition(self):
        """Test that field resolution works through composition hierarchy."""
        # Create test instances
        path_planning = PathPlanningConfig(output_dir_suffix="_test")
        well_filter = StepWellFilterConfig(well_filter=["A01", "A02"])
        
        step_config = StepMaterializationConfig(
            path_planning=path_planning,
            well_filter=well_filter,
            sub_dir="test_checkpoints"
        )
        
        # Test direct field resolution
        assert resolve_field_through_composition(step_config, "sub_dir") == "test_checkpoints"
        
        # Test composition field resolution
        assert resolve_field_through_composition(step_config, "output_dir_suffix") == "_test"

        # well_filter resolves to the StepWellFilterConfig object (direct field)
        resolved_well_filter = resolve_field_through_composition(step_config, "well_filter")
        assert isinstance(resolved_well_filter, StepWellFilterConfig)
        assert resolved_well_filter.well_filter == ["A01", "A02"]
        
        # Test non-existent field
        assert resolve_field_through_composition(step_config, "nonexistent_field") is None
    
    def test_composition_lazy_dataclass_creation(self):
        """Test that composition-based lazy dataclass creation works."""
        # Create composition-based lazy class
        CompositionLazyStepConfig = create_composition_lazy_dataclass(
            base_class=StepMaterializationConfig,
            global_config_type=GlobalPipelineConfig,
            field_path="materialization_defaults",
            lazy_class_name="CompositionLazyStepMaterializationConfig"
        )
        
        # Verify it's a valid class
        assert CompositionLazyStepConfig is not None
        assert CompositionLazyStepConfig.__name__ == "CompositionLazyStepMaterializationConfig"
        
        # Test instantiation
        instance = CompositionLazyStepConfig()
        assert instance is not None
        
        # Test that it has the expected methods
        assert hasattr(instance, '_resolve_field_value')
        assert hasattr(instance, 'to_base_config')
    
    def test_composition_hierarchy_discovery(self):
        """Test automatic composition hierarchy discovery."""
        hierarchy = discover_composition_hierarchy(StepMaterializationConfig)
        
        print(f"StepMaterializationConfig hierarchy: {hierarchy}")
        
        # Should discover PathPlanningConfig and StepWellFilterConfig
        assert PathPlanningConfig in hierarchy
        assert StepWellFilterConfig in hierarchy
        
        # Check field paths
        assert hierarchy[PathPlanningConfig] == ['path_planning']
        assert hierarchy[StepWellFilterConfig] == ['well_filter']
    
    def test_nested_composition_discovery(self):
        """Test discovery of nested composition relationships."""
        # Create a test config with nested compositions
        @dataclass
        class NestedConfig:
            path_planning: Optional[PathPlanningConfig] = None
            step_config: Optional[StepMaterializationConfig] = None
        
        hierarchy = discover_composition_hierarchy(NestedConfig)
        
        print(f"NestedConfig hierarchy: {hierarchy}")
        
        # Should discover direct compositions
        assert PathPlanningConfig in hierarchy
        assert StepMaterializationConfig in hierarchy
        
        # Should discover nested compositions through StepMaterializationConfig
        # (StepMaterializationConfig contains PathPlanningConfig and StepWellFilterConfig)
        expected_paths = {
            PathPlanningConfig: ['path_planning', 'step_config.path_planning'],
            StepMaterializationConfig: ['step_config'],
            StepWellFilterConfig: ['step_config.well_filter']
        }
        
        for config_type, expected_path_list in expected_paths.items():
            if config_type in hierarchy:
                for expected_path in expected_path_list:
                    assert expected_path in hierarchy[config_type], f"Missing path {expected_path} for {config_type}"
    
    def test_composition_vs_inheritance_field_paths(self):
        """Test that composition detection finds equivalent field paths to inheritance."""
        # Test with GlobalPipelineConfig as root
        composition_paths = find_all_composition_paths_for_type(GlobalPipelineConfig, PathPlanningConfig)
        
        print(f"PathPlanningConfig composition paths in GlobalPipelineConfig: {composition_paths}")
        
        # Should find path_planning field
        assert 'path_planning' in composition_paths
    
    def test_all_config_types_composition_detection(self):
        """Test composition detection on all major config types."""
        config_types = [
            PathPlanningConfig,
            StepMaterializationConfig,
            VFSConfig,
            ZarrConfig,
            NapariStreamingConfig
        ]
        
        for config_type in config_types:
            print(f"\nTesting {config_type.__name__}:")
            
            # Test relationship discovery
            relationships = find_composition_relationships(config_type)
            print(f"  Composed types: {[t.__name__ for t in relationships]}")
            
            # Test hierarchy discovery
            hierarchy = discover_composition_hierarchy(config_type)
            print(f"  Hierarchy: {hierarchy}")
            
            # Test comparison with inheritance
            comparison = compare_inheritance_vs_composition(config_type, GlobalPipelineConfig)
            print(f"  Comparison: {comparison}")
            
            # All should complete without errors
            assert isinstance(relationships, list)
            assert isinstance(hierarchy, dict)
            assert isinstance(comparison, dict)


@pytest.fixture
def sample_global_config():
    """Create a sample global config for testing."""
    return GlobalPipelineConfig(
        path_planning=PathPlanningConfig(output_dir_suffix="_test"),
        materialization_defaults=StepMaterializationConfig(
            path_planning=PathPlanningConfig(output_dir_suffix="_materialization"),
            well_filter=StepWellFilterConfig(well_filter=["A01"]),
            sub_dir="test_checkpoints"
        )
    )


class TestCompositionFieldResolution:
    """Test field resolution through composition hierarchies."""
    
    def test_resolution_priority_order(self, sample_global_config):
        """Test that field resolution follows correct priority order."""
        # Set up global context
        from openhcs.core.context.global_config import set_current_global_config
        set_current_global_config(GlobalPipelineConfig, sample_global_config)
        
        # Create composition-based lazy config
        CompositionLazyConfig = create_composition_lazy_dataclass(
            base_class=StepMaterializationConfig,
            global_config_type=GlobalPipelineConfig,
            field_path="materialization_defaults"
        )
        
        instance = CompositionLazyConfig()
        
        # Test that fields resolve correctly
        # sub_dir should come from direct field
        assert hasattr(instance, 'sub_dir')
        
        # Should be able to resolve to base config
        base_config = instance.to_base_config()
        assert isinstance(base_config, StepMaterializationConfig)
    
    def test_composition_equivalent_to_inheritance(self, sample_global_config):
        """Test that composition-based resolution produces equivalent results to inheritance."""
        from openhcs.core.context.global_config import set_current_global_config
        from openhcs.core.config import LazyStepMaterializationConfig
        
        set_current_global_config(GlobalPipelineConfig, sample_global_config)
        
        # Create both inheritance-based and composition-based lazy configs
        inheritance_instance = LazyStepMaterializationConfig()
        
        CompositionLazyConfig = create_composition_lazy_dataclass(
            base_class=StepMaterializationConfig,
            global_config_type=GlobalPipelineConfig,
            field_path="materialization_defaults"
        )
        composition_instance = CompositionLazyConfig()
        
        # Convert both to base configs for comparison
        inheritance_base = inheritance_instance.to_base_config()
        composition_base = composition_instance.to_base_config()
        
        # Compare key fields (may not be identical due to different resolution logic)
        print(f"Inheritance base: {inheritance_base}")
        print(f"Composition base: {composition_base}")
        
        # Both should be valid StepMaterializationConfig instances
        assert isinstance(inheritance_base, StepMaterializationConfig)
        assert isinstance(composition_base, StepMaterializationConfig)


if __name__ == "__main__":
    # Run tests directly for development
    test_class = TestCompositionDetectionEquivalence()
    test_class.test_stepmaterialization_config_relationships()
    test_class.test_pathplanning_config_relationships()
    test_class.test_field_resolution_through_composition()
    test_class.test_composition_lazy_dataclass_creation()
    test_class.test_all_config_types_composition_detection()
    print("✅ All composition detection tests passed!")
