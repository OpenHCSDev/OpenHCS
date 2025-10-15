"""
Unified experimental analysis engine.

This module provides a unified analysis engine that uses the format registry
system to process experimental data from multiple microscope formats following
OpenHCS architectural principles.
"""

from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple

from openhcs.core.config import ExperimentalAnalysisConfig
from .format_registry_service import FormatRegistryService
from .format_registry import FormatDetectionError, DataProcessingError


class ExperimentalAnalysisEngine:
    """
    Unified analysis engine using format registry system.
    
    This engine eliminates code duplication by using the registry pattern
    to handle different microscope formats through a unified interface.
    """
    
    def __init__(self, config: ExperimentalAnalysisConfig):
        """
        Initialize analysis engine with configuration.
        
        Args:
            config: Experimental analysis configuration
        """
        self.config = config
        self.format_service = FormatRegistryService()
    
    def run_analysis(
        self, 
        results_path: str, 
        config_file: str, 
        compiled_results_path: str,
        heatmap_path: Optional[str] = None
    ) -> Dict[str, Any]:
        """
        Run complete experimental analysis with automatic format detection.
        
        Args:
            results_path: Path to microscope results file
            config_file: Path to experimental configuration Excel file
            compiled_results_path: Output path for compiled results
            heatmap_path: Optional output path for heatmap visualization
            
        Returns:
            Dictionary containing analysis results and metadata
            
        Raises:
            FormatDetectionError: If microscope format cannot be detected
            DataProcessingError: If data processing fails
            FileNotFoundError: If required files are missing
        """
        try:
            # Step 1: Detect or determine format
            format_name = self._determine_format(results_path)
            
            # Step 2: Get format registry
            format_registry = self.format_service.get_registry_instance_for_format(format_name)
            
            # Step 3: Parse experimental configuration
            experiment_config = self._parse_experiment_config(config_file)
            
            # Step 4: Process microscope data
            processed_data = format_registry.process_data(results_path)
            
            # Step 5: Create experiment data structure
            experiment_dict_locations = self._make_experiment_dict_locations(
                experiment_config['plate_groups'],
                experiment_config['plate_layout'],
                experiment_config['conditions']
            )
            
            # Step 6: Map experimental design to measured values
            experiment_dict_values = self._make_experiment_dict_values(
                processed_data['plates_dict'],
                experiment_dict_locations,
                processed_data['features'],
                experiment_config['plate_groups'],
                experiment_config['per_well_datapoints']
            )
            
            # Step 7: Apply normalization if controls are defined
            if experiment_config['ctrl_positions'] is not None:
                experiment_dict_values_normalized = self._normalize_experiment(
                    experiment_dict_values,
                    experiment_config['ctrl_positions'],
                    processed_data['features'],
                    processed_data['plates_dict'],
                    experiment_config['plate_groups']
                )
            else:
                experiment_dict_values_normalized = experiment_dict_values
            
            # Step 8: Generate results tables
            feature_tables = self._create_all_feature_tables(
                experiment_dict_values_normalized,
                processed_data['features'],
                experiment_config['per_well_datapoints']
            )
            
            # Step 9: Export results
            self._export_results(feature_tables, compiled_results_path)
            
            # Step 10: Export raw results if configured
            if self.config.export_raw_results:
                raw_results_path = compiled_results_path.replace('.xlsx', '_raw.xlsx')
                feature_tables_raw = self._create_all_feature_tables(
                    experiment_dict_values,
                    processed_data['features'],
                    experiment_config['per_well_datapoints']
                )
                self._export_results(feature_tables_raw, raw_results_path)
            
            # Step 11: Generate heatmaps if configured
            if self.config.export_heatmaps and heatmap_path:
                self._export_heatmaps(feature_tables, heatmap_path)
            
            return {
                'format_name': format_name,
                'features': processed_data['features'],
                'conditions': experiment_config['conditions'],
                'feature_tables': feature_tables,
                'experiment_config': experiment_config,
                'processed_data': processed_data
            }
            
        except Exception as e:
            raise DataProcessingError(f"Analysis failed: {e}") from e
    
    def _determine_format(self, results_path: str) -> str:
        """
        Determine microscope format for results file.
        
        Args:
            results_path: Path to results file
            
        Returns:
            Format name
            
        Raises:
            FormatDetectionError: If format cannot be determined
        """
        if self.config.auto_detect_format:
            try:
                return self.format_service.detect_format_from_file(results_path)
            except FormatDetectionError:
                if self.config.default_format:
                    return self.config.default_format
                raise
        elif self.config.default_format:
            return self.config.default_format
        else:
            raise FormatDetectionError(
                "Auto-detection disabled and no default format specified"
            )
    
    def _parse_experiment_config(self, config_file: str) -> Dict[str, Any]:
        """
        Parse experimental configuration from Excel file.
        
        Args:
            config_file: Path to configuration file
            
        Returns:
            Parsed configuration dictionary
            
        Raises:
            FileNotFoundError: If config file doesn't exist
            ValueError: If config parsing fails
        """
        config_path = Path(config_file)
        if not config_path.exists():
            raise FileNotFoundError(f"Configuration file not found: {config_file}")
        
        try:
            # Parse experimental design
            scope, plate_layout, conditions, ctrl_positions, excluded_positions, per_well_datapoints = self._read_plate_layout(config_file)
            
            # Parse plate groups
            plate_groups = self._load_plate_groups(config_file)
            
            return {
                'scope': scope,
                'plate_layout': plate_layout,
                'conditions': conditions,
                'ctrl_positions': ctrl_positions,
                'excluded_positions': excluded_positions,
                'per_well_datapoints': per_well_datapoints,
                'plate_groups': plate_groups
            }
            
        except Exception as e:
            raise ValueError(f"Failed to parse configuration file {config_file}: {e}")
    
    def _read_plate_layout(self, config_path: str) -> Tuple[str, Dict, List, Optional[Dict], Optional[Dict], bool]:
        """
        Read plate layout from configuration file.

        This method maintains compatibility with existing configuration format
        while using the new architecture.

        Args:
            config_path: Path to configuration file

        Returns:
            Tuple of (scope, plate_layout, conditions, ctrl_positions, excluded_positions, per_well_datapoints)
        """
        # Import the existing function to maintain compatibility
        # This will be gradually refactored to use the new architecture
        from openhcs.formats.experimental_analysis import read_plate_layout
        return read_plate_layout(config_path)
    
    def _load_plate_groups(self, config_path: str) -> Dict:
        """
        Load plate groups from configuration file.
        
        Args:
            config_path: Path to configuration file
            
        Returns:
            Plate groups dictionary
        """
        # Import the existing function to maintain compatibility
        from openhcs.formats.experimental_analysis import load_plate_groups
        return load_plate_groups(config_path)
    
    def _make_experiment_dict_locations(self, plate_groups: Dict, plate_layout: Dict, conditions: List) -> Dict:
        """Create experiment location mapping."""
        from openhcs.formats.experimental_analysis import make_experiment_dict_locations
        return make_experiment_dict_locations(plate_groups, plate_layout, conditions)
    
    def _make_experiment_dict_values(self, plates_dict: Dict, experiment_dict_locations: Dict, features: List, plate_groups: Dict, per_well_datapoints: bool = False) -> Dict:
        """Map experimental design to measured values."""
        from openhcs.formats.experimental_analysis import make_experiment_dict_values
        return make_experiment_dict_values(plates_dict, experiment_dict_locations, features, plate_groups, per_well_datapoints)
    
    def _normalize_experiment(self, experiment_dict_values: Dict, ctrl_positions: Dict, features: List, plates_dict: Dict, plate_groups: Dict) -> Dict:
        """Apply normalization using control wells."""
        from openhcs.formats.experimental_analysis import normalize_experiment
        return normalize_experiment(experiment_dict_values, ctrl_positions, features, plates_dict, plate_groups)
    
    def _create_all_feature_tables(self, experiment_dict_values: Dict, features: List, per_well_datapoints: bool = False) -> Dict:
        """Create feature tables for export."""
        from openhcs.formats.experimental_analysis import create_all_feature_tables
        return create_all_feature_tables(experiment_dict_values, features, per_well_datapoints)
    
    def _export_results(self, feature_tables: Dict, output_path: str):
        """Export results to Excel file."""
        from openhcs.formats.experimental_analysis import feature_tables_to_excel
        feature_tables_to_excel(feature_tables, output_path)
    
    def _export_heatmaps(self, feature_tables: Dict, output_path: str):
        """Export heatmap visualizations."""
        # This would be implemented to generate heatmaps
        # For now, use the same export as regular results
        self._export_results(feature_tables, output_path)


# Backward compatibility function
def run_experimental_analysis(
    results_path: str = "mx_results.xlsx",
    config_file: str = "./config.xlsx",
    compiled_results_path: str = "./compiled_results_normalized.xlsx",
    heatmap_path: str = "./heatmaps.xlsx"
) -> Dict[str, Any]:
    """
    Run complete experimental analysis pipeline (backward compatibility wrapper).
    
    Args:
        results_path: Path to results Excel file (CX5 or MetaXpress format)
        config_file: Path to experimental configuration Excel file
        compiled_results_path: Output path for compiled results
        heatmap_path: Output path for heatmap visualization
        
    Returns:
        Analysis results dictionary
    """
    from openhcs.core.config import ExperimentalAnalysisConfig
    
    # Use default configuration for backward compatibility
    config = ExperimentalAnalysisConfig()
    engine = ExperimentalAnalysisEngine(config)
    
    return engine.run_analysis(
        results_path=results_path,
        config_file=config_file,
        compiled_results_path=compiled_results_path,
        heatmap_path=heatmap_path
    )
