Experimental Analysis System
=============================

OpenHCS provides a comprehensive experimental analysis system for processing high-content screening data from ThermoFisher CX5 and MetaXpress systems, with support for complex experimental designs, replicate management, and statistical analysis.

## System Overview

The experimental analysis system handles the complete workflow from experimental design configuration to statistical analysis and visualization:

- **Configuration parsing**: Excel-based experimental design definition
- **Data ingestion**: Support for CX5 and MetaXpress result formats
- **Replicate management**: Biological and technical replicate handling
- **Statistical analysis**: Control-based normalization and dose-response analysis
- **Result export**: Compiled results and heatmap visualization

## Architecture Components

### Core Modules

**openhcs.formats.experimental_analysis**
  Primary analysis pipeline with comprehensive experimental design support

**openhcs.formats.metaxpress**
  MetaXpress format compatibility and legacy analysis support

**openhcs.processing.backends.analysis.cx5_format**
  ThermoFisher CX5 format support and analysis functions

### Configuration System

The system uses Excel-based configuration files with a structured format:

.. code-block:: python

   def read_plate_layout(config_path):
       """Parse experimental configuration from Excel file."""
       xls = pd.ExcelFile(config_path)
       df = pd.read_excel(xls, 'drug_curve_map', index_col=0, header=None)
       
       # Parse global parameters
       N = None          # Number of biological replicates
       scope = None      # Microscope format (EDDU_CX5, EDDU_metaxpress)
       
       # Parse experimental conditions
       conditions = []   # List of experimental conditions
       layout = {}       # Condition-to-wells mapping
       
       # Parse control definitions
       ctrl_positions = None  # Control well positions for normalization

**Configuration Structure**:
- **Global parameters**: N (replicates), Scope (microscope format)
- **Control definitions**: Control wells for normalization
- **Condition blocks**: Experimental conditions with dose-response mapping
- **Plate groups**: Biological replicate to physical plate mapping

### Data Processing Pipeline

#### Phase 1: Configuration Parsing

.. code-block:: python

   # Parse experimental design
   scope, plate_layout, conditions, ctrl_positions = read_plate_layout(config_file)
   plate_groups = load_plate_groups(config_file)
   
   # Create experiment location mapping
   experiment_dict_locations = make_experiment_dict_locations(
       plate_groups, plate_layout, conditions
   )

**Output**: Structured mapping of conditions → replicates → doses → wells

#### Phase 2: Data Ingestion

.. code-block:: python

   def read_results(results_path, scope=None):
       """Read results from microscope-specific Excel format."""
       xls = pd.ExcelFile(results_path)
       if scope == "EDDU_CX5":
           raw_df = pd.read_excel(xls, 'Rawdata')
       elif scope == "EDDU_metaxpress":
           raw_df = pd.read_excel(xls, xls.sheet_names[0])
       return raw_df

**Format Support**:
- **CX5 format**: ThermoFisher CX5 'Rawdata' sheet structure
- **MetaXpress format**: Molecular Devices MetaXpress export format

#### Phase 3: Data Structure Creation

.. code-block:: python

   # Create well-based data structures
   well_dict = create_well_dict(df, scope=scope)
   plates_dict = create_plates_dict(df, scope=scope)
   plates_dict = fill_plates_dict(df, plates_dict, scope=scope)

**Data Structures**:
- **well_dict**: ``{well: {feature: value}}`` - Well-centric feature mapping
- **plates_dict**: ``{plate: {well: {feature: value}}}`` - Plate-centric organization

#### Phase 4: Experimental Data Mapping

.. code-block:: python

   # Map experimental design to measured values
   experiment_dict_values = make_experiment_dict_values(
       plates_dict, experiment_dict_locations, features
   )

**Output**: ``experiment_dict[condition][replicate][dose] = {feature: [values]}``

#### Phase 5: Statistical Analysis

.. code-block:: python

   # Control-based normalization
   if ctrl_positions is not None:
       experiment_dict_values = normalize_experiment(
           experiment_dict_values, ctrl_positions, features, plates_dict
       )
   
   # Generate feature tables
   feature_tables = create_all_feature_tables(experiment_dict_values, features)

### Replicate Management System

#### Biological Replicates

The system handles multiple biological replicates (N1, N2, N3, etc.) with automatic aggregation:

.. code-block:: python

   def make_experiment_dict_locations(plate_groups, plate_layout, conditions):
       """Create mapping of experimental conditions to well locations."""
       experiment_dict = {}
       
       for condition in conditions:
           experiment_dict[condition] = {}
           for replicate in range(1, N+1):  # N biological replicates
               replicate_key = f"N{replicate}"
               experiment_dict[condition][replicate_key] = {}
               
               # Map doses to wells for this replicate
               for dose_idx, dose in enumerate(doses):
                   wells = get_wells_for_replicate_dose(condition, replicate, dose_idx)
                   experiment_dict[condition][replicate_key][dose] = wells

#### Technical Replicates

Technical replicates (multiple wells per condition/dose) are automatically detected and averaged:

.. code-block:: python

   def process_technical_replicates(experiment_dict_values):
       """Average technical replicates within each condition/dose."""
       for condition in experiment_dict_values:
           for replicate in experiment_dict_values[condition]:
               for dose in experiment_dict_values[condition][replicate]:
                   # Multiple wells = technical replicates
                   well_values = experiment_dict_values[condition][replicate][dose]
                   if len(well_values) > 1:
                       # Average technical replicates
                       averaged_values = np.mean(well_values, axis=0)
                       experiment_dict_values[condition][replicate][dose] = averaged_values

### Normalization System

#### Control-Based Normalization

The system supports control-based normalization for plate-to-plate variation correction:

.. code-block:: python

   def normalize_experiment(experiment_dict_values, ctrl_positions, features, plates_dict):
       """Normalize experimental values using control wells."""
       
       # Calculate control statistics
       control_stats = calculate_control_statistics(ctrl_positions, plates_dict, features)
       
       # Normalize each experimental condition
       for condition in experiment_dict_values:
           for replicate in experiment_dict_values[condition]:
               for dose in experiment_dict_values[condition][replicate]:
                   normalized_values = normalize_to_controls(
                       experiment_dict_values[condition][replicate][dose],
                       control_stats,
                       features
                   )
                   experiment_dict_values[condition][replicate][dose] = normalized_values

**Normalization Methods**:
- **Z-score normalization**: ``(value - control_mean) / control_std``
- **Percent of control**: ``(value / control_mean) * 100``
- **Fold change**: ``value / control_mean``

### Feature Extraction System

#### Microscope-Specific Feature Extraction

.. code-block:: python

   def get_features(raw_df, scope=None):
       """Extract feature columns based on microscope format."""
       if scope == "EDDU_CX5":
           return get_features_EDDU_CX5(raw_df)
       elif scope == "EDDU_metaxpress":
           return get_features_EDDU_metaxpress(raw_df)

   def get_features_EDDU_CX5(raw_df):
       """Extract features from CX5 format."""
       return raw_df.iloc[:, raw_df.columns.str.find("Replicate").argmax()+1:-1].columns

   def get_features_EDDU_metaxpress(raw_df):
       """Extract features from MetaXpress format."""
       feature_rows = raw_df[pd.isnull(raw_df.iloc[:,0])].iloc[0].tolist()[2:]
       return feature_rows

**Feature Types**:
- **Cell count metrics**: Total cells, viable cells, dead cells
- **Morphological features**: Cell area, perimeter, circularity, eccentricity
- **Intensity measurements**: Mean, median, standard deviation per channel
- **Texture features**: Contrast, correlation, energy, homogeneity

### Export System

#### Result Compilation

.. code-block:: python

   def create_all_feature_tables(experiment_dict_values, features):
       """Create feature-specific tables for export."""
       feature_tables = {}
       
       for feature in features:
           feature_table = create_feature_table(experiment_dict_values, feature)
           feature_tables[feature] = feature_table
       
       return feature_tables

#### Excel Export with Heatmaps

.. code-block:: python

   def export_results_with_heatmaps(feature_tables, output_path):
       """Export results with integrated heatmap visualization."""
       with pd.ExcelWriter(output_path, engine='xlsxwriter') as writer:
           for feature_name, feature_table in feature_tables.items():
               # Write data table
               feature_table.to_excel(writer, sheet_name=feature_name)
               
               # Generate heatmap
               create_heatmap_visualization(feature_table, writer, feature_name)

## Integration Points

### Pipeline Integration

The experimental analysis system integrates with OpenHCS pipelines through the analysis consolidation system:

.. code-block:: python

   # Integration with analysis consolidation
   from openhcs.processing.backends.analysis.consolidate_analysis_results import (
       consolidate_analysis_results_pipeline
   )
   
   # Experimental analysis can feed into consolidation
   consolidated_results = consolidate_analysis_results_pipeline(
       image_stack=processed_images,
       results_directory=experimental_results_dir,
       consolidation_config=AnalysisConsolidationConfig(),
       plate_metadata_config=PlateMetadataConfig()
   )

### Configuration System Integration

The experimental analysis system can be configured through the global configuration system:

.. code-block:: python

   @dataclass(frozen=True)
   class ExperimentalAnalysisConfig:
       """Configuration for experimental analysis system."""
       enabled: bool = True
       config_file: str = "config.xlsx"
       normalization_method: str = "z_score"  # z_score, percent_control, fold_change
       export_heatmaps: bool = True
       statistical_tests: bool = True

## Performance Characteristics

### Memory Efficiency

- **Lazy loading**: Results loaded on-demand to minimize memory usage
- **Chunked processing**: Large datasets processed in chunks
- **Efficient data structures**: Optimized pandas DataFrames for statistical operations

### Scalability

- **Multi-plate support**: Handles experiments across multiple physical plates
- **Variable replicate numbers**: Supports any number of biological replicates
- **Flexible condition numbers**: No limit on experimental conditions per plate

### Statistical Robustness

- **Outlier detection**: Automatic identification of statistical outliers
- **Missing data handling**: Robust handling of missing wells or failed measurements
- **Quality control metrics**: Automatic calculation of assay quality metrics (Z-factor, etc.)

The experimental analysis system provides comprehensive support for high-content screening experimental workflows, from initial experimental design through final statistical analysis and visualization, ensuring robust and reproducible analysis of complex multi-condition, multi-replicate experiments.
