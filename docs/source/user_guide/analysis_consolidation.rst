Analysis Consolidation Guide
============================

OpenHCS automatically consolidates analysis results from multi-well pipelines into MetaXpress-compatible summary tables, streamlining data management and enabling seamless integration with existing analysis workflows.

## Quick Start

Analysis consolidation runs automatically after pipeline completion when enabled (default). The system:

1. **Detects CSV files** in the results directory
2. **Groups by well ID** using filename patterns
3. **Aggregates analysis metrics** into summary statistics
4. **Generates MetaXpress-style output** with proper headers

**No manual intervention required** - consolidated results appear alongside individual well results.

## Configuration

### Basic Configuration

Control analysis consolidation through the global configuration:

.. code-block:: python

   from openhcs.core.config import GlobalPipelineConfig, AnalysisConsolidationConfig
   
   # Enable/disable consolidation
   config = GlobalPipelineConfig(
       analysis_consolidation=AnalysisConsolidationConfig(
           enabled=True,                    # Enable automatic consolidation
           metaxpress_style=True,          # Generate MetaXpress-compatible format
           output_filename="summary.csv"   # Custom output filename
       )
   )

### Advanced Configuration

Customize file patterns and processing behavior:

.. code-block:: python

   # Custom well pattern and file filtering
   consolidation_config = AnalysisConsolidationConfig(
       enabled=True,
       metaxpress_style=True,
       well_pattern=r"([A-Z]\d{1,2})",           # Match A1, A01, B12, etc.
       file_extensions=(".csv", ".tsv"),          # Include TSV files
       exclude_patterns=(                         # Skip these patterns
           r".*consolidated.*",
           r".*summary.*",
           r".*backup.*"
       ),
       output_filename="metaxpress_results.csv"
   )

### Plate Metadata Configuration

Customize MetaXpress header information:

.. code-block:: python

   from openhcs.core.config import PlateMetadataConfig
   
   metadata_config = PlateMetadataConfig(
       barcode="PLATE-2024-001",
       plate_name="Cell Viability Assay",
       plate_id="CV001",
       description="96-well cell viability analysis with drug treatment",
       acquisition_user="Lab Technician",
       z_step="1"
   )
   
   # Use in global config
   config = GlobalPipelineConfig(
       analysis_consolidation=consolidation_config,
       plate_metadata=metadata_config
   )

## Output Format

### MetaXpress-Style Headers

The consolidated output includes MetaXpress-compatible headers:

.. code-block:: text

   Barcode,PLATE-2024-001
   Plate Name,Cell Viability Assay
   Plate ID,CV001
   Description,96-well cell viability analysis with drug treatment
   Acquisition User,Lab Technician
   Z Step,1
   Well,Cell Count (cell_counting),Cell Area Mean (cell_counting),Viability (viability_analysis)
   A01,245,156.7,0.823
   A02,198,142.3,0.756
   B01,267,162.1,0.891
   ...

### Column Organization

**Well Column**: Primary identifier (always first column)
**Grouped Metrics**: Columns grouped by analysis type with descriptive names
**Sorted Order**: Consistent ordering within each analysis group

Example column structure:
- ``Well`` - Well identifier (A01, B02, etc.)
- ``Cell Count (cell_counting)`` - Total cells detected
- ``Cell Area Mean (cell_counting)`` - Average cell area
- ``Cell Area Std (cell_counting)`` - Cell area standard deviation
- ``Intensity Mean (fluorescence)`` - Mean fluorescence intensity
- ``Intensity Max (fluorescence)`` - Maximum fluorescence intensity

## File Pattern Recognition

### Well ID Extraction

The system automatically extracts well IDs from filenames using configurable patterns:

**Standard Patterns**:
- ``A01_cell_counting.csv`` → Well: ``A01``, Analysis: ``cell_counting``
- ``B12_fluorescence_analysis.csv`` → Well: ``B12``, Analysis: ``fluorescence_analysis``
- ``C03_morphology_results.csv`` → Well: ``C03``, Analysis: ``morphology_results``

**Custom Patterns**:
.. code-block:: python

   # For different naming conventions
   well_pattern = r"Well_([A-Z]\d{2})"     # Well_A01_analysis.csv
   well_pattern = r"([A-Z]\d{1,2})_"       # A1_analysis.csv or A01_analysis.csv
   well_pattern = r"(\d{2}[A-Z])"          # 01A_analysis.csv

### Analysis Type Detection

The system automatically detects analysis types from filename patterns:

**Common Analysis Types**:
- ``cell_counting``: Files containing "cell_count", "counting", "cells"
- ``intensity_analysis``: Files containing "intensity", "fluorescence", "signal"
- ``morphology_analysis``: Files containing "morphology", "shape", "area"
- ``viability_analysis``: Files containing "viability", "live", "dead"

## Integration with Pipelines

### Automatic Execution

Analysis consolidation runs automatically after pipeline completion:

.. code-block:: python

   from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
   from openhcs.core.config import GlobalPipelineConfig
   
   # Configure with consolidation enabled
   config = GlobalPipelineConfig(
       analysis_consolidation=AnalysisConsolidationConfig(enabled=True)
   )
   
   # Run pipeline - consolidation happens automatically
   orchestrator = PipelineOrchestrator(plate_path="/path/to/plate")
   results = orchestrator.run_pipeline(pipeline)
   
   # Consolidated results available in results directory
   # Look for: metaxpress_style_summary.csv

### Manual Execution

For custom consolidation workflows:

.. code-block:: python

   from openhcs.processing.backends.analysis.consolidate_analysis_results import consolidate_analysis_results
   from openhcs.core.config import AnalysisConsolidationConfig, PlateMetadataConfig
   
   # Manual consolidation
   summary_df = consolidate_analysis_results(
       results_directory="/path/to/results",
       well_ids=["A01", "A02", "B01", "B02"],  # Specify wells to include
       consolidation_config=AnalysisConsolidationConfig(),
       plate_metadata_config=PlateMetadataConfig(),
       output_path="/path/to/consolidated_results.csv"
   )

### Pipeline Function Integration

Use consolidation as a pipeline step:

.. code-block:: python

   from openhcs.core.steps.function_step import FunctionStep
   from openhcs.processing.backends.analysis.consolidate_analysis_results import consolidate_analysis_results_pipeline
   
   # Add consolidation as a pipeline step
   consolidation_step = FunctionStep(
       func=consolidate_analysis_results_pipeline,
       name="consolidate_results",
       variable_components=[],  # Runs once per plate
       results_directory="/path/to/results",
       consolidation_config=AnalysisConsolidationConfig(),
       plate_metadata_config=PlateMetadataConfig()
   )

## Troubleshooting

### Common Issues

**No CSV Files Found**:
- Verify analysis steps are materializing results to CSV
- Check that results directory path is correct
- Ensure CSV files follow expected naming patterns

**Missing Wells in Output**:
- Verify well ID pattern matches your filename convention
- Check that CSV files exist for all expected wells
- Review exclude patterns to ensure files aren't being filtered out

**Incorrect Analysis Type Detection**:
- Use custom analysis type mapping if automatic detection fails
- Ensure filenames contain recognizable analysis type keywords
- Consider standardizing filename conventions

### Validation

Verify consolidation is working correctly:

.. code-block:: python

   import pandas as pd
   from pathlib import Path
   
   # Check consolidated output
   results_dir = Path("/path/to/results")
   consolidated_file = results_dir / "metaxpress_style_summary.csv"
   
   if consolidated_file.exists():
       # Read and inspect consolidated results
       df = pd.read_csv(consolidated_file, skiprows=6)  # Skip MetaXpress headers
       print(f"Consolidated {len(df)} wells")
       print(f"Analysis columns: {[col for col in df.columns if col != 'Well']}")
   else:
       print("Consolidated file not found - check configuration")

### Performance Considerations

**Large Datasets**:
- Consolidation processes all CSV files in memory
- For very large datasets, consider processing in batches
- Monitor memory usage during consolidation

**File Organization**:
- Keep results directories organized by plate/experiment
- Use consistent naming conventions across experiments
- Clean up intermediate files to reduce processing time

## Best Practices

### Filename Conventions

**Recommended Pattern**: ``{well_id}_{analysis_type}_{timestamp}.csv``
- Example: ``A01_cell_counting_20240315.csv``
- Enables automatic well and analysis type detection
- Timestamp prevents filename conflicts

### Configuration Management

**Environment-Specific Configs**:
.. code-block:: python

   # Development environment
   dev_config = AnalysisConsolidationConfig(
       enabled=True,
       metaxpress_style=False,  # Simple CSV for debugging
       output_filename="dev_summary.csv"
   )
   
   # Production environment
   prod_config = AnalysisConsolidationConfig(
       enabled=True,
       metaxpress_style=True,   # Full MetaXpress compatibility
       output_filename="metaxpress_results.csv"
   )

### Quality Control

**Validation Checks**:
- Verify all expected wells are present in consolidated output
- Check that analysis metrics are within expected ranges
- Compare consolidated results with individual well files for accuracy

The analysis consolidation system provides seamless integration between OpenHCS analysis pipelines and downstream data analysis workflows, ensuring that multi-well analysis results are immediately available in standardized, analysis-ready formats.
