Analysis Consolidation System
=============================

OpenHCS provides an automatic analysis consolidation system that aggregates CSV-based analysis results from pipelines into MetaXpress-compatible summary tables, enabling seamless integration with existing microscopy analysis workflows.

## Overview

The analysis consolidation system addresses the challenge of managing multiple analysis outputs across wells and analysis types by:

- **Automatic aggregation**: Consolidates CSV files from multiple wells into single summary tables
- **MetaXpress compatibility**: Generates output format compatible with MetaXpress analysis tools
- **Pipeline integration**: Automatically triggers after pipeline completion
- **Flexible configuration**: Configurable output formats, file patterns, and metadata

## Architecture Components

### Core Modules

**consolidate_analysis_results.py**
  Primary consolidation engine that processes CSV files and creates summary tables

**consolidate_special_outputs.py**
  Handles special output types and custom aggregation patterns

**metaxpress.py**
  MetaXpress format compatibility and legacy analysis support

### Configuration Classes

The system uses two main configuration dataclasses:

.. code-block:: python

   @dataclass(frozen=True)
   class AnalysisConsolidationConfig:
       """Configuration for automatic analysis results consolidation."""
       enabled: bool = True
       metaxpress_style: bool = True
       well_pattern: str = r"([A-Z]\d{2})"
       file_extensions: tuple[str, ...] = (".csv",)
       exclude_patterns: tuple[str, ...] = (r".*consolidated.*", r".*summary.*")
       output_filename: str = "metaxpress_style_summary.csv"

   @dataclass(frozen=True)
   class PlateMetadataConfig:
       """Configuration for plate metadata in MetaXpress-style output."""
       barcode: Optional[str] = None
       plate_name: Optional[str] = None
       plate_id: Optional[str] = None
       description: Optional[str] = None
       acquisition_user: str = "OpenHCS"
       z_step: str = "1"

## Orchestrator Integration

The analysis consolidation system integrates directly with the ``PipelineOrchestrator`` and runs automatically after plate execution:

.. code-block:: python

   # In orchestrator.py
   def run_compiled_plate(self, compiled_contexts: Dict[str, Any]) -> Dict[str, Any]:
       # ... execute pipeline ...
       
       # Run automatic analysis consolidation if enabled
       shared_context = get_current_global_config(GlobalPipelineConfig)
       if shared_context.analysis_consolidation.enabled:
           # Find results directory from compiled contexts
           results_dir = self._find_results_directory(compiled_contexts)
           
           if results_dir and results_dir.exists():
               csv_files = list(results_dir.glob("*.csv"))
               if csv_files:
                   consolidate_analysis_results(
                       results_directory=str(results_dir),
                       axis_ids=list(compiled_contexts.keys()),
                       consolidation_config=shared_context.analysis_consolidation,
                       plate_metadata_config=shared_context.plate_metadata
                   )

**Automatic Triggering**: The system automatically detects when analysis results are available and triggers consolidation without user intervention.

## MetaXpress Format Support

### Header Structure

The system generates MetaXpress-compatible headers with plate metadata:

.. code-block:: python

   def create_metaxpress_header(summary_df: pd.DataFrame, plate_metadata: Dict[str, str]) -> List[List[str]]:
       """Create MetaXpress-style header rows with metadata."""
       header_rows = [
           ['Barcode', plate_metadata.get('barcode', 'OpenHCS-Plate')],
           ['Plate Name', plate_metadata.get('plate_name', 'OpenHCS Analysis Results')],
           ['Plate ID', plate_metadata.get('plate_id', '00000')],
           ['Description', plate_metadata.get('description', 'Consolidated analysis results')],
           ['Acquisition User', plate_metadata.get('acquisition_user', 'OpenHCS')],
           ['Z Step', plate_metadata.get('z_step', '1')]
       ]
       return header_rows

### Column Organization

**MetaXpress-style column ordering**:
1. **Well column first**: Primary identifier for each row
2. **Grouped by analysis type**: Columns grouped by analysis method
3. **Sorted within groups**: Consistent ordering within each analysis type

### Output Format

The consolidated output follows MetaXpress conventions:

::

   Barcode,OpenHCS-Plate-001
   Plate Name,Cell Analysis Results
   Plate ID,12345
   Description,Consolidated analysis results from OpenHCS pipeline: 96 wells analyzed
   Acquisition User,OpenHCS
   Z Step,1
   Well,Cell Count (cell_counting),Cell Area Mean (cell_counting),Intensity Mean (intensity_analysis)
   A01,245,156.7,0.823
   A02,198,142.3,0.756
   ...

## Pipeline Function Integration

The system provides a pipeline-compatible function for use in ``FunctionStep`` objects:

.. code-block:: python

   @numpy_func
   @special_outputs(("consolidated_results", materialize_consolidated_results))
   def consolidate_analysis_results_pipeline(
       image_stack: np.ndarray,
       results_directory: str,
       consolidation_config: AnalysisConsolidationConfig,
       plate_metadata_config: PlateMetadataConfig
   ) -> tuple[np.ndarray, pd.DataFrame]:
       """Pipeline-compatible version of consolidate_analysis_results."""
       
       summary_df = consolidate_analysis_results(
           results_directory=results_directory,
           consolidation_config=consolidation_config,
           plate_metadata_config=plate_metadata_config,
           output_path=None  # Handled by materialization
       )
       
       return image_stack, summary_df

**Special Outputs Integration**: Uses the ``@special_outputs`` decorator to handle DataFrame materialization through the OpenHCS special outputs system.

## File Pattern Recognition

### Well ID Extraction

The system uses configurable regex patterns to extract well IDs from filenames:

.. code-block:: python

   # Default pattern for standard 96/384-well plates
   well_pattern = r"([A-Z]\d{2})"  # Matches A01, B12, etc.
   
   # Custom patterns can be configured
   well_pattern = r"([A-Z]\d{1,2})"  # Matches A1, A01, etc.

### File Filtering

**Include patterns**: File extensions to process (default: ``.csv``)
**Exclude patterns**: Patterns to skip (consolidated files, summaries, etc.)

.. code-block:: python

   file_extensions = (".csv",)
   exclude_patterns = (r".*consolidated.*", r".*metaxpress.*", r".*summary.*")

## Analysis Type Detection

The system automatically detects analysis types from filename patterns:

.. code-block:: python

   def detect_analysis_type(file_path: str) -> str:
       """Detect analysis type from filename patterns."""
       filename = Path(file_path).stem.lower()
       
       # Common analysis type patterns
       if 'cell_count' in filename or 'counting' in filename:
           return 'cell_counting'
       elif 'intensity' in filename or 'fluorescence' in filename:
           return 'intensity_analysis'
       elif 'morphology' in filename or 'shape' in filename:
           return 'morphology_analysis'
       else:
           return 'general_analysis'

## Configuration Integration

The analysis consolidation system integrates with the global configuration system:

.. code-block:: python

   @dataclass(frozen=True)
   class GlobalPipelineConfig:
       # ... other config fields ...
       
       analysis_consolidation: AnalysisConsolidationConfig = field(default_factory=AnalysisConsolidationConfig)
       """Configuration for automatic analysis results consolidation."""
       
       plate_metadata: PlateMetadataConfig = field(default_factory=PlateMetadataConfig)
       """Configuration for plate metadata in consolidated outputs."""

**Global Context**: Configuration is accessible throughout the pipeline execution via the global context system.

## Benefits and Use Cases

### **Workflow Integration**
- **Seamless MetaXpress compatibility**: Direct import into existing analysis workflows
- **Automatic execution**: No manual consolidation steps required
- **Consistent formatting**: Standardized output across different analysis types

### **Data Management**
- **Single summary files**: Reduces file proliferation from multi-well analyses
- **Structured metadata**: Preserves experimental context and plate information
- **Flexible aggregation**: Configurable summarization strategies per analysis type

### **Analysis Efficiency**
- **Immediate availability**: Consolidated results available immediately after pipeline completion
- **Standard format**: Compatible with downstream statistical analysis tools
- **Quality control**: Consistent data structure enables automated validation

The analysis consolidation system provides essential infrastructure for high-throughput microscopy workflows, ensuring that OpenHCS analysis results integrate seamlessly with existing laboratory data management and analysis pipelines.
