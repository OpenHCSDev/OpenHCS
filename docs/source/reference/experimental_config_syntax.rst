Experimental Configuration Syntax Reference
===========================================

This document provides the complete syntax reference for defining complex experimental designs in Excel format (``config.xlsx``) for use with OpenHCS experimental analysis.

## File Structure

The configuration uses an Excel file with multiple sheets:

- **drug_curve_map**: Main experimental design definition
- **plate_groups**: Mapping of replicates to physical plates
- **Additional sheets**: As needed for complex experiments

## Sheet 1: drug_curve_map

### Global Parameters (Required)

These parameters must appear at the top of the sheet:

.. code-block:: text

   N                    3                    # Number of biological replicates
   Scope               EDDU_metaxpress       # Microscope format

**Supported Scopes:**

- ``EDDU_CX5``: ThermoFisher CX5 format
- ``EDDU_metaxpress``: MetaXpress format

### Control Definition Block (Optional)

Define control wells for normalization:

.. code-block:: text

   Controls            A01  B01  E01  F01  A05  B05  E05  F05  A09  B09  E09  F09
   Plate Group         1    1    1    1    1    1    1    1    1    1    1    1
   Group N             1    1    1    1    2    2    2    2    3    3    3    3

**Field Definitions:**

- **Controls**: Well positions for control conditions
- **Plate Group**: Physical plate identifier for each control well
- **Group N**: Biological replicate assignment (1=N1, 2=N2, 3=N3, etc.)

### Experimental Condition Blocks (Required)

Each experimental condition follows this pattern:

.. code-block:: text

   Condition           [Condition Name]      # Name of the experimental condition
   Dose                [dose1] [dose2] ...   # Dose series (concentrations, timepoints, etc.)
   Wells1              [well1] [well2] ...   # Wells for biological replicate 1
   Plate Group         [plate] [plate] ...   # Plate assignment for Wells1
   Wells1              [well1] [well2] ...   # Additional rows = technical replicates
   Plate Group         [plate] [plate] ...   # Plate assignment for additional Wells1
   Wells2              [well1] [well2] ...   # Wells for biological replicate 2
   Plate Group         [plate] [plate] ...   # Plate assignment for Wells2
   Wells3              [well1] [well2] ...   # Wells for biological replicate 3
   Plate Group         [plate] [plate] ...   # Plate assignment for Wells3

**Key Rules:**

1. **WellsN** (N=1,2,3...): Each number corresponds to a biological replicate
2. **Wells** (no number): Same wells applied to ALL biological replicates
3. **Multiple rows per WellsN**: Creates technical replicates (averaged together)
4. **Dose-to-well mapping**: First dose maps to first well, second dose to second well, etc.
5. **Plate Group**: Must follow each Wells row, maps wells to physical plates
6. **Empty rows**: Used to separate different conditions

### Complete Example Block

.. code-block:: text

   Condition           Drug_A + Inhibitor_B
   Dose                0    10   50   100
   Wells1              A01  A02  A03  A04    # N1: Control, 10μM, 50μM, 100μM
   Plate Group         1    1    1    1
   Wells1              B01  B02  B03  B04    # N1: Technical replicates
   Plate Group         1    1    1    1
   Wells2              A05  A06  A07  A08    # N2: Same doses
   Plate Group         1    1    1    1
   Wells2              B05  B06  B07  B08    # N2: Technical replicates
   Plate Group         1    1    1    1
   Wells3              A09  A10  A11  A12    # N3: Same doses
   Plate Group         1    1    1    1
   Wells3              B09  B10  B11  B12    # N3: Technical replicates
   Plate Group         1    1    1    1

## Sheet 2: plate_groups

Maps biological replicates to physical plate identifiers:

.. code-block:: text

        0         1
   0  NaN         1
   1   N1  20220818
   2   N2  20220818  
   3   N3  20220818

**Column Definitions:**

- **Column 0**: Replicate names (N1, N2, N3, etc.)
- **Column 1**: Physical plate identifier/barcode

## Data Processing Flow

1. **Parse global parameters** (N, Scope)
2. **Extract control definitions** for normalization
3. **Process each condition block**:
   - Map doses to wells for each biological replicate
   - Group technical replicates (multiple rows per WellsN)
   - Assign plate groups
4. **Load plate group mappings**
5. **Create data structure**: ``experiment_dict[condition][replicate][dose] = [(well, plate_group), ...]``

## Advanced Syntax Features

### Multi-Plate Experiments

.. code-block:: text

   Wells1              A01  A02  A03  A04
   Plate Group         1    1    2    2      # Wells A01,A02 on plate 1; A03,A04 on plate 2

### Same Wells Across All Replicates

.. code-block:: text

   Wells               A01  A02  A03  A04    # Applied to ALL biological replicates (N1, N2, N3...)
   Plate Group         1    1    1    1      # Plate mapping for all replicates

### Complex Technical Replication

.. code-block:: text

   Wells1              A01  A02  A03  A04    # First technical replicate
   Plate Group         1    1    1    1
   Wells1              B01  B02  B03  B04    # Second technical replicate
   Plate Group         1    1    1    1
   Wells1              C01  C02  C03  C04    # Third technical replicate
   Plate Group         1    1    1    1

### Variable Replicate Numbers

.. code-block:: text

   N                   4                     # Can have any number of replicates
   ...
   Wells1              ...                   # N1
   Wells2              ...                   # N2  
   Wells3              ...                   # N3
   Wells4              ...                   # N4

## Syntax Validation Rules

### Required Elements

- **N parameter**: Must be specified at top of sheet
- **Scope parameter**: Must be valid microscope format
- **Condition blocks**: At least one condition must be defined
- **Plate Group rows**: Must follow every Wells row

### Validation Checks

- **Dose-Well count matching**: Number of doses must equal number of wells in each row
- **Replicate completeness**: All WellsN (1 to N) must be defined for each condition
- **Plate Group presence**: Every Wells row must have corresponding Plate Group row
- **Well format validation**: Wells must follow standard format (A01, B12, etc.)

### Common Syntax Errors

**Missing Plate Group**:

.. code-block:: text

   Wells1              A01  A02  A03  A04
   # ERROR: Missing Plate Group row

**Dose-Well Mismatch**:

.. code-block:: text

   Dose                0    10   50          # 3 doses
   Wells1              A01  A02  A03  A04    # 4 wells - ERROR

**Invalid Scope**:

.. code-block:: text

   Scope               INVALID_SCOPE         # ERROR: Not supported

**Incomplete Replicates**:

.. code-block:: text

   N                   3
   Wells1              A01  A02  A03  A04    # N1 defined
   Wells2              A05  A06  A07  A08    # N2 defined
   # ERROR: Wells3 missing for N3

## Best Practices

### Naming Conventions

1. **Condition names**: Use descriptive, filesystem-safe names
2. **Dose units**: Include units in condition names or documentation
3. **Well organization**: Group related conditions in adjacent regions

### Layout Strategies

1. **Control distribution**: Spread controls across plate to detect edge effects
2. **Replicate balancing**: Distribute biological replicates across plate positions
3. **Technical replicates**: Use adjacent wells for technical replicates when possible

### Documentation

1. **Comments**: Use descriptive condition names as inline documentation
2. **Metadata**: Include experimental details in separate documentation
3. **Validation**: Test configuration with small datasets before full experiments

### File Management

1. **Version control**: Keep versioned copies of configuration files
2. **Backup**: Maintain backups of both configuration and results
3. **Naming**: Use descriptive filenames with dates/versions

## Example Files

Complete example configuration files are available in the OpenHCS documentation:

- :download:`experimental_config_example.xlsx <../examples/experimental_config_example.xlsx>` - Complete working example

## Integration with Analysis Pipeline

The configuration syntax integrates seamlessly with the OpenHCS experimental analysis pipeline:

.. code-block:: python

   from openhcs.formats.experimental_analysis import run_experimental_analysis

   # Configuration file follows syntax described above
   run_experimental_analysis(
       results_path="microscope_results.xlsx",
       config_file="./config.xlsx",  # Uses syntax from this reference
       compiled_results_path="./compiled_results_normalized.xlsx",
       heatmap_path="./heatmaps.xlsx"
   )

This syntax reference provides the complete specification for creating experimental configuration files that integrate with the OpenHCS experimental analysis system, enabling robust analysis of complex multi-condition, multi-replicate high-content screening experiments.
