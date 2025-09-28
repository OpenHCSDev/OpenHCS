Experimental Layout Configuration
==================================

OpenHCS provides a comprehensive Excel-based system for defining complex experimental designs with well-to-condition mapping, biological replicates, and dose-response curves for high-content screening experiments.

## Overview

The experimental layout system enables:

- **Well-to-condition mapping**: Assign specific wells to experimental conditions and doses
- **Biological replicates**: Manage multiple biological replicates (N1, N2, N3) across plates
- **Technical replicates**: Handle multiple wells per condition for statistical robustness
- **Control definition**: Define control wells for normalization and quality control
- **Multi-plate experiments**: Map replicates to physical plate identifiers
- **Dose-response curves**: Automatic dose-to-well mapping for concentration series

## Configuration File Structure

The experimental configuration uses an Excel file (``config.xlsx``) with multiple sheets:

- **drug_curve_map**: Main experimental design definition
- **plate_groups**: Mapping of biological replicates to physical plates
- **Additional sheets**: As needed for complex experiments

## Basic Configuration

### Global Parameters

Every configuration file must start with global parameters:

.. code-block:: text

   N                    3                    # Number of biological replicates
   Scope               EDDU_metaxpress       # Microscope format

**Supported Scopes**:
- ``EDDU_CX5``: ThermoFisher CX5 format
- ``EDDU_metaxpress``: MetaXpress format

### Simple Experimental Condition

Define a basic experimental condition with dose series:

.. code-block:: text

   Condition           Drug_Treatment
   Dose                0    10   50   100
   Wells1              A01  A02  A03  A04    # Biological replicate 1
   Plate Group         1    1    1    1
   Wells2              A05  A06  A07  A08    # Biological replicate 2
   Plate Group         1    1    1    1
   Wells3              A09  A10  A11  A12    # Biological replicate 3
   Plate Group         1    1    1    1

**Key Elements**:
- **Condition**: Descriptive name for the experimental condition
- **Dose**: Concentration series (can be any units: μM, nM, time points, etc.)
- **WellsN**: Wells assigned to biological replicate N (N=1,2,3...)
- **Plate Group**: Physical plate identifier for each well

## Advanced Features

### Control Wells Definition

Define control wells for normalization:

.. code-block:: text

   Controls            A01  B01  E01  F01  A05  B05  E05  F05  A09  B09  E09  F09
   Plate Group         1    1    1    1    1    1    1    1    1    1    1    1
   Group N             1    1    1    1    2    2    2    2    3    3    3    3

- **Controls**: Well positions for control conditions
- **Plate Group**: Physical plate identifier for each control well
- **Group N**: Biological replicate assignment (1=N1, 2=N2, 3=N3)

### Technical Replicates

Add technical replicates by using multiple rows per biological replicate:

.. code-block:: text

   Condition           Drug_A_High_Dose
   Dose                0    10   50   100
   Wells1              A01  A02  A03  A04    # First technical replicate set
   Plate Group         1    1    1    1
   Wells1              B01  B02  B03  B04    # Second technical replicate set
   Plate Group         1    1    1    1
   Wells1              C01  C02  C03  C04    # Third technical replicate set
   Plate Group         1    1    1    1

**Technical replicates are automatically averaged** during analysis.

### Multi-Plate Experiments

Distribute conditions across multiple physical plates:

.. code-block:: text

   Condition           Cross_Plate_Treatment
   Dose                0    10   50   100
   Wells1              A01  A02  A03  A04
   Plate Group         1    1    2    2      # Wells A01,A02 on plate 1; A03,A04 on plate 2
   Wells2              A05  A06  A07  A08
   Plate Group         1    1    2    2
   Wells3              A09  A10  A11  A12
   Plate Group         1    1    2    2

### Shared Wells Across Replicates

Use the same wells for all biological replicates:

.. code-block:: text

   Condition           Shared_Well_Treatment
   Dose                0    10   50   100
   Wells               A01  A02  A03  A04    # Applied to ALL biological replicates
   Plate Group         1    1    1    1

**Note**: ``Wells`` (without number) applies to all biological replicates (N1, N2, N3...).

## Plate Groups Configuration

The ``plate_groups`` sheet maps biological replicates to physical plate identifiers:

.. code-block:: text

        0         1
   0  NaN         1
   1   N1  20220818
   2   N2  20220819  
   3   N3  20220820

- **Column 0**: Replicate names (N1, N2, N3, etc.)
- **Column 1**: Physical plate identifier/barcode

## Complete Example

Here's a complete configuration for a drug dose-response experiment:

**Sheet: drug_curve_map**

.. code-block:: text

   N                    3
   Scope               EDDU_metaxpress

   Controls            A01  B01  C01  A12  B12  C12
   Plate Group         1    1    1    1    1    1
   Group N             1    1    1    2    2    2

   Condition           Drug_A_Treatment
   Dose                0    1    10   100
   Wells1              A02  A03  A04  A05
   Plate Group         1    1    1    1
   Wells1              B02  B03  B04  B05    # Technical replicates
   Plate Group         1    1    1    1
   Wells2              A06  A07  A08  A09
   Plate Group         1    1    1    1
   Wells2              B06  B07  B08  B09
   Plate Group         1    1    1    1
   Wells3              A10  A11  B10  B11
   Plate Group         1    1    1    1

   Condition           Drug_B_Treatment
   Dose                0    5    25   125
   Wells1              C02  C03  C04  C05
   Plate Group         1    1    1    1
   Wells2              C06  C07  C08  C09
   Plate Group         1    1    1    1
   Wells3              C10  C11  D10  D11
   Plate Group         1    1    1    1

**Sheet: plate_groups**

.. code-block:: text

        0         1
   0  NaN         1
   1   N1  PLATE001
   2   N2  PLATE001
   3   N3  PLATE001

## Usage in Analysis Pipeline

### Basic Analysis

.. code-block:: python

   from openhcs.formats.experimental_analysis import run_experimental_analysis

   # Run complete experimental analysis
   run_experimental_analysis(
       results_path="microscope_results.xlsx",     # Results from CX5/MetaXpress
       config_file="./config.xlsx",                # Experimental design
       compiled_results_path="./compiled_results_normalized.xlsx",
       heatmap_path="./heatmaps.xlsx"
   )

### Custom Analysis Pipeline

.. code-block:: python

   from openhcs.formats.experimental_analysis import (
       read_plate_layout, load_plate_groups, 
       make_experiment_dict_locations, read_results
   )

   # Parse experimental configuration
   scope, plate_layout, conditions, ctrl_positions, excluded_positions, per_well_datapoints = read_plate_layout("config.xlsx")
   plate_groups = load_plate_groups("config.xlsx")
   experiment_dict_locations = make_experiment_dict_locations(
       plate_groups, plate_layout, conditions
   )

   # Load and process results
   df = read_results("results.xlsx", scope=scope)
   # ... continue with custom analysis

## Data Processing Flow

The system processes experimental configurations through these steps:

1. **Parse global parameters** (N, Scope)
2. **Extract control definitions** for normalization
3. **Process each condition block**:
   - Map doses to wells for each biological replicate
   - Group technical replicates (multiple rows per WellsN)
   - Assign plate groups
4. **Load plate group mappings**
5. **Create data structure**: ``experiment_dict[condition][replicate][dose] = [(well, plate_group), ...]``

## Best Practices

### Experimental Design

1. **Consistent naming**: Use clear, descriptive condition names
2. **Logical well layout**: Group related conditions in adjacent plate regions
3. **Control placement**: Distribute controls across the plate to account for edge effects
4. **Replicate distribution**: Balance biological replicates across plate positions

### Configuration Management

1. **Documentation**: Include description in first row for complex experiments
2. **Validation**: Check that all WellsN (1 to N) are defined for each condition
3. **Backup**: Keep versioned copies of configuration files
4. **Testing**: Validate configuration with small test datasets before full experiments

### File Organization

.. code-block:: text

   experiment_folder/
   ├── config.xlsx                    # Experimental design
   ├── microscope_results.xlsx        # Raw results from microscope
   ├── compiled_results_normalized.xlsx # Processed results
   └── heatmaps.xlsx                  # Visualization outputs

## Error Handling

Common configuration errors and solutions:

**Missing Plate Group**:
- Each Wells row must be followed by Plate Group
- Solution: Add Plate Group row after every Wells row

**Dose-Well Mismatch**:
- Number of doses must match number of wells
- Solution: Ensure equal number of doses and wells in each row

**Invalid Scope**:
- Only EDDU_CX5 and EDDU_metaxpress supported
- Solution: Use correct scope identifier

**Missing Biological Replicates**:
- All WellsN (1 to N) must be defined for each condition
- Solution: Define Wells1, Wells2, ..., WellsN for each condition

The experimental layout system provides comprehensive support for complex high-content screening experimental designs, enabling robust statistical analysis and seamless integration with microscopy analysis workflows.
