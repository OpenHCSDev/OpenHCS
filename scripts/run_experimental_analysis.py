#!/usr/bin/env python3
"""
Easy-to-use script for running OpenHCS experimental analysis.

This script consolidates MetaXpress/CX5 results with experimental configuration
to produce normalized results and heatmaps.

Usage:
    python scripts/run_experimental_analysis.py <directory>

    Where <directory> contains:
    - config.xlsx (experimental configuration)
    - metaxpress_style_summary.csv (consolidated results from OpenHCS)

    Output files will be created in the same directory:
    - compiled_results_normalized.xlsx
    - heatmaps.xlsx

Example:
    python scripts/run_experimental_analysis.py /path/to/experiment/2025-10-24
"""

import sys
import re
from pathlib import Path
import pandas as pd


def convert_opera_phenix_to_standard_well_id(well_id: str) -> str:
    """
    Convert Opera Phenix well ID (R02C03) to standard format (B03).

    Args:
        well_id: Opera Phenix format well ID (e.g., R02C03)

    Returns:
        Standard format well ID (e.g., B03)
    """
    # Match Opera Phenix format: R##C##
    match = re.match(r'[Rr](\d+)[Cc](\d+)', well_id)
    if match:
        row_num = int(match.group(1))
        col_num = int(match.group(2))

        # Convert row number to letter (1=A, 2=B, etc.)
        row_letter = chr(ord('A') + row_num - 1)

        # Format as standard well ID
        return f"{row_letter}{col_num:02d}"

    # If not Opera Phenix format, return as-is
    return well_id


def convert_summary_well_ids(csv_path: Path) -> Path:
    """
    Convert Opera Phenix well IDs in summary CSV to standard format.

    Creates a new file with _converted suffix.

    Args:
        csv_path: Path to metaxpress_style_summary.csv

    Returns:
        Path to converted CSV file
    """
    # Read the entire CSV as text to preserve MetaXpress header
    with open(csv_path, 'r') as f:
        lines = f.readlines()

    # Find the "Well" header row
    well_row_idx = None
    for i, line in enumerate(lines):
        if line.startswith('Well,'):
            well_row_idx = i
            break

    if well_row_idx is None:
        # No Well column found, return original
        return csv_path

    # Check first data row to see if it has Opera Phenix format
    if well_row_idx + 1 < len(lines):
        first_data_line = lines[well_row_idx + 1]
        first_well = first_data_line.split(',')[0].strip()

        if re.match(r'[Rr]\d+[Cc]\d+', first_well):
            print(f"Converting Opera Phenix well IDs to standard format...")
            print(f"  Example: {first_well} -> {convert_opera_phenix_to_standard_well_id(first_well)}")

            # Convert all data rows (after the Well header)
            converted_lines = lines[:well_row_idx + 1]  # Keep header rows

            for line in lines[well_row_idx + 1:]:
                parts = line.split(',', 1)  # Split only on first comma
                if len(parts) >= 2:
                    well_id = parts[0].strip()
                    rest = parts[1]

                    # Convert well ID if it matches Opera Phenix format
                    if re.match(r'[Rr]\d+[Cc]\d+', well_id):
                        converted_well = convert_opera_phenix_to_standard_well_id(well_id)
                        converted_lines.append(f"{converted_well},{rest}")
                    else:
                        converted_lines.append(line)
                else:
                    converted_lines.append(line)

            # Save to new file
            converted_path = csv_path.parent / f"{csv_path.stem}_converted{csv_path.suffix}"
            with open(converted_path, 'w') as f:
                f.writelines(converted_lines)

            print(f"  Saved converted file: {converted_path.name}")
            return converted_path

    # No conversion needed
    return csv_path


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        print("\nError: Missing directory argument")
        sys.exit(1)
    
    # Get directory from command line
    directory = Path(sys.argv[1])
    
    if not directory.exists():
        print(f"Error: Directory not found: {directory}")
        sys.exit(1)
    
    # Define expected input files
    config_file = directory / "config.xlsx"
    results_file = directory / "metaxpress_style_summary.csv"
    
    # Check if input files exist
    if not config_file.exists():
        print(f"Error: Config file not found: {config_file}")
        print("Expected: config.xlsx in the specified directory")
        sys.exit(1)
    
    if not results_file.exists():
        print(f"Error: Results file not found: {results_file}")
        print("Expected: metaxpress_style_summary.csv in the specified directory")
        sys.exit(1)
    
    # Define output files
    compiled_results = directory / "compiled_results_normalized.xlsx"
    heatmaps = directory / "heatmaps.xlsx"
    
    print("=" * 60)
    print("OpenHCS Experimental Analysis")
    print("=" * 60)
    print(f"Directory: {directory}")
    print(f"Config:    {config_file.name}")
    print(f"Results:   {results_file.name}")
    print("=" * 60)

    # Convert Opera Phenix well IDs if needed
    converted_results_file = convert_summary_well_ids(results_file)

    # Import and run analysis
    try:
        from openhcs.formats.experimental_analysis import run_experimental_analysis

        print("\nRunning experimental analysis...")
        run_experimental_analysis(
            results_path=str(converted_results_file),
            config_file=str(config_file),
            compiled_results_path=str(compiled_results),
            heatmap_path=str(heatmaps)
        )
        
        print("\n" + "=" * 60)
        print("✓ Analysis complete!")
        print("=" * 60)
        print(f"Compiled results: {compiled_results.name}")
        print(f"Heatmaps:         {heatmaps.name}")
        print("=" * 60)
        
    except Exception as e:
        print(f"\n✗ Error during analysis: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()

