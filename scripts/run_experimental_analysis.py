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
from pathlib import Path


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
    
    # Import and run analysis
    try:
        from openhcs.formats.experimental_analysis import run_experimental_analysis
        
        print("\nRunning experimental analysis...")
        run_experimental_analysis(
            results_path=str(results_file),
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

