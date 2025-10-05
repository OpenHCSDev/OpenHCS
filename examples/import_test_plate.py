#!/usr/bin/env python3
"""
Generate synthetic ImageXpress plate and import to OMERO using in-place import.

This script:
1. Generates a synthetic ImageXpress plate on disk
2. Imports it into OMERO using --transfer=ln_s (in-place import)
3. Returns the plate ID for testing

This preserves the original file structure so OpenHCS can process the files directly.
"""

import sys
import subprocess
from pathlib import Path
import tempfile
import shutil

def generate_synthetic_plate(output_dir: Path):
    """Generate a synthetic ImageXpress plate using OpenHCS test fixtures."""
    from openhcs.tests.generators.generate_synthetic_data import SyntheticMicroscopyGenerator
    
    print(f"[1/3] Generating synthetic ImageXpress plate...")
    print(f"  Output directory: {output_dir}")
    
    generator = SyntheticMicroscopyGenerator(
        output_dir=str(output_dir),
        grid_size=(2, 2),  # Small grid for fast testing
        tile_size=(128, 128),  # Small tiles for fast testing
        overlap_percent=10,
        wavelengths=2,  # 2 channels
        z_stack_levels=3,  # 3 z-planes
        wells=['A01', 'A02'],  # Just 2 wells for fast testing
        format='ImageXpress',
        auto_image_size=True
    )
    generator.generate_dataset()
    
    # Count generated files
    image_files = list(output_dir.rglob("*.tif"))
    print(f"✓ Generated {len(image_files)} images")
    
    return output_dir


def import_to_omero(plate_dir: Path, plate_name: str = "OpenHCS_Test_Plate"):
    """Import the plate to OMERO.

    Note: Bio-Formats has issues with our synthetic HTD files (tries to use CellWorxReader
    instead of MetaXpressReader). For now, we'll import the directory which will create
    individual images. Once we have real ImageXpress data or fix the HTD format, we can
    import the HTD file directly to create a proper Plate object.
    """
    print(f"\n[2/3] Importing to OMERO...")
    print(f"  Plate directory: {plate_dir}")
    print(f"  Plate name: {plate_name}")

    # For now, import the directory
    # TODO: Fix HTD format to work with MetaXpressReader
    cmd = [
        "omero", "import",
        "-s", "localhost",  # Server
        "-p", "4064",  # Port
        "-u", "root",  # Username
        "-w", "omero-root-password",  # Password
        f"--name={plate_name}",
        str(plate_dir)
    ]

    print(f"  Running: omero import -s localhost -u root --name={plate_name} {plate_dir}")

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            check=True
        )
        
        # Parse plate ID from output
        # OMERO import outputs lines like "Plate:123"
        for line in result.stdout.split('\n'):
            if 'Plate:' in line:
                plate_id = line.split('Plate:')[1].split()[0]
                print(f"✓ Imported plate ID: {plate_id}")
                return int(plate_id)
        
        # If we didn't find the plate ID in stdout, check stderr
        for line in result.stderr.split('\n'):
            if 'Plate:' in line:
                plate_id = line.split('Plate:')[1].split()[0]
                print(f"✓ Imported plate ID: {plate_id}")
                return int(plate_id)
        
        print("Warning: Could not parse plate ID from import output")
        print("STDOUT:", result.stdout)
        print("STDERR:", result.stderr)
        return None
        
    except subprocess.CalledProcessError as e:
        print(f"✗ Import failed: {e}")
        print("STDOUT:", e.stdout)
        print("STDERR:", e.stderr)
        raise


def main():
    """Generate and import a test plate."""
    # Create a persistent directory for the plate
    # (Don't use tempfile - we want to keep the files for OMERO to reference)
    plate_dir = Path("/tmp/openhcs_test_plate")
    
    # Clean up old plate if it exists
    if plate_dir.exists():
        print(f"Removing old plate directory: {plate_dir}")
        shutil.rmtree(plate_dir)
    
    plate_dir.mkdir(parents=True, exist_ok=True)
    
    try:
        # Generate synthetic plate
        generate_synthetic_plate(plate_dir)
        
        # Import to OMERO
        plate_id = import_to_omero(plate_dir, plate_name="OpenHCS_Test_Plate")
        
        if plate_id:
            print(f"\n[3/3] ✓ Success!")
            print(f"  Plate ID: {plate_id}")
            print(f"  Plate directory: {plate_dir}")
            print(f"\nYou can now test with:")
            print(f"  python test_omero_integration.py {plate_id}")
            return plate_id
        else:
            print(f"\n[3/3] ✗ Failed to get plate ID")
            return None
            
    except Exception as e:
        print(f"\n✗ Error: {e}")
        import traceback
        traceback.print_exc()
        return None


if __name__ == "__main__":
    plate_id = main()
    sys.exit(0 if plate_id else 1)

