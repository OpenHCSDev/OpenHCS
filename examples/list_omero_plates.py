#!/usr/bin/env python3
"""
List all plates in OMERO and show their IDs and file paths.
"""

from omero.gateway import BlitzGateway
from pathlib import Path

def list_plates():
    """List all plates in OMERO."""
    conn = BlitzGateway('root', 'omero-root-password', host='localhost', port=4064, secure=False)
    
    try:
        if not conn.connect():
            print("✗ Failed to connect to OMERO")
            return
        
        print("✓ Connected to OMERO")
        print("\nPlates in OMERO:")
        print("=" * 80)
        
        plates = list(conn.getObjects("Plate"))
        
        if not plates:
            print("No plates found in OMERO")
            return
        
        for plate in plates:
            print(f"\nPlate ID: {plate.getId()}")
            print(f"  Name: {plate.getName()}")
            print(f"  Description: {plate.getDescription() or 'N/A'}")
            
            # Get wells
            wells = list(plate.listChildren())
            print(f"  Wells: {len(wells)}")
            
            if wells:
                # Get first image to find file path
                well_samples = list(wells[0].listChildren())
                if well_samples:
                    image = well_samples[0].getImage()
                    if image:
                        print(f"  Image ID: {image.getId()}")
                        print(f"  Image name: {image.getName()}")
                        fileset = image.getFileset()
                        if fileset:
                            print(f"  Fileset ID: {fileset.getId()}")
                            orig_files = list(fileset.listFiles())
                            print(f"  Original files: {len(orig_files)}")
                            if orig_files:
                                first_file = orig_files[0]
                                file_path = first_file.getPath() + first_file.getName()
                                print(f"  File path: {file_path}")

                                # Try to find the plate directory
                                omero_data_dir = Path("/OMERO/ManagedRepository")
                                full_path = omero_data_dir / file_path
                                print(f"  Full path: {full_path}")
                                print(f"  Exists: {full_path.exists()}")
                                if full_path.exists():
                                    print(f"  Parent dir: {full_path.parent}")
                        else:
                            print(f"  No fileset (image created from pixels, not imported)")
        
        print("\n" + "=" * 80)
        print(f"\nTotal plates: {len(plates)}")
        
    finally:
        conn.close()


if __name__ == "__main__":
    list_plates()

