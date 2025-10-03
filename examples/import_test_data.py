#!/usr/bin/env python3
"""
Import OpenHCS test data into OMERO for demo purposes.

This script takes existing test data from tests/data/ and imports it into OMERO,
creating a dataset that can be used for the OMERO integration demo.
"""

import sys
from pathlib import Path
from omero.gateway import BlitzGateway
from omero.model import DatasetI, PlateI
from omero.rtypes import rstring


def import_test_plate(conn, plate_path: Path, dataset_name: str = "OpenHCS_Test_Data"):
    """Import a test plate into OMERO."""
    
    # Create dataset
    dataset = DatasetI()
    dataset.setName(rstring(dataset_name))
    dataset = conn.getUpdateService().saveAndReturnObject(dataset)
    dataset_id = dataset.getId().getValue()
    
    print(f"✓ Created dataset: {dataset_name} (ID: {dataset_id})")
    
    # Import images from plate
    # Note: This is a simplified version - real import would use omero-py's import functionality
    print(f"📁 Scanning plate directory: {plate_path}")
    
    image_files = list(plate_path.rglob("*.tif")) + list(plate_path.rglob("*.tiff"))
    print(f"📸 Found {len(image_files)} image files")
    
    if not image_files:
        print("⚠️  No image files found. Make sure test data exists.")
        return None
    
    print(f"\n💡 To import these files into OMERO, run:")
    print(f"   omero import -d {dataset_id} {plate_path}")
    print(f"\nOr use OMERO.web interface at http://localhost:4080")
    
    return dataset_id


def main():
    # Connect to OMERO
    conn = BlitzGateway('root', 'omero-root-password', host='localhost', port=4064)
    if not conn.connect():
        print("❌ Failed to connect to OMERO")
        sys.exit(1)
    
    print("✓ Connected to OMERO")
    
    try:
        # Find test data
        test_data_dir = Path("tests/data")
        if not test_data_dir.exists():
            print(f"❌ Test data directory not found: {test_data_dir}")
            sys.exit(1)
        
        # Look for plate directories
        plate_dirs = [d for d in test_data_dir.iterdir() if d.is_dir()]
        
        if not plate_dirs:
            print(f"❌ No plate directories found in {test_data_dir}")
            sys.exit(1)
        
        print(f"\n📦 Found {len(plate_dirs)} plate(s):")
        for i, plate_dir in enumerate(plate_dirs, 1):
            print(f"  {i}. {plate_dir.name}")
        
        # Import first plate
        plate_path = plate_dirs[0]
        print(f"\n🔄 Importing: {plate_path.name}")
        
        dataset_id = import_test_plate(conn, plate_path)
        
        if dataset_id:
            print(f"\n✅ Setup complete!")
            print(f"   Dataset ID: {dataset_id}")
            print(f"   Use this ID in omero_demo.py")
        
    finally:
        conn.close()


if __name__ == '__main__':
    main()

