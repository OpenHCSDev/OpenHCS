#!/usr/bin/env python3
"""
Generate and upload synthetic test data to OMERO as a Plate.

This script:
1. Generates synthetic microscopy images using SyntheticMicroscopyGenerator
2. Uploads them to OMERO as a proper Plate/Well/WellSample structure
3. Returns plate ID for use in demo
"""

import sys
import tempfile
from pathlib import Path
import numpy as np
from omero.gateway import BlitzGateway
import omero.model
from omero.rtypes import rstring, rint, rdouble, rlong
import omero.gateway


def generate_and_upload_synthetic_plate(
    conn,
    plate_name: str = "OpenHCS_Synthetic_Plate",
    grid_size=(2, 2),
    tile_size=(128, 128),
    wavelengths=2,
    z_stack_levels=3,
    wells=['A01', 'A02', 'B01', 'B02']
):
    """
    Generate synthetic data and upload to OMERO as a Plate.

    This creates a proper HCS Plate structure with Wells and WellSamples,
    preserving the plate organization that OpenHCS expects.
    """

    print(f"[1/4] Generating synthetic microscopy data...")
    print(f"  Grid: {grid_size[0]}x{grid_size[1]}, Tile: {tile_size}, Channels: {wavelengths}, Z-levels: {z_stack_levels}")
    print(f"  Wells: {wells}")

    # Generate synthetic data to temp directory
    from openhcs.tests.generators.generate_synthetic_data import SyntheticMicroscopyGenerator

    with tempfile.TemporaryDirectory() as tmpdir:
        generator = SyntheticMicroscopyGenerator(
            output_dir=tmpdir,
            grid_size=grid_size,
            tile_size=tile_size,
            overlap_percent=10,
            wavelengths=wavelengths,
            z_stack_levels=z_stack_levels,
            wells=wells,
            format='ImageXpress',
            auto_image_size=True
        )
        generator.generate_dataset()

        print(f"✓ Generated synthetic data for {len(wells)} wells")

        # Create Plate in OMERO
        print(f"\n[2/4] Creating OMERO Plate...")
        update_service = conn.getUpdateService()

        plate = omero.model.PlateI()
        plate.setName(rstring(plate_name))
        plate.setColumnNamingConvention(rstring("number"))
        plate.setRowNamingConvention(rstring("letter"))
        plate = update_service.saveAndReturnObject(plate)
        plate_id = plate.getId().getValue()

        print(f"✓ Created plate: {plate_name} (ID: {plate_id})")

        # Upload images and create Wells
        print(f"\n[3/4] Uploading images and creating Wells...")

        # Group images by well
        image_files = sorted(Path(tmpdir).rglob("*.tif"))
        print(f"  Found {len(image_files)} images to upload")

        # Parse well positions from filenames
        # ImageXpress format: <well>_s<site>_w<channel>_z<z>.tif
        from collections import defaultdict
        wells_data = defaultdict(list)

        for img_path in image_files:
            # Extract well from filename (e.g., "A01_s1_w1_z0.tif" -> "A01")
            filename = img_path.name
            well_id = filename.split('_')[0]  # First part is well ID
            wells_data[well_id].append(img_path)

        # Create Wells and upload images
        for well_idx, (well_id, well_images) in enumerate(sorted(wells_data.items()), 1):
            # Parse well position (e.g., "A01" -> row=0, col=0)
            row = ord(well_id[0]) - ord('A')  # A=0, B=1, etc.
            col = int(well_id[1:]) - 1  # 01=0, 02=1, etc.

            # Create Well
            well = omero.model.WellI()
            well.setPlate(omero.model.PlateI(plate_id, False))
            well.setColumn(rint(col))
            well.setRow(rint(row))

            # Upload images for this well and create WellSamples
            for site_idx, img_path in enumerate(sorted(well_images)):
                # Read image
                import tifffile
                img_data = tifffile.imread(img_path)

                # Ensure 3D (Z, Y, X)
                if img_data.ndim == 2:
                    img_data = img_data[np.newaxis, ...]

                # Upload image to OMERO
                # createImageFromNumpySeq expects planes in order: T, C, Z
                # For single timepoint, single channel: just iterate through Z
                def plane_generator():
                    for t in range(1):  # sizeT=1
                        for c in range(1):  # sizeC=1
                            for z in range(img_data.shape[0]):  # sizeZ
                                yield img_data[z]

                image = conn.createImageFromNumpySeq(
                    zctPlanes=plane_generator(),
                    imageName=img_path.name,
                    sizeZ=img_data.shape[0],
                    sizeC=1,
                    sizeT=1
                )

                # Create WellSample linking image to well
                ws = omero.model.WellSampleI()
                ws.setImage(omero.model.ImageI(image.getId(), False))
                ws.setWell(well)
                well.addWellSample(ws)

            # Save well with all its samples
            update_service.saveObject(well)
            print(f"  Created well {well_id} (row={row}, col={col}) with {len(well_images)} images")

        print(f"✓ Created {len(wells_data)} wells with images")

    return plate_id


def main():
    """Generate synthetic plate and upload to OMERO."""

    # Connect to OMERO
    print("Connecting to OMERO...")
    conn = BlitzGateway('root', 'omero-root-password', host='localhost', port=4064, secure=False)
    if not conn.connect():
        print("❌ Failed to connect to OMERO")
        print("   Make sure OMERO is running: docker-compose up -d")
        sys.exit(1)

    print("✓ Connected to OMERO\n")

    try:
        plate_id = generate_and_upload_synthetic_plate(
            conn,
            wells=['A01', 'A02', 'B01', 'B02']
        )

        print(f"\n✅ Setup complete!")
        print(f"   Plate ID: {plate_id}")
        print(f"\n   Use plate ID {plate_id} in omero_demo.py")
        print(f"\n   View in OMERO.web: http://localhost:4080/webclient/?show=plate-{plate_id}")

        return plate_id

    finally:
        conn.close()


if __name__ == '__main__':
    main()

