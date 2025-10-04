#!/usr/bin/env python3
"""
Generate and upload synthetic test data to OMERO.

This script:
1. Generates synthetic microscopy images using SyntheticMicroscopyGenerator
2. Uploads them directly to OMERO via API
3. Returns dataset ID for use in demo
"""

import sys
import tempfile
from pathlib import Path
import numpy as np
from omero.gateway import BlitzGateway
from omero.model import DatasetI, ImageI, PixelsI
from omero.rtypes import rstring, rint, rdouble
import omero.gateway


def generate_and_upload_synthetic_data(
    conn,
    dataset_name: str = "OpenHCS_Synthetic_Test",
    grid_size=(2, 2),
    tile_size=(128, 128),
    wavelengths=2,
    z_stack_levels=3,
    well='A01'
):
    """Generate synthetic data and upload to OMERO."""

    print(f"[1/3] Generating synthetic microscopy data...")
    print(f"  Grid: {grid_size[0]}x{grid_size[1]}, Tile: {tile_size}, Channels: {wavelengths}, Z-levels: {z_stack_levels}")

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
            wells=[well],
            format='ImageXpress',
            auto_image_size=True
        )
        generator.generate_dataset()

        print(f"✓ Generated synthetic data")

        # Create dataset in OMERO
        print(f"\n[2/3] Creating OMERO dataset...")
        dataset = DatasetI()
        dataset.setName(rstring(dataset_name))
        dataset = conn.getUpdateService().saveAndReturnObject(dataset)
        dataset_id = dataset.getId().getValue()

        print(f"✓ Created dataset: {dataset_name} (ID: {dataset_id})")

        # Upload images to OMERO
        print(f"\n[3/3] Uploading images to OMERO...")

        plate_dir = Path(tmpdir) / well
        image_files = sorted(plate_dir.rglob("*.tif"))

        print(f"  Found {len(image_files)} images to upload")

        image_ids = []
        for i, img_path in enumerate(image_files, 1):
            # Read image
            import tifffile
            img_data = tifffile.imread(img_path)

            # Ensure 3D (Z, Y, X)
            if img_data.ndim == 2:
                img_data = img_data[np.newaxis, ...]

            # Upload to OMERO
            image_id = _upload_image_to_omero(
                conn, img_data, img_path.name, dataset_id
            )
            image_ids.append(image_id)

            if i % 5 == 0 or i == len(image_files):
                print(f"  Uploaded {i}/{len(image_files)} images...")

        print(f"✓ Uploaded {len(image_ids)} images")

    return dataset_id, image_ids


def _upload_image_to_omero(conn, img_data: np.ndarray, name: str, dataset_id: int) -> int:
    """Upload a single image to OMERO."""

    # Create image
    sizeZ, sizeY, sizeX = img_data.shape
    sizeC = 1
    sizeT = 1

    # Create image object
    image = conn.createImageFromNumpySeq(
        plane_gen=(img_data[z] for z in range(sizeZ)),
        name=name,
        sizeZ=sizeZ,
        sizeC=sizeC,
        sizeT=sizeT,
        dataset=conn.getObject("Dataset", dataset_id)
    )

    return image.getId()


def main():
    """Generate synthetic data and upload to OMERO."""

    # Connect to OMERO
    print("Connecting to OMERO...")
    conn = BlitzGateway('root', 'omero-root-password', host='localhost', port=4064)
    if not conn.connect():
        print("❌ Failed to connect to OMERO")
        print("   Make sure OMERO is running: docker-compose up -d")
        sys.exit(1)

    print("✓ Connected to OMERO\n")

    try:
        dataset_id, image_ids = generate_and_upload_synthetic_data(conn)

        print(f"\n✅ Setup complete!")
        print(f"   Dataset ID: {dataset_id}")
        print(f"   Images uploaded: {len(image_ids)}")
        print(f"\n   Use dataset ID {dataset_id} in omero_demo.py")

        return dataset_id

    finally:
        conn.close()


if __name__ == '__main__':
    main()

