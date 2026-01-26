#!/usr/bin/env python3
"""
Generate composite figures showing XY and XZ max projections side by side.

For each well, creates a figure with:
- Left panel: XY max projection composite
- Right panel: XZ max projection composite

Usage:
    python scripts/generate_xy_xz_composite_figures.py \
        --input-dir /path/to/max_project \
        --output-dir /path/to/output
"""

import argparse
import logging
from pathlib import Path
import re

import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend
import matplotlib.pyplot as plt
from PIL import Image

# Set up logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


def parse_filename(filename: str) -> dict:
    """
    Parse filename to extract well and other metadata.
    
    Example: source_images_well_R07C05_site_1_timepoint_1_XY_max_composite.png
    Returns: {'well': 'R07C05', 'site': '1', 'timepoint': '1', 'projection': 'XY'}
    """
    pattern = r'well_([^_]+)_site_(\d+)_timepoint_(\d+)_(XY|XZ)_max_composite'
    match = re.search(pattern, filename)
    
    if not match:
        return None
    
    return {
        'well': match.group(1),
        'site': match.group(2),
        'timepoint': match.group(3),
        'projection': match.group(4)
    }


def create_composite_figure(xy_path: Path, xz_path: Path, output_path: Path, well_id: str) -> None:
    """
    Create a figure with XY and XZ projections side by side.
    
    Args:
        xy_path: Path to XY max projection composite image
        xz_path: Path to XZ max projection composite image
        output_path: Path to save output figure
        well_id: Well identifier for title
    """
    # Load images
    xy_img = Image.open(xy_path)
    xz_img = Image.open(xz_path)
    
    # Create figure with 2 subplots side by side
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 8))
    
    # Display XY projection
    ax1.imshow(xy_img)
    ax1.set_title('XY Max Projection', fontsize=14, weight='bold')
    ax1.axis('off')
    
    # Display XZ projection
    ax2.imshow(xz_img)
    ax2.set_title('XZ Max Projection', fontsize=14, weight='bold')
    ax2.axis('off')
    
    # Add overall title with well ID
    fig.suptitle(f'Well {well_id}', fontsize=16, weight='bold')
    
    # Adjust layout
    plt.tight_layout()
    
    # Save figure
    output_path.parent.mkdir(parents=True, exist_ok=True)
    plt.savefig(output_path, bbox_inches='tight', dpi=150)
    plt.close(fig)


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Generate composite figures with XY and XZ max projections side by side"
    )
    parser.add_argument(
        '--input-dir',
        type=Path,
        required=True,
        help='Directory containing XY and XZ max projection composite images'
    )
    parser.add_argument(
        '--output-dir',
        type=Path,
        required=True,
        help='Directory to save output figures'
    )
    
    args = parser.parse_args()
    
    if not args.input_dir.exists():
        logger.error(f"Input directory not found: {args.input_dir}")
        return
    
    # Find all composite images
    composite_images = list(args.input_dir.glob('*_composite.png'))
    logger.info(f"Found {len(composite_images)} composite images")
    
    # Group by well
    wells = {}
    for img_path in composite_images:
        metadata = parse_filename(img_path.name)
        if not metadata:
            logger.warning(f"Could not parse filename: {img_path.name}")
            continue
        
        well_key = f"{metadata['well']}_site_{metadata['site']}_timepoint_{metadata['timepoint']}"
        
        if well_key not in wells:
            wells[well_key] = {}
        
        wells[well_key][metadata['projection']] = img_path
    
    logger.info(f"Grouped into {len(wells)} wells")
    
    # Create composite figures
    created = 0
    for well_key, projections in sorted(wells.items()):
        if 'XY' not in projections or 'XZ' not in projections:
            logger.warning(f"Missing projection for {well_key}: {list(projections.keys())}")
            continue
        
        output_filename = f"{well_key}_composite_figure.png"
        output_path = args.output_dir / output_filename
        
        create_composite_figure(
            projections['XY'],
            projections['XZ'],
            output_path,
            well_key
        )
        
        created += 1
        logger.info(f"✓ Created: {output_filename}")
    
    logger.info(f"\n✅ Generated {created} composite figures in {args.output_dir}")


if __name__ == "__main__":
    main()

