# Figure Generation Scripts

This directory contains scripts for generating various figures, plots, and visualizations from imaging data and analysis results.

## Scripts

### `generate_xy_xz_composite_figures.py`
Creates side-by-side composite figures showing XY and XZ max projections for each well.

**Features:**
- Pairs XY and XZ max projection images
- Creates figures with two panels side by side
- Includes well identification in titles

**Usage:**
```bash
python scripts/figures/generate_xy_xz_composite_figures.py \
    --input-dir /path/to/max_project \
    --output-dir /path/to/output
```

---

### `generate_figure_overlays.py`
Generates figure overlays showing analyzed wells with ROIs (Regions of Interest) overlaid on images.

**Features:**
- Matches ROI files (.roi.zip) to corresponding images
- Filters wells based on analysis configuration (excludes excluded wells)
- Overlays polygon ROIs with labels on images
- Supports multiprocessing for faster processing
- Includes channel information and well annotations

**Usage:**
```bash
python scripts/figures/generate_figure_overlays.py \
    --plate-dir /path/to/plate1 \
    --plate-dir /path/to/plate2 \
    --config /path/to/config.xlsx \
    --results /path/to/results.csv
```

---

### `generate_automated_plots.py`
Generates automated bar plots with statistical analysis from compiled results files.

**Features:**
- Reads plot configuration from config.xlsx (plot_config sheet)
- Creates bar plots with error bars (SEM)
- Includes scatter points for individual data points
- Runs statistical tests (ANOVA, pairwise t-tests)
- Adds significance markers (*, **, ***, ns)
- Processes three data types: normalized, raw per replicate, and raw per well

**Usage:**
```bash
python scripts/figures/generate_automated_plots.py \
    --config /path/to/config.xlsx \
    --results-dir /path/to/compiled_results \
    --output-dir /path/to/plots
```

---

### `generate_figure_mosaics.py`
Creates mosaic/grid images from individual figure overlays, grouping by condition.

**Features:**
- Groups figures by experimental condition
- Creates grid layouts (roughly square)
- Sorts images by channel and replicate
- Outputs high-resolution mosaics (300 DPI)

**Usage:**
```bash
python scripts/figures/generate_figure_mosaics.py \
    --figures-dir /path/to/figures \
    --output-dir /path/to/mosaics
```

## Workflow

Typical figure generation workflow:

1. **Generate overlays**: Use `generate_figure_overlays.py` to create individual well figures with ROIs
2. **Create composites**: Use `generate_xy_xz_composite_figures.py` for projection comparisons
3. **Build mosaics**: Use `generate_figure_mosaics.py` to create condition summary grids
4. **Plot statistics**: Use `generate_automated_plots.py` for quantitative analysis plots

## Dependencies

All scripts require:
- Python 3.x
- matplotlib
- numpy
- PIL/Pillow
- pandas (for automated plots)
- scipy (for statistical tests)
- openhcs package (for ROI handling)

## Related

See also `../napari-plugins/` for napari plugins for creating orthogonal projections and exporting layers directly from napari.
