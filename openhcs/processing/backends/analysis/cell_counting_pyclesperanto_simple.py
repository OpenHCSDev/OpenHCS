"""
Simplified GPU-accelerated cell counting using pyclesperanto Voronoi-Otsu labeling.

This module provides a clean, simple implementation based on the pyclesperanto
Voronoi-Otsu labeling reference workflow, while maintaining compatibility with
the existing OpenHCS materialization system.
"""

import numpy as np
import logging
from typing import Dict, List, Tuple, Any, Union
from dataclasses import dataclass
from enum import Enum

logger = logging.getLogger(__name__)

# Core scientific computing imports
import pandas as pd
import json
import pyclesperanto as cle

# OpenHCS imports
from openhcs.core.memory import pyclesperanto as pyclesperanto_func
from openhcs.core.pipeline.function_contracts import special_outputs
from openhcs.processing.materialization import materializer_spec, tiff_stack_materializer
from openhcs.constants.constants import Backend


class DetectionMethod(Enum):
    """Simplified cell detection methods."""
    VORONOI_OTSU = "voronoi_otsu"      # Voronoi-Otsu labeling (reference workflow)
    THRESHOLD = "threshold"            # Simple thresholding (fallback)


@dataclass
class CellCountResult:
    """Results for single-channel cell counting - compatible with existing system."""
    slice_index: int
    method: str
    cell_count: int
    cell_positions: List[Tuple[float, float]]  # (x, y) centroids
    cell_areas: List[float]
    cell_intensities: List[float]
    detection_confidence: List[float]
    parameters_used: Dict[str, Any]
    binary_mask: np.ndarray = None  # Labeled mask for ROI extraction


def materialize_cell_counts(data: List[CellCountResult], path: str, filemanager, backend: str) -> str:
    """Materialize cell counting results - compatible with existing system."""
    logger.info(f"🔬 CELL_COUNT_MATERIALIZE: Called with path={path}, data_length={len(data) if data else 0}, backend={backend}")

    if not data:
        logger.warning("🔬 CELL_COUNT_MATERIALIZE: No data to materialize")
        return path

    # Generate output file paths
    base_path = path.replace('.pkl', '')
    json_path = f"{base_path}.json"
    csv_path = f"{base_path}_details.csv"

    # Ensure output directory exists for disk backend
    from pathlib import Path
    output_dir = Path(json_path).parent
    if backend == Backend.DISK.value:
        filemanager.ensure_directory(str(output_dir), backend)

    summary = {
        "analysis_type": "single_channel_cell_counting",
        "total_slices": len(data),
        "results_per_slice": []
    }
    rows = []

    total_cells = 0
    for result in data:
        total_cells += result.cell_count

        # Add to summary
        summary["results_per_slice"].append({
            "slice_index": result.slice_index,
            "method": result.method,
            "cell_count": result.cell_count,
            "avg_cell_area": np.mean(result.cell_areas) if result.cell_areas else 0,
            "avg_cell_intensity": np.mean(result.cell_intensities) if result.cell_intensities else 0,
            "parameters": result.parameters_used
        })

        # Add individual cell data to CSV
        for i, (pos, area, intensity, confidence) in enumerate(zip(
            result.cell_positions, result.cell_areas,
            result.cell_intensities, result.detection_confidence
        )):
            rows.append({
                'slice_index': result.slice_index,
                'cell_id': f"slice_{result.slice_index}_cell_{i}",
                'x_position': pos[0],
                'y_position': pos[1],
                'cell_area': area,
                'cell_intensity': intensity,
                'detection_confidence': confidence,
                'detection_method': result.method
            })

    summary["total_cells_all_slices"] = total_cells
    summary["average_cells_per_slice"] = total_cells / len(data) if data else 0

    # Save JSON summary
    json_content = json.dumps(summary, indent=2, default=str)
    if filemanager.exists(json_path, backend):
        filemanager.delete(json_path, backend)
    filemanager.save(json_content, json_path, backend)

    # Save CSV details
    if rows:
        df = pd.DataFrame(rows)
        csv_content = df.to_csv(index=False)
        if filemanager.exists(csv_path, backend):
            filemanager.delete(csv_path, backend)
        filemanager.save(csv_content, csv_path, backend)

    return json_path


def materialize_segmentation_masks(data: List[np.ndarray], path: str, filemanager, backend: str) -> str:
    """Materialize segmentation masks as ROIs - compatible with existing system."""
    logger.info(f"🔬 SEGMENTATION_MATERIALIZE: Called with path={path}, backend={backend}, masks_count={len(data) if data else 0}")

    if not data:
        logger.info("🔬 SEGMENTATION_MATERIALIZE: No segmentation masks to materialize")
        summary_path = path.replace('.pkl', '_segmentation_summary.txt')
        summary_content = "No segmentation masks generated (return_segmentation_mask=False)\n"
        filemanager.save(summary_content, summary_path, backend)
        return summary_path

    # Extract ROIs from labeled masks
    from polystore.roi import extract_rois_from_labeled_mask

    all_rois = []
    total_cells = 0
    for z_idx, mask in enumerate(data):
        rois = extract_rois_from_labeled_mask(
            mask,
            min_area=10,
            extract_contours=True
        )
        all_rois.extend(rois)
        total_cells += len(rois)
        logger.debug(f"🔬 SEGMENTATION_MATERIALIZE: Extracted {len(rois)} ROIs from z-plane {z_idx}")

    logger.info(f"🔬 SEGMENTATION_MATERIALIZE: Extracted {total_cells} total ROIs from {len(data)} z-planes")

    # Save ROIs
    base_path = path.replace('.pkl', '')
    roi_path = f"{base_path}_rois.roi.zip"

    if all_rois:
        filemanager.save(all_rois, roi_path, backend)
        logger.info(f"🔬 SEGMENTATION_MATERIALIZE: Saved {len(all_rois)} ROIs to {backend} backend")

    # Save summary
    summary_path = f"{base_path}_segmentation_summary.txt"
    summary_content = f"Segmentation ROIs: {len(all_rois)} cells\n"
    summary_content += f"Z-planes: {len(data)}\n"
    if all_rois:
        summary_content += f"ROI file: {roi_path}\n"
    else:
        summary_content += f"No ROIs extracted (all regions below min_area threshold)\n"

    filemanager.save(summary_content, summary_path, backend)

    return summary_path


@pyclesperanto_func
@special_outputs(
    ("cell_counts", materializer_spec("cell_counts")),
    ("segmentation_masks", tiff_stack_materializer(
        summary_suffix="_segmentation_summary.txt"
    ))
)
def count_cells_single_channel(
    image_stack: np.ndarray,
    # Simplified parameters
    detection_method: DetectionMethod = DetectionMethod.VORONOI_OTSU,
    # Core parameters
    gaussian_sigma: float = 1.0,
    min_cell_area: int = 50,
    max_cell_area: int = 5000,
    # Output parameters
    return_segmentation_mask: bool = False
) -> Tuple[np.ndarray, List[CellCountResult]]:
    """
    Count cells using simplified Voronoi-Otsu labeling workflow.
    
    This implementation follows the pyclesperanto reference workflow:
    1. Gaussian blur
    2. Detect spots
    3. Otsu threshold
    4. Masked Voronoi labeling
    
    Args:
        image_stack: 3D array (Z, Y, X) where each Z slice is processed independently
        detection_method: Method for cell detection (VORONOI_OTSU or THRESHOLD)
        gaussian_sigma: Standard deviation for Gaussian blur
        min_cell_area: Minimum area for valid cells (pixels)
        max_cell_area: Maximum area for valid cells (pixels)
        return_segmentation_mask: Return segmentation masks in output
        
    Returns:
        output_stack: Original image stack unchanged (Z, Y, X)
        cell_count_results: List of CellCountResult objects for each slice
        segmentation_masks: (Special output) List of segmentation mask arrays if requested
    """
    if image_stack.ndim != 3:
        raise ValueError(f"Expected 3D image stack, got {image_stack.ndim}D")
    
    results = []
    segmentation_masks = []

    # Store parameters for reproducibility
    parameters = {
        "detection_method": detection_method.value,
        "gaussian_sigma": gaussian_sigma,
        "min_cell_area": min_cell_area,
        "max_cell_area": max_cell_area,
        "return_segmentation_mask": return_segmentation_mask
    }

    logger.info(f"Processing {image_stack.shape[0]} slices with {detection_method.value} method")

    for z_idx in range(image_stack.shape[0]):
        # Extract slice and push to GPU
        slice_img = cle.push(image_stack[z_idx].astype(np.float32))

        # Detect cells using specified method
        if detection_method == DetectionMethod.VORONOI_OTSU:
            result = _detect_cells_voronoi_otsu(slice_img, z_idx, parameters)
        elif detection_method == DetectionMethod.THRESHOLD:
            result = _detect_cells_threshold(slice_img, z_idx, parameters)
        else:
            raise ValueError(f"Unknown detection method: {detection_method.value}")

        results.append(result)

        # Create segmentation mask if requested
        if return_segmentation_mask:
            segmentation_mask = _create_labeled_mask(slice_img, result)
            segmentation_masks.append(segmentation_mask)

    # Always return segmentation masks (empty list if not requested)
    return image_stack, results, segmentation_masks


def _detect_cells_voronoi_otsu(
    gpu_image: cle.Array,
    slice_idx: int,
    params: Dict[str, Any]
) -> CellCountResult:
    """
    Detect cells using Voronoi-Otsu labeling (reference workflow).
    
    This follows the exact workflow from the pyclesperanto notebook:
    1. Gaussian blur
    2. Detect spots
    3. Otsu threshold
    4. Masked Voronoi labeling
    """
    # Step 1: Apply Gaussian blur
    blurred = cle.gaussian_blur(gpu_image, sigma_x=params["gaussian_sigma"], sigma_y=params["gaussian_sigma"])
    
    # Step 2: Detect spots (simplified - use fixed radius)
    spots = cle.detect_spots(blurred, radius_x=1, radius_y=1)
    
    # Step 3: Create binary mask using Otsu threshold
    binary = cle.threshold_otsu(blurred)
    
    # Step 4: Apply Voronoi labeling
    voronoi_labels = cle.masked_voronoi_labeling(spots, binary)
    
    # Step 5: Filter by size and get statistics
    voronoi_labels = cle.remove_small_labels(voronoi_labels, minimum_size=params["min_cell_area"])
    voronoi_labels = cle.remove_large_labels(voronoi_labels, maximum_size=params["max_cell_area"])
    
    # Get statistics from pyclesperanto
    stats_dict = cle.statistics_of_labelled_pixels(gpu_image, voronoi_labels)
    
    # Extract results
    if 'label' in stats_dict and len(stats_dict['label']) > 0:
        positions = [(float(x), float(y)) for x, y in zip(stats_dict['centroid_x'], stats_dict['centroid_y'])]
        areas = stats_dict.get('area', [])
        intensities = stats_dict.get('mean_intensity', [])
        confidences = [1.0] * len(positions)  # Simple confidence for Voronoi method
        
        # Convert labeled mask to numpy for binary_mask field
        labeled_mask = cle.pull(voronoi_labels)
    else:
        positions = []
        areas = []
        intensities = []
        confidences = []
        labeled_mask = np.zeros_like(cle.pull(gpu_image), dtype=np.uint16)

    return CellCountResult(
        slice_index=slice_idx,
        method="voronoi_otsu_pyclesperanto",
        cell_count=len(positions),
        cell_positions=positions,
        cell_areas=areas,
        cell_intensities=intensities,
        detection_confidence=confidences,
        parameters_used=params,
        binary_mask=labeled_mask
    )


def _detect_cells_threshold(
    gpu_image: cle.Array,
    slice_idx: int,
    params: Dict[str, Any]
) -> CellCountResult:
    """
    Detect cells using simple thresholding (fallback method).
    """
    # Apply threshold
    max_intensity = cle.maximum_of_all_pixels(gpu_image)
    threshold_val = 0.1 * max_intensity  # Fixed threshold for simplicity
    binary = cle.greater_constant(gpu_image, scalar=threshold_val)
    
    # Connected components labeling
    labels = cle.connected_components_labeling(binary)
    
    # Remove small and large objects
    labels = cle.remove_small_labels(labels, minimum_size=params["min_cell_area"])
    labels = cle.remove_large_labels(labels, maximum_size=params["max_cell_area"])
    
    # Get statistics
    stats_dict = cle.statistics_of_labelled_pixels(gpu_image, labels)
    
    # Extract results
    if 'label' in stats_dict and len(stats_dict['label']) > 0:
        positions = [(float(x), float(y)) for x, y in zip(stats_dict['centroid_x'], stats_dict['centroid_y'])]
        areas = stats_dict.get('area', [])
        intensities = stats_dict.get('mean_intensity', [])
        
        # Use intensity as confidence measure
        max_intensity_cpu = float(max_intensity)
        confidences = [float(intensity / max_intensity_cpu) for intensity in intensities]
        
        # Convert labeled mask to numpy
        labeled_mask = cle.pull(labels)
    else:
        positions = []
        areas = []
        intensities = []
        confidences = []
        labeled_mask = np.zeros_like(cle.pull(gpu_image), dtype=np.uint16)

    return CellCountResult(
        slice_index=slice_idx,
        method="threshold_pyclesperanto",
        cell_count=len(positions),
        cell_positions=positions,
        cell_areas=areas,
        cell_intensities=intensities,
        detection_confidence=confidences,
        parameters_used=params,
        binary_mask=labeled_mask
    )


def _create_labeled_mask(gpu_image: cle.Array, result: CellCountResult) -> np.ndarray:
    """
    Create labeled segmentation mask for ROI extraction.
    
    Returns a labeled mask where each connected region has a unique integer ID.
    """
    # If we already have the binary mask from detection, use it
    if result.binary_mask is not None:
        return result.binary_mask
    
    # Fallback: create mask from positions
    image_shape = cle.pull(gpu_image).shape
    labeled_mask = np.zeros(image_shape, dtype=np.uint16)
    
    # Create simple circular regions around detected positions
    for i, (x, y) in enumerate(result.cell_positions):
        if i < len(result.cell_areas):
            # Use actual cell area if available
            radius = np.sqrt(result.cell_areas[i] / np.pi)
        else:
            # Default radius
            radius = 5.0
        
        # Create circular region
        rr, cc = np.ogrid[:image_shape[0], :image_shape[1]]
        mask = (rr - y)**2 + (cc - x)**2 <= radius**2
        
        # Ensure indices are within bounds
        valid_mask = (rr >= 0) & (rr < image_shape[0]) & (cc >= 0) & (cc < image_shape[1])
        mask = mask & valid_mask
        
        # Assign unique label ID (i+1 to avoid background label 0)
        labeled_mask[mask] = i + 1
    
    return labeled_mask


def count_cells_simple(
    image: np.ndarray,
    gaussian_sigma: float = 1.0,
    min_cell_area: int = 50,
    max_cell_area: int = 5000
) -> Tuple[int, List[Tuple[float, float]]]:
    """
    Quick cell counting with minimal parameters.
    
    Args:
        image: 2D numpy array
        gaussian_sigma: Gaussian blur sigma
        min_cell_area: Minimum cell area (pixels)
        max_cell_area: Maximum cell area (pixels)
        
    Returns:
        cell_count: Number of detected cells
        cell_positions: List of (x, y) centroid positions
    """
    # Convert 2D to 3D for the main function
    image_stack = image[np.newaxis, ...]
    
    # Call main function with Voronoi-Otsu method
    _, results, _ = count_cells_single_channel(
        image_stack,
        detection_method=DetectionMethod.VORONOI_OTSU,
        gaussian_sigma=gaussian_sigma,
        min_cell_area=min_cell_area,
        max_cell_area=max_cell_area,
        return_segmentation_mask=False
    )
    
    # Extract results from first (and only) slice
    result = results[0]
    return result.cell_count, result.cell_positions
