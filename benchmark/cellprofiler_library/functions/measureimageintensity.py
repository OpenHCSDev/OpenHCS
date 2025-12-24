"""
Converted from CellProfiler: MeasureImageIntensity
Original: MeasureImageIntensity.measure

Measures several intensity features across an entire image (excluding masked pixels).
Measurements include: TotalIntensity, MeanIntensity, MedianIntensity, StdIntensity,
MADIntensity, MinIntensity, MaxIntensity, TotalArea, PercentMaximal,
LowerQuartileIntensity, UpperQuartileIntensity, and custom percentiles.
"""

import numpy as np
from typing import Tuple, List, Optional
from dataclasses import dataclass, field
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract
from openhcs.core.pipeline.function_contracts import special_outputs, special_inputs
from openhcs.processing.materialization import csv_materializer


@dataclass
class ImageIntensityMeasurement:
    """Intensity measurements for an image or masked region."""
    slice_index: int
    total_intensity: float
    mean_intensity: float
    median_intensity: float
    std_intensity: float
    mad_intensity: float
    min_intensity: float
    max_intensity: float
    total_area: int
    percent_maximal: float
    lower_quartile_intensity: float
    upper_quartile_intensity: float
    percentile_values: str  # JSON-encoded dict of percentile -> value


def _parse_percentiles(percentiles_str: str) -> List[int]:
    """Parse comma-separated percentile string into sorted, deduplicated list."""
    CellProfiler Parameter Mapping:
    (CellProfiler setting -> Python parameter)
        'Select images to measure' -> (pipeline-handled)
        'Measure the intensity only from areas enclosed by objects?' -> (pipeline-handled)
        'Select input object sets' -> (pipeline-handled)
        'Calculate custom percentiles' -> calculate_percentiles
        'Specify percentiles to measure' -> percentiles

    CellProfiler Parameter Mapping:
    (CellProfiler setting -> Python parameter)
        'Select images to measure' -> (pipeline-handled)
        'Measure the intensity only from areas enclosed by objects?' -> (pipeline-handled)
        'Select input object sets' -> (pipeline-handled)
        'Calculate custom percentiles' -> calculate_percentiles
        'Specify percentiles to measure' -> percentiles

    CellProfiler Parameter Mapping:
    (CellProfiler setting -> Python parameter)
        'Select images to measure' -> (pipeline-handled)
        'Measure the intensity only from areas enclosed by objects?' -> (pipeline-handled)
        'Select input object sets' -> (pipeline-handled)
        'Calculate custom percentiles' -> calculate_percentiles
        'Specify percentiles to measure' -> percentiles

    percentiles = []
    for p in percentiles_str.replace(" ", "").split(","):
        if p == "":
            continue
        if p.isdigit() and 0 <= int(p) <= 100:
            percentiles.append(int(p))
    return sorted(set(percentiles))


@numpy(contract=ProcessingContract.PURE_2D)
@special_outputs(("intensity_measurements", csv_materializer(
    fields=["slice_index", "total_intensity", "mean_intensity", "median_intensity",
            "std_intensity", "mad_intensity", "min_intensity", "max_intensity",
            "total_area", "percent_maximal", "lower_quartile_intensity",
            "upper_quartile_intensity", "percentile_values"],
    analysis_type="image_intensity"
)))
def measure_image_intensity(
    image: np.ndarray,
    calculate_percentiles: bool = False,
    percentiles: str = "10,90",
) -> Tuple[np.ndarray, ImageIntensityMeasurement]:
    """
    Measure intensity features across an entire image.
    
    Args:
        image: Input grayscale image (H, W)
        calculate_percentiles: Whether to calculate custom percentiles
        percentiles: Comma-separated list of percentiles to calculate (0-100)
    
    Returns:
        Tuple of (original image, intensity measurements)
    """
    import json
    
    # Flatten and filter out non-finite values
    pixels = image.flatten()
    pixels = pixels[np.isfinite(pixels)]
    pixel_count = pixels.size
    
    percentile_dict = {}
    
    if pixel_count == 0:
        # Handle empty image case
        pixel_sum = 0.0
        pixel_mean = 0.0
        pixel_std = 0.0
        pixel_mad = 0.0
        pixel_median = 0.0
        pixel_min = 0.0
        pixel_max = 0.0
        pixel_pct_max = 0.0
        pixel_lower_qrt = 0.0
        pixel_upper_qrt = 0.0
        
        if calculate_percentiles:
            parsed_percentiles = _parse_percentiles(percentiles)
            for p in parsed_percentiles:
                percentile_dict[p] = 0.0
    else:
        # Calculate intensity statistics
        pixel_sum = float(np.sum(pixels))
        pixel_mean = pixel_sum / float(pixel_count)
        pixel_std = float(np.std(pixels))
        pixel_median = float(np.median(pixels))
        pixel_mad = float(np.median(np.abs(pixels - pixel_median)))
        pixel_min = float(np.min(pixels))
        pixel_max = float(np.max(pixels))
        pixel_pct_max = 100.0 * float(np.sum(pixels == pixel_max)) / float(pixel_count)
        
        # Calculate quartiles
        quartiles = np.percentile(pixels, [25, 75])
        pixel_lower_qrt = float(quartiles[0])
        pixel_upper_qrt = float(quartiles[1])
        
        # Calculate custom percentiles if requested
        if calculate_percentiles:
            parsed_percentiles = _parse_percentiles(percentiles)
            if parsed_percentiles:
                percentile_results = np.percentile(pixels, parsed_percentiles)
                for p, val in zip(parsed_percentiles, percentile_results):
                    percentile_dict[p] = float(val)
    
    measurements = ImageIntensityMeasurement(
        slice_index=0,
        total_intensity=pixel_sum,
        mean_intensity=pixel_mean,
        median_intensity=pixel_median,
        std_intensity=pixel_std,
        mad_intensity=pixel_mad,
        min_intensity=pixel_min,
        max_intensity=pixel_max,
        total_area=int(pixel_count),
        percent_maximal=pixel_pct_max,
        lower_quartile_intensity=pixel_lower_qrt,
        upper_quartile_intensity=pixel_upper_qrt,
        percentile_values=json.dumps(percentile_dict)
    )
    
    return image, measurements


@numpy(contract=ProcessingContract.PURE_2D)
@special_inputs("labels")
@special_outputs(("intensity_measurements", csv_materializer(
    fields=["slice_index", "total_intensity", "mean_intensity", "median_intensity",
            "std_intensity", "mad_intensity", "min_intensity", "max_intensity",
            "total_area", "percent_maximal", "lower_quartile_intensity",
            "upper_quartile_intensity", "percentile_values"],
    analysis_type="masked_image_intensity"
)))
def measure_image_intensity_masked(
    image: np.ndarray,
    labels: np.ndarray,
    calculate_percentiles: bool = False,
    percentiles: str = "10,90",
) -> Tuple[np.ndarray, ImageIntensityMeasurement]:
    """
    Measure intensity features within labeled object regions.
    
    This measures aggregate intensity across ALL objects in the label image,
    not per-object measurements. For per-object measurements, use
    measure_object_intensity instead.
    
    Args:
        image: Input grayscale image (H, W)
        labels: Label image where non-zero pixels indicate object regions (H, W)
        calculate_percentiles: Whether to calculate custom percentiles
        percentiles: Comma-separated list of percentiles to calculate (0-100)
    
    Returns:
        Tuple of (original image, intensity measurements)
    """
    import json
    
    # Extract pixels within labeled regions
    mask = labels > 0
    pixels = image[mask].flatten()
    pixels = pixels[np.isfinite(pixels)]
    pixel_count = pixels.size
    
    percentile_dict = {}
    
    if pixel_count == 0:
        # Handle empty mask case
        pixel_sum = 0.0
        pixel_mean = 0.0
        pixel_std = 0.0
        pixel_mad = 0.0
        pixel_median = 0.0
        pixel_min = 0.0
        pixel_max = 0.0
        pixel_pct_max = 0.0
        pixel_lower_qrt = 0.0
        pixel_upper_qrt = 0.0
        
        if calculate_percentiles:
            parsed_percentiles = _parse_percentiles(percentiles)
            for p in parsed_percentiles:
                percentile_dict[p] = 0.0
    else:
        # Calculate intensity statistics
        pixel_sum = float(np.sum(pixels))
        pixel_mean = pixel_sum / float(pixel_count)
        pixel_std = float(np.std(pixels))
        pixel_median = float(np.median(pixels))
        pixel_mad = float(np.median(np.abs(pixels - pixel_median)))
        pixel_min = float(np.min(pixels))
        pixel_max = float(np.max(pixels))
        pixel_pct_max = 100.0 * float(np.sum(pixels == pixel_max)) / float(pixel_count)
        
        # Calculate quartiles
        quartiles = np.percentile(pixels, [25, 75])
        pixel_lower_qrt = float(quartiles[0])
        pixel_upper_qrt = float(quartiles[1])
        
        # Calculate custom percentiles if requested
        if calculate_percentiles:
            parsed_percentiles = _parse_percentiles(percentiles)
            if parsed_percentiles:
                percentile_results = np.percentile(pixels, parsed_percentiles)
                for p, val in zip(parsed_percentiles, percentile_results):
                    percentile_dict[p] = float(val)
    
    measurements = ImageIntensityMeasurement(
        slice_index=0,
        total_intensity=pixel_sum,
        mean_intensity=pixel_mean,
        median_intensity=pixel_median,
        std_intensity=pixel_std,
        mad_intensity=pixel_mad,
        min_intensity=pixel_min,
        max_intensity=pixel_max,
        total_area=int(pixel_count),
        percent_maximal=pixel_pct_max,
        lower_quartile_intensity=pixel_lower_qrt,
        upper_quartile_intensity=pixel_upper_qrt,
        percentile_values=json.dumps(percentile_dict)
    )
    
    return image, measurements