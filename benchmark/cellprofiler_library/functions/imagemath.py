"""
Converted from CellProfiler: ImageMath
Original: ImageMath module

Performs simple mathematical operations on image intensities.
Supports addition, subtraction, multiplication, division, averaging,
min/max, standard deviation, inversion, log transform, and logical operations.
"""

import numpy as np
from typing import Tuple
from enum import Enum
from openhcs.core.memory.decorators import numpy


class MathOperation(Enum):
    ADD = "add"
    SUBTRACT = "subtract"
    DIFFERENCE = "absolute_difference"
    MULTIPLY = "multiply"
    DIVIDE = "divide"
    AVERAGE = "average"
    MINIMUM = "minimum"
    MAXIMUM = "maximum"
    STDEV = "standard_deviation"
    INVERT = "invert"
    COMPLEMENT = "complement"
    LOG_TRANSFORM = "log_transform_base2"
    LOG_TRANSFORM_LEGACY = "log_transform_legacy"
    NONE = "none"
    OR = "or"
    AND = "and"
    NOT = "not"
    EQUALS = "equals"


BINARY_OUTPUT_OPS = [MathOperation.AND, MathOperation.OR, MathOperation.NOT, MathOperation.EQUALS]
SINGLE_IMAGE_OPS = [MathOperation.INVERT, MathOperation.LOG_TRANSFORM, MathOperation.LOG_TRANSFORM_LEGACY, MathOperation.NOT, MathOperation.NONE]


@numpy
def image_math(
    image: np.ndarray,
    operation: MathOperation = MathOperation.ADD,
    factors: Tuple[float, ...] = (1.0, 1.0),
    exponent: float = 1.0,
    after_factor: float = 1.0,
    addend: float = 0.0,
    truncate_low: bool = True,
    truncate_high: bool = True,
    replace_nan: bool = True,
) -> np.ndarray:
    """
    Perform mathematical operations on image intensities.
    
    Args:
        image: Input array of shape (N, H, W) where N images are stacked along dim 0.
               For single-image operations (INVERT, LOG_TRANSFORM, NOT, NONE),
               only the first slice is used.
               For multi-image operations, all N slices are combined.
        operation: The mathematical operation to perform.
        factors: Tuple of multiplication factors for each input image (applied before operation).
        exponent: Raise the result to this power (after operation).
        after_factor: Multiply the result by this value (after operation).
        addend: Add this value to the result (after operation).
        truncate_low: Set values less than 0 to 0.
        truncate_high: Set values greater than 1 to 1.
        replace_nan: Replace NaN values with 0.
    
    Returns:
        Processed image of shape (1, H, W).
    """
    import skimage.util
    
    # Handle input dimensions
    if image.ndim == 2:
        image = image[np.newaxis, :, :]
    
    n_images = image.shape[0]
    
    # Extend factors if needed
    if len(factors) < n_images:
        factors = tuple(factors) + (1.0,) * (n_images - len(factors))
    
    # For single-image operations, only use first image
    if operation in SINGLE_IMAGE_OPS:
        n_images = 1
    
    # Apply factors to each image (except for binary output operations)
    pixel_data = []
    for i in range(n_images):
        pd = image[i].astype(np.float64)
        if operation not in BINARY_OUTPUT_OPS and factors[i] != 1.0:
            pd = pd * factors[i]
        pixel_data.append(pd)
    
    # Helper to check if all inputs are boolean
    def use_logical_operation(data_list):
        return all(pd.dtype == bool for pd in data_list if not np.isscalar(pd))
    
    output_pixel_data = pixel_data[0].copy()
    
    if operation == MathOperation.ADD:
        for pd in pixel_data[1:]:
            output_pixel_data = np.add(output_pixel_data, pd)
    
    elif operation == MathOperation.SUBTRACT:
        if use_logical_operation(pixel_data):
            output_pixel_data = pixel_data[0].copy()
            for pd in pixel_data[1:]:
                output_pixel_data[pd.astype(bool)] = False
        else:
            for pd in pixel_data[1:]:
                output_pixel_data = np.subtract(output_pixel_data, pd)
    
    elif operation == MathOperation.DIFFERENCE:
        if use_logical_operation(pixel_data):
            for pd in pixel_data[1:]:
                output_pixel_data = np.logical_xor(output_pixel_data, pd)
        else:
            for pd in pixel_data[1:]:
                output_pixel_data = np.abs(np.subtract(output_pixel_data, pd))
    
    elif operation == MathOperation.MULTIPLY:
        if use_logical_operation(pixel_data):
            for pd in pixel_data[1:]:
                output_pixel_data = np.logical_and(output_pixel_data, pd)
        else:
            for pd in pixel_data[1:]:
                output_pixel_data = np.multiply(output_pixel_data, pd)
    
    elif operation == MathOperation.DIVIDE:
        for pd in pixel_data[1:]:
            output_pixel_data = np.divide(output_pixel_data, pd)
    
    elif operation == MathOperation.AVERAGE:
        for pd in pixel_data[1:]:
            output_pixel_data = np.add(output_pixel_data, pd)
        if not use_logical_operation(pixel_data):
            total_factor = sum(factors[:n_images])
            output_pixel_data = output_pixel_data / total_factor
    
    elif operation == MathOperation.MINIMUM:
        for pd in pixel_data[1:]:
            output_pixel_data = np.minimum(output_pixel_data, pd)
    
    elif operation == MathOperation.MAXIMUM:
        for pd in pixel_data[1:]:
            output_pixel_data = np.maximum(output_pixel_data, pd)
    
    elif operation == MathOperation.STDEV:
        pixel_array = np.array(pixel_data)
        output_pixel_data = np.std(pixel_array, axis=0)
    
    elif operation == MathOperation.INVERT:
        output_pixel_data = skimage.util.invert(output_pixel_data)
    
    elif operation == MathOperation.NOT:
        output_pixel_data = np.logical_not(output_pixel_data).astype(np.float64)
    
    elif operation == MathOperation.LOG_TRANSFORM:
        output_pixel_data = np.log2(output_pixel_data + 1)
    
    elif operation == MathOperation.LOG_TRANSFORM_LEGACY:
        output_pixel_data = np.log2(output_pixel_data)
    
    elif operation == MathOperation.AND:
        for pd in pixel_data[1:]:
            output_pixel_data = np.logical_and(output_pixel_data, pd)
        output_pixel_data = output_pixel_data.astype(np.float64)
    
    elif operation == MathOperation.OR:
        for pd in pixel_data[1:]:
            output_pixel_data = np.logical_or(output_pixel_data, pd)
        output_pixel_data = output_pixel_data.astype(np.float64)
    
    elif operation == MathOperation.EQUALS:
        output_pixel_data = np.ones(pixel_data[0].shape, dtype=bool)
        comparitor = pixel_data[0]
        for pd in pixel_data[1:]:
            output_pixel_data = output_pixel_data & (comparitor == pd)
        output_pixel_data = output_pixel_data.astype(np.float64)
    
    elif operation == MathOperation.NONE:
        pass  # output_pixel_data is already a copy
    
    # Post-processing (not for binary output operations)
    if operation not in BINARY_OUTPUT_OPS:
        if exponent != 1.0:
            output_pixel_data = output_pixel_data ** exponent
        if after_factor != 1.0:
            output_pixel_data = output_pixel_data * after_factor
        if addend != 0.0:
            output_pixel_data = output_pixel_data + addend
        
        # Truncation
        if truncate_low:
            output_pixel_data[output_pixel_data < 0] = 0
        if truncate_high:
            output_pixel_data[output_pixel_data > 1] = 1
        if replace_nan:
            output_pixel_data[np.isnan(output_pixel_data)] = 0
    
    # Ensure output is (1, H, W)
    if output_pixel_data.ndim == 2:
        output_pixel_data = output_pixel_data[np.newaxis, :, :]
    
    return output_pixel_data.astype(np.float32)