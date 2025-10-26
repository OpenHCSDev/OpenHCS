"""
Stack utilities module for OpenHCS.

This module provides functions for stacking 2D slices into a 3D array
and unstacking a 3D array into 2D slices, with explicit memory type handling.

This module enforces Clause 278 — Mandatory 3D Output Enforcement:
All functions must return a 3D array of shape [Z, Y, X], even when operating
on a single 2D slice. No logic may check, coerce, or infer rank at unstack time.
"""

import logging
from typing import Any, List

import numpy as np

from openhcs.constants.constants import GPU_MEMORY_TYPES, MemoryType
from openhcs.core.memory.converters import detect_memory_type
from openhcs.core.memory.framework_config import _FRAMEWORK_CONFIG
from openhcs.core.utils import optional_import

logger = logging.getLogger(__name__)

# 🔍 MEMORY CONVERSION LOGGING: Test log to verify logger is working
logger.debug("🔄 STACK_UTILS: Module loaded - memory conversion logging enabled")


def _is_2d(data: Any) -> bool:
    """
    Check if data is a 2D array.

    Args:
        data: Data to check

    Returns:
        True if data is 2D, False otherwise
    """
    # Check if data has a shape attribute
    if not hasattr(data, 'shape'):
        return False

    # Check if shape has length 2
    return len(data.shape) == 2


def _is_3d(data: Any) -> bool:
    """
    Check if data is a 3D array.

    Args:
        data: Data to check

    Returns:
        True if data is 3D, False otherwise
    """
    # Check if data has a shape attribute
    if not hasattr(data, 'shape'):
        return False

    # Check if shape has length 3
    return len(data.shape) == 3


def _enforce_gpu_device_requirements(memory_type: str, gpu_id: int) -> None:
    """
    Enforce GPU device requirements.

    Args:
        memory_type: The memory type
        gpu_id: The GPU device ID

    Raises:
        ValueError: If gpu_id is negative
    """
    # For GPU memory types, validate gpu_id
    if memory_type in {mem_type.value for mem_type in GPU_MEMORY_TYPES}:
        if gpu_id < 0:
            raise ValueError(f"Invalid GPU device ID: {gpu_id}. Must be a non-negative integer.")


# NOTE: Allocation operations now defined in framework_config.py
# This eliminates the scattered _ALLOCATION_OPS dict


def _allocate_stack_array(memory_type: str, stack_shape: tuple, first_slice: Any, gpu_id: int) -> Any:
    """
    Allocate a 3D array for stacking slices using framework config.

    Args:
        memory_type: The target memory type
        stack_shape: The shape of the stack (Z, Y, X)
        first_slice: The first slice (used for dtype inference)
        gpu_id: The GPU device ID

    Returns:
        Pre-allocated array or None for pyclesperanto
    """
    # Convert string to enum
    mem_type = MemoryType(memory_type)
    config = _FRAMEWORK_CONFIG[mem_type]
    allocate_expr = config['allocate_stack']

    # Check if allocation is None (pyclesperanto uses custom stacking)
    if allocate_expr is None:
        return None

    # Import the module
    mod = optional_import(mem_type.value)
    if mod is None:
        raise ValueError(f"{mem_type.value} is required for memory type {memory_type}")

    # Handle dtype conversion if needed
    needs_conversion = config['needs_dtype_conversion']
    if callable(needs_conversion):
        # It's a callable that determines if conversion is needed
        needs_conversion = needs_conversion(first_slice, detect_memory_type)

    if needs_conversion:
        from openhcs.core.memory.converters import convert_memory
        first_slice_source_type = detect_memory_type(first_slice)
        sample_converted = convert_memory(  # noqa: F841 (used in eval)
            data=first_slice,
            source_type=first_slice_source_type,
            target_type=memory_type,
            gpu_id=gpu_id
        )
        dtype = sample_converted.dtype  # noqa: F841 (used in eval)
    else:
        dtype = first_slice.dtype if hasattr(first_slice, 'dtype') else None  # noqa: F841 (used in eval)

    # Set up local variables for eval
    np = optional_import("numpy")  # noqa: F841 (used in eval)
    cupy = mod if mem_type == MemoryType.CUPY else None  # noqa: F841 (used in eval)
    torch = mod if mem_type == MemoryType.TORCH else None  # noqa: F841 (used in eval)
    tf = mod if mem_type == MemoryType.TENSORFLOW else None  # noqa: F841 (used in eval)
    jnp = optional_import("jax.numpy") if mem_type == MemoryType.JAX else None  # noqa: F841 (used in eval)

    # Execute allocation with context if needed
    allocate_context = config.get('allocate_context')
    if allocate_context:
        context = eval(allocate_context)
        with context:
            return eval(allocate_expr)
    else:
        return eval(allocate_expr)


def stack_slices(slices: List[Any], memory_type: str, gpu_id: int) -> Any:
    """
    Stack 2D slices into a 3D array with the specified memory type.

    STRICT VALIDATION: Assumes all slices are 2D arrays.
    No automatic handling of improper inputs.

    Args:
        slices: List of 2D slices (numpy arrays, cupy arrays, torch tensors, etc.)
        memory_type: The memory type to use for the stacked array (REQUIRED)
        gpu_id: The target GPU device ID (REQUIRED)

    Returns:
        A 3D array with the specified memory type of shape [Z, Y, X]

    Raises:
        ValueError: If memory_type is not supported or slices is empty
        ValueError: If gpu_id is negative for GPU memory types
        ValueError: If slices are not 2D arrays
        MemoryConversionError: If conversion fails
    """
    if not slices:
        raise ValueError("Cannot stack empty list of slices")

    # Verify all slices are 2D
    for i, slice_data in enumerate(slices):
        if not _is_2d(slice_data):
            raise ValueError(f"Slice at index {i} is not a 2D array. All slices must be 2D.")

    # Analyze input types for conversion planning (minimal logging)
    input_types = [detect_memory_type(slice_data) for slice_data in slices]
    unique_input_types = set(input_types)
    needs_conversion = memory_type not in unique_input_types or len(unique_input_types) > 1

    # Check GPU requirements
    _enforce_gpu_device_requirements(memory_type, gpu_id)

    # Pre-allocate the final 3D array to avoid intermediate list and final stack operation
    first_slice = slices[0]
    stack_shape = (len(slices), first_slice.shape[0], first_slice.shape[1])

    # Create pre-allocated result array in target memory type using enum dispatch
    result = _allocate_stack_array(memory_type, stack_shape, first_slice, gpu_id)

    # Convert each slice and assign to result array
    conversion_count = 0

    # Check for custom stack handler (pyclesperanto)
    mem_type = MemoryType(memory_type)
    config = _FRAMEWORK_CONFIG[mem_type]
    stack_handler = config.get('stack_handler')

    if stack_handler:
        # Use custom stack handler
        mod = optional_import(mem_type.value)
        result = stack_handler(slices, memory_type, gpu_id, mod)
    else:
        # Standard stacking logic
        for i, slice_data in enumerate(slices):
            source_type = detect_memory_type(slice_data)

            # Track conversions for batch logging
            if source_type != memory_type:
                conversion_count += 1

            # Direct conversion
            if source_type == memory_type:
                converted_data = slice_data
            else:
                from openhcs.core.memory.converters import convert_memory
                converted_data = convert_memory(
                    data=slice_data,
                    source_type=source_type,
                    target_type=memory_type,
                    gpu_id=gpu_id
                )

            # Assign converted slice using framework-specific handler if available
            assign_handler = config.get('assign_slice')
            if assign_handler:
                # Custom assignment (JAX immutability)
                result = assign_handler(result, i, converted_data)
            else:
                # Standard assignment
                result[i] = converted_data

    # 🔍 MEMORY CONVERSION LOGGING: Only log when conversions happen or issues occur
    if conversion_count > 0:
        logger.debug(f"🔄 STACK_SLICES: Converted {conversion_count}/{len(slices)} slices to {memory_type}")
    # Silent success for no-conversion cases to reduce log pollution

    return result


def unstack_slices(array: Any, memory_type: str, gpu_id: int, validate_slices: bool = True) -> List[Any]:
    """
    Split a 3D array into 2D slices along axis 0 and convert to the specified memory type.

    STRICT VALIDATION: Input must be a 3D array. No automatic handling of improper inputs.

    Args:
        array: 3D array to split - MUST BE 3D
        memory_type: The memory type to use for the output slices (REQUIRED)
        gpu_id: The target GPU device ID (REQUIRED)
        validate_slices: If True, validates that each extracted slice is 2D

    Returns:
        List of 2D slices in the specified memory type

    Raises:
        ValueError: If array is not 3D
        ValueError: If validate_slices is True and any extracted slice is not 2D
        ValueError: If gpu_id is negative for GPU memory types
        ValueError: If memory_type is not supported
        MemoryConversionError: If conversion fails
    """
    # Detect input type and check if conversion is needed
    input_type = detect_memory_type(array)
    input_shape = getattr(array, 'shape', 'unknown')
    needs_conversion = input_type != memory_type

    # Verify the array is 3D - fail loudly if not
    if not _is_3d(array):
        raise ValueError(f"Array must be 3D, got shape {getattr(array, 'shape', 'unknown')}")

    # Check GPU requirements
    _enforce_gpu_device_requirements(memory_type, gpu_id)

    # Convert to target memory type
    source_type = input_type  # Reuse already detected type

    # Direct conversion
    if source_type == memory_type:
        # No conversion needed - silent success to reduce log pollution
        pass
    else:
        # Convert and log the conversion
        from openhcs.core.memory.converters import convert_memory
        logger.debug(f"🔄 UNSTACK_SLICES: Converting array - {source_type} → {memory_type}")
        array = convert_memory(
            data=array,
            source_type=source_type,
            target_type=memory_type,
            gpu_id=gpu_id
        )

    # Extract slices along axis 0 (already in the target memory type)
    slices = [array[i] for i in range(array.shape[0])]

    # Validate that all extracted slices are 2D if requested
    if validate_slices:
        for i, slice_data in enumerate(slices):
            if not _is_2d(slice_data):
                raise ValueError(f"Extracted slice at index {i} is not 2D. This indicates a malformed 3D array.")

    # 🔍 MEMORY CONVERSION LOGGING: Only log conversions or issues
    if source_type != memory_type:
        logger.debug(f"🔄 UNSTACK_SLICES: Converted and extracted {len(slices)} slices")
    elif len(slices) == 0:
        logger.warning("🔄 UNSTACK_SLICES: No slices extracted (empty array)")
    # Silent success for no-conversion cases to reduce log pollution

    return slices
