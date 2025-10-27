"""
Shared slice-by-slice processing logic for all memory types.

This module provides a single implementation of slice-by-slice processing
that works for all memory types, eliminating duplication across dtype wrappers.
"""

from openhcs.core.memory.stack_utils import unstack_slices, stack_slices
from openhcs.core.memory.converters import detect_memory_type


def process_slices(image, func, args, kwargs):
    """
    Process a 3D array slice-by-slice using the provided function.
    
    This function handles:
    - Unstacking 3D arrays into 2D slices
    - Processing each slice independently
    - Handling functions that return tuples (main output + special outputs)
    - Stacking results back into 3D arrays
    - Combining special outputs from all slices
    
    Args:
        image: 3D array to process
        func: Function to apply to each slice
        args: Positional arguments to pass to func
        kwargs: Keyword arguments to pass to func
        
    Returns:
        Processed 3D array, or tuple of (processed_3d_array, special_outputs...)
        if func returns tuples
    """
    # Detect memory type and use proper OpenHCS utilities
    memory_type = detect_memory_type(image)
    gpu_id = 0  # Default GPU ID for slice processing

    # Unstack 3D array into 2D slices
    slices_2d = unstack_slices(image, memory_type, gpu_id)

    # Process each slice and handle special outputs
    main_outputs = []
    special_outputs_list = []

    for slice_2d in slices_2d:
        slice_result = func(slice_2d, *args, **kwargs)

        # Check if result is a tuple (indicating special outputs)
        if isinstance(slice_result, tuple):
            main_outputs.append(slice_result[0])  # First element is main output
            special_outputs_list.append(slice_result[1:])  # Rest are special outputs
        else:
            main_outputs.append(slice_result)  # Single output

    # Stack main outputs back into 3D array
    result = stack_slices(main_outputs, memory_type, gpu_id)

    # If we have special outputs, combine them and return tuple
    if special_outputs_list:
        # Combine special outputs from all slices
        combined_special_outputs = []
        num_special_outputs = len(special_outputs_list[0])

        for i in range(num_special_outputs):
            # Collect the i-th special output from all slices
            special_output_values = [slice_outputs[i] for slice_outputs in special_outputs_list]
            combined_special_outputs.append(special_output_values)

        # Return tuple: (stacked_main_output, combined_special_output1, combined_special_output2, ...)
        return (result, *combined_special_outputs)
    
    return result

