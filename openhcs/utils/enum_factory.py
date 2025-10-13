"""
Dynamic enum creation utilities for OpenHCS.

Provides functions for creating enums dynamically from introspection,
particularly for visualization colormaps and other runtime-discovered options.
"""
from enum import Enum
from typing import List, Callable, Optional
from openhcs.utils.environment import is_headless_mode


def get_available_colormaps() -> List[str]:
    """
    Get available colormaps using introspection - napari first, then matplotlib.

    In headless/CI contexts, avoid importing viz libs; return minimal stable set.

    Returns:
        List of available colormap names
    """
    if is_headless_mode():
        return ['gray', 'viridis']

    try:
        from napari.utils.colormaps import AVAILABLE_COLORMAPS
        return list(AVAILABLE_COLORMAPS.keys())
    except ImportError:
        pass

    try:
        import matplotlib.pyplot as plt
        return list(plt.colormaps())
    except ImportError:
        pass

    raise ImportError("Neither napari nor matplotlib colormaps are available. Install napari or matplotlib.")


def create_colormap_enum() -> Enum:
    """
    Create a dynamic enum for available colormaps using pure introspection.

    Returns:
        Enum class with colormap names as members

    Raises:
        ValueError: If no colormaps are available or no valid identifiers could be created
    """
    available_cmaps = get_available_colormaps()

    if not available_cmaps:
        raise ValueError("No colormaps available for enum creation")

    members = {}
    for cmap_name in available_cmaps:
        enum_name = cmap_name.replace(' ', '_').replace('-', '_').replace('.', '_').upper()
        if enum_name and enum_name[0].isdigit():
            enum_name = f"CMAP_{enum_name}"
        if enum_name and enum_name.replace('_', '').replace('CMAP', '').isalnum():
            members[enum_name] = cmap_name

    if not members:
        raise ValueError("No valid colormap identifiers could be created")

    NapariColormap = Enum('NapariColormap', members)

    # Set proper module and qualname for pickling support
    NapariColormap.__module__ = 'openhcs.core.config'
    NapariColormap.__qualname__ = 'NapariColormap'

    return NapariColormap


def create_enum_from_source(
    enum_name: str,
    source_func: Callable[[], List[str]],
    name_transform: Optional[Callable[[str], str]] = None
) -> Enum:
    """
    Generic factory for creating enums from introspection source functions.

    Args:
        enum_name: Name for the created enum class
        source_func: Function that returns list of string values for enum members
        name_transform: Optional function to transform value strings to enum member names

    Returns:
        Dynamically created Enum class

    Example:
        >>> def get_luts():
        ...     return ['Grays', 'Fire', 'Ice']
        >>> FijiLUT = create_enum_from_source('FijiLUT', get_luts)
    """
    values = source_func()
    if not values:
        raise ValueError(f"No values available for {enum_name} creation")

    members = {}
    for value in values:
        if name_transform:
            member_name = name_transform(value)
        else:
            member_name = value.replace(' ', '_').replace('-', '_').replace('.', '_').upper()
            if member_name and member_name[0].isdigit():
                member_name = f"VAL_{member_name}"

        if member_name and member_name.replace('_', '').replace('VAL', '').isalnum():
            members[member_name] = value

    if not members:
        raise ValueError(f"No valid identifiers could be created for {enum_name}")

    EnumClass = Enum(enum_name, members)

    # Set proper module and qualname for pickling support
    EnumClass.__module__ = 'openhcs.core.config'
    EnumClass.__qualname__ = enum_name

    return EnumClass

