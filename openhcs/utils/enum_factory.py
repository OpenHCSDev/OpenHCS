"""
Dynamic enum creation utilities for OpenHCS.

Provides functions for creating enums dynamically from introspection,
particularly for visualization colormaps and other runtime-discovered options.

Caching:
- Colormap enums are cached to avoid expensive napari/matplotlib imports
- Cache invalidated on OpenHCS version change or after 30 days
- Provides ~20x speedup on subsequent runs
"""
from enum import Enum
from typing import List, Callable, Optional, Dict, Any
import logging
from openhcs.utils.environment import is_headless_mode

logger = logging.getLogger(__name__)


# Lazy import cache manager to avoid circular dependencies
_cache_manager = None


def _get_colormap_cache_manager():
    """Lazy import of cache manager for colormap enums."""
    global _cache_manager
    if _cache_manager is None:
        try:
            from openhcs.core.registry_cache import RegistryCacheManager, CacheConfig

            def get_version():
                try:
                    import openhcs
                    return openhcs.__version__
                except:
                    return "unknown"

            # Serializer for enum members (just store the dict)
            def serialize_enum_members(members: Dict[str, str]) -> Dict[str, Any]:
                return {'members': members}

            # Deserializer for enum members
            def deserialize_enum_members(data: Dict[str, Any]) -> Dict[str, str]:
                return data.get('members', {})

            _cache_manager = RegistryCacheManager(
                cache_name="colormap_enum",
                version_getter=get_version,
                serializer=serialize_enum_members,
                deserializer=deserialize_enum_members,
                config=CacheConfig(
                    max_age_days=30,  # Longer cache for stable enums
                    check_mtimes=False  # No file tracking needed for external libs
                )
            )
        except Exception as e:
            logger.debug(f"Failed to initialize colormap cache manager: {e}")
            _cache_manager = False  # Mark as failed to avoid retrying

    return _cache_manager if _cache_manager is not False else None


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


def create_colormap_enum(lazy: bool = False, enable_cache: bool = True) -> Enum:
    """
    Create a dynamic enum for available colormaps using pure introspection.

    Caching is enabled by default to avoid expensive napari/matplotlib imports
    on subsequent runs (~20x speedup).

    Args:
        lazy: If True, use minimal colormap set without importing napari/matplotlib.
              This avoids blocking imports (napari → dask → GPU libs).
        enable_cache: If True, use persistent cache for enum members (default: True)

    Returns:
        Enum class with colormap names as members

    Raises:
        ValueError: If no colormaps are available or no valid identifiers could be created
    """
    # Try to load from cache first (if not lazy mode)
    cache_manager = _get_colormap_cache_manager() if enable_cache and not lazy else None

    if cache_manager:
        try:
            cached_data = cache_manager.load_cache()
            if cached_data is not None:
                # Cache hit - reconstruct enum from cached members
                members = cached_data
                logger.debug(f"✅ Loaded {len(members)} colormap enum members from cache")

                NapariColormap = Enum('NapariColormap', members)
                NapariColormap.__module__ = 'openhcs.core.config'
                NapariColormap.__qualname__ = 'NapariColormap'
                return NapariColormap
        except Exception as e:
            logger.debug(f"Cache load failed for colormap enum: {e}")

    # Cache miss or disabled - discover colormaps
    if lazy:
        # Use minimal set without importing visualization libraries
        available_cmaps = ['gray', 'viridis', 'magma', 'inferno', 'plasma', 'cividis']
    else:
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

    # Save to cache if enabled
    if cache_manager:
        try:
            cache_manager.save_cache(members)
            logger.debug(f"💾 Saved {len(members)} colormap enum members to cache")
        except Exception as e:
            logger.debug(f"Failed to save colormap enum cache: {e}")

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

