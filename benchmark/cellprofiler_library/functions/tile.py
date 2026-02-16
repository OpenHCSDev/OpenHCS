"""
Converted from CellProfiler: Tile
Original: Tile module for creating montage images
"""

import numpy as np
from typing import Tuple, Optional
from enum import Enum
from openhcs.core.memory.decorators import numpy


class TileMethod(Enum):
    WITHIN_CYCLES = "within_cycles"
    ACROSS_CYCLES = "across_cycles"


class PlaceFirst(Enum):
    TOP_LEFT = "top_left"
    BOTTOM_LEFT = "bottom_left"
    TOP_RIGHT = "top_right"
    BOTTOM_RIGHT = "bottom_right"


class TileStyle(Enum):
    ROW = "row"
    COLUMN = "column"


def _get_tile_ij(
    image_index: int,
    rows: int,
    columns: int,
    tile_style: TileStyle,
    place_first: PlaceFirst,
    meander: bool
) -> Tuple[int, int]:
    """Get the I/J coordinates for an image in the grid.
    
    Args:
        image_index: Index of the image (0-based)
        rows: Number of rows in the grid
        columns: Number of columns in the grid
        tile_style: Whether to tile by row or column first
        place_first: Which corner to start from
        meander: Whether to reverse direction on alternate rows/columns
    
    Returns:
        Tuple of (row_index, column_index)
    """
    if tile_style == TileStyle.ROW:
        tile_i = int(image_index / columns)
        tile_j = image_index % columns
        if meander and tile_i % 2 == 1:
            tile_j = columns - tile_j - 1
    else:
        tile_i = image_index % rows
        tile_j = int(image_index / rows)
        if meander and tile_j % 2 == 1:
            tile_i = rows - tile_i - 1
    
    if place_first in (PlaceFirst.BOTTOM_LEFT, PlaceFirst.BOTTOM_RIGHT):
        tile_i = rows - tile_i - 1
    if place_first in (PlaceFirst.TOP_RIGHT, PlaceFirst.BOTTOM_RIGHT):
        tile_j = columns - tile_j - 1
    
    return tile_i, tile_j


def _get_grid_dimensions(
    image_count: int,
    rows: int,
    columns: int,
    auto_rows: bool,
    auto_columns: bool
) -> Tuple[int, int]:
    """Calculate grid dimensions based on settings.
    
    Args:
        image_count: Number of images to tile
        rows: Specified number of rows (used if not auto)
        columns: Specified number of columns (used if not auto)
        auto_rows: Whether to automatically calculate rows
        auto_columns: Whether to automatically calculate columns
    
    Returns:
        Tuple of (rows, columns)
    """
    if auto_rows:
        if auto_columns:
            # Square root approach
            i = int(np.sqrt(image_count))
            j = int((image_count + i - 1) / i)
            return i, j
        else:
            j = columns
            i = int((image_count + j - 1) / j)
            return i, j
    elif auto_columns:
        i = rows
        j = int((image_count + i - 1) / i)
        return i, j
    else:
        return rows, columns


def _put_tile(
    pixels: np.ndarray,
    output_pixels: np.ndarray,
    image_index: int,
    rows: int,
    columns: int,
    tile_style: TileStyle,
    place_first: PlaceFirst,
    meander: bool
) -> None:
    """Place a single tile into the output image.
    
    Args:
        pixels: Input tile image (H, W) or (H, W, C)
        output_pixels: Output montage image to place tile into
        image_index: Index of this tile
        rows: Number of rows in grid
        columns: Number of columns in grid
        tile_style: Row or column first tiling
        place_first: Starting corner
        meander: Whether to meander
    """
    tile_height = int(output_pixels.shape[0] / rows)
    tile_width = int(output_pixels.shape[1] / columns)
    
    tile_i, tile_j = _get_tile_ij(image_index, rows, columns, tile_style, place_first, meander)
    
    tile_i *= tile_height
    tile_j *= tile_width
    
    img_height = min(tile_height, pixels.shape[0])
    img_width = min(tile_width, pixels.shape[1])
    
    output_pixels[
        tile_i:(tile_i + img_height),
        tile_j:(tile_j + img_width)
    ] = pixels[:img_height, :img_width]


@numpy
def tile(
    image: np.ndarray,
    rows: int = 8,
    columns: int = 12,
    place_first: PlaceFirst = PlaceFirst.TOP_LEFT,
    tile_style: TileStyle = TileStyle.ROW,
    meander: bool = False,
    auto_rows: bool = False,
    auto_columns: bool = False,
) -> np.ndarray:
    """Tile multiple images together to form a montage.
    
    This function takes multiple images stacked along dimension 0 and
    arranges them into a grid layout to create a single montage image.
    
    Args:
        image: Input images stacked along dim 0, shape (N, H, W) where N is
               the number of images to tile together.
        rows: Number of rows in the output grid. Ignored if auto_rows is True.
        columns: Number of columns in the output grid. Ignored if auto_columns is True.
        place_first: Which corner to place the first image.
        tile_style: Whether to fill by row first or column first.
        meander: If True, alternate rows/columns are filled in reverse direction.
        auto_rows: If True, automatically calculate number of rows based on image count.
        auto_columns: If True, automatically calculate number of columns based on image count.
    
    Returns:
        Tiled montage image with shape (1, H_out, W_out) where H_out and W_out
        are determined by the grid dimensions and individual tile sizes.
    
    Note:
        - If both auto_rows and auto_columns are True, creates a roughly square grid.
        - If grid has more slots than images, empty slots are filled with zeros.
        - Images are placed at their original size; if tiles vary in size, the
          largest dimensions are used for the grid cell size.
    """
    # Get number of images from dimension 0
    num_images = image.shape[0]
    
    if num_images == 0:
        raise ValueError("No images provided for tiling")
    
    # Calculate grid dimensions
    grid_rows, grid_cols = _get_grid_dimensions(
        num_images, rows, columns, auto_rows, auto_columns
    )
    
    # Validate grid can hold all images
    if grid_rows * grid_cols < num_images:
        raise ValueError(
            f"Grid size ({grid_rows}x{grid_cols}={grid_rows*grid_cols}) "
            f"is too small for {num_images} images"
        )
    
    # Determine tile dimensions (use max across all images)
    tile_height = image.shape[1]
    tile_width = image.shape[2]
    
    # Create output array
    output_height = tile_height * grid_rows
    output_width = tile_width * grid_cols
    output_pixels = np.zeros((output_height, output_width), dtype=image.dtype)
    
    # Place each tile
    for i in range(num_images):
        _put_tile(
            image[i],
            output_pixels,
            i,
            grid_rows,
            grid_cols,
            tile_style,
            place_first,
            meander
        )
    
    # Return with batch dimension
    return output_pixels[np.newaxis, :, :]