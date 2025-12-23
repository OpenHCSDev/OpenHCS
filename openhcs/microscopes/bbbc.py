"""
BBBC (Broad Bioimage Benchmark Collection) microscope implementations.

This module provides handlers for BBBC datasets, which come in different formats:
- BBBC021: ImageXpress format (TIFF with {Well}_{Site}_{Channel}{UUID}.tif pattern)
- BBBC038: Kaggle nuclei format (PNG files organized by ImageId folders)

Each BBBC dataset family gets its own handler class.
"""

import logging
import re
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Union, Type

from openhcs.constants.constants import Backend
from openhcs.io.exceptions import MetadataNotFoundError
from openhcs.io.filemanager import FileManager
from openhcs.microscopes.microscope_base import MicroscopeHandler
from openhcs.microscopes.microscope_interfaces import FilenameParser, MetadataHandler

logger = logging.getLogger(__name__)


# ============================================================================
# BBBC021 Handler (ImageXpress Format)
# ============================================================================

class BBBC021FilenameParser(FilenameParser):
    """
    Parser for BBBC021 dataset filenames.

    Format: {Well}_{Site}_{Channel}{UUID}.tif
    Example: G10_s1_w1BEDC2073-A983-4B98-95E9-84466707A25D.tif

    Components:
    - Well: A01-P24 (plate coordinates)
    - Site: s1, s2, ... (field of view)
    - Channel: w1 (DAPI), w2 (Tubulin), w4 (Actin)
    - UUID: Unique identifier (not used for parsing)
    """

    # Pattern: {Well}_{Site}_{Channel}{UUID}.tif
    # Well: [A-P]\d{2}
    # Site: s\d+
    # Channel: w[124]
    # UUID: [A-F0-9-]+ (hex with dashes)
    _pattern = re.compile(
        r'^(?P<well>[A-P]\d{2})_'
        r's(?P<site>\d+)_'
        r'w(?P<channel>[124])'
        r'(?P<uuid>[A-F0-9-]+)'
        r'\.(?P<extension>tif|TIF)$'
    )

    def __init__(self, filemanager=None, pattern_format=None):
        super().__init__()
        self.filemanager = filemanager
        self.pattern_format = pattern_format

    @classmethod
    def can_parse(cls, filename: str) -> bool:
        """Check if filename matches BBBC021 pattern."""
        basename = Path(str(filename)).name
        return cls._pattern.match(basename) is not None

    def parse_filename(self, filename: str) -> Optional[Dict[str, Any]]:
        """
        Parse BBBC021 filename into components.

        Args:
            filename: Filename to parse

        Returns:
            Dict with keys: well, site, channel, z_index, extension
            (z_index defaults to 1 since BBBC021 has no Z-stacks)
        """
        basename = Path(filename).name
        match = self._pattern.match(basename)

        if not match:
            return None

        return {
            'well': match.group('well'),
            'site': int(match.group('site')),
            'channel': int(match.group('channel')),
            'z_index': 1,  # BBBC021 has no Z-stacks
            'extension': f".{match.group('extension')}",
        }

    def extract_component_coordinates(self, component_value: str) -> Tuple[str, str]:
        """
        Extract row/column from well identifier.

        Args:
            component_value: Well like 'A01', 'B12', etc.

        Returns:
            (row, column) tuple like ('A', '01')
        """
        if not component_value or len(component_value) < 2:
            raise ValueError(f"Invalid well format: {component_value}")

        row = component_value[0]  # A-P
        col = component_value[1:]  # 01-24

        return (row, col)

    def construct_filename(self, extension: str = '.tif', **component_values) -> str:
        """
        Construct BBBC021 filename from components.

        Args:
            well: Well ID (e.g., 'A01')
            site: Site number (int or str)
            channel: Channel number (int or str)
            extension: File extension (default: '.tif')
            **component_values: Other component values (ignored)

        Returns:
            Filename string (without UUID - use existing UUID from original file)
        """
        well = component_values.get('well', 'A01')
        site = component_values.get('site', 1)
        channel = component_values.get('channel', 1)

        # Format: {Well}_s{Site}_w{Channel}.tif
        # Note: We omit UUID in constructed filenames since they're unique identifiers
        # In practice, use original filename or generate minimal pattern
        return f"{well}_s{site}_w{channel}{extension}"


class BBBC021MetadataHandler(MetadataHandler):
    """
    Metadata handler for BBBC021 dataset.

    BBBC021 metadata comes from CSV files:
    - BBBC021_v1_image.csv: Image metadata (plate, well, compound, etc.)
    - BBBC021_v1_compound.csv: Compound structures (SMILES)
    - BBBC021_v1_moa.csv: Mechanism of action labels
    """

    def __init__(self, filemanager: FileManager):
        super().__init__()
        self.filemanager = filemanager

    def find_metadata_file(self, plate_path: Union[str, Path]) -> Path:
        """
        Find BBBC021 metadata CSV file.

        Args:
            plate_path: Path to plate directory

        Returns:
            Path to BBBC021_v1_image.csv

        Raises:
            MetadataNotFoundError: If CSV not found
        """
        plate_path = Path(plate_path)

        # BBBC021 metadata is in the plate root or parent directory
        candidates = [
            plate_path / "BBBC021_v1_image.csv",
            plate_path.parent / "BBBC021_v1_image.csv",
            plate_path / "metadata" / "BBBC021_v1_image.csv",
        ]

        for candidate in candidates:
            if candidate.exists():
                return candidate

        raise MetadataNotFoundError(
            f"BBBC021_v1_image.csv not found in {plate_path} or parent directories. "
            "Download from https://data.broadinstitute.org/bbbc/BBBC021/"
        )

    def get_grid_dimensions(self, plate_path: Union[str, Path]) -> Tuple[int, int]:
        """
        Get grid dimensions for BBBC021.

        BBBC021 uses variable site layouts per well - no fixed grid.
        Return default (1, 1) and let pattern discovery handle actual sites.
        """
        return (1, 1)

    def get_pixel_size(self, plate_path: Union[str, Path]) -> float:
        """
        Get pixel size for BBBC021.

        BBBC021 is 20x magnification ImageXpress, typical pixel size ~0.65 μm.
        Exact value not published - return typical value.
        """
        return 0.65  # μm/pixel (typical for 20x ImageXpress)

    def get_channel_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
        """
        Get channel names for BBBC021.

        Returns:
            Dict mapping channel numbers to names
        """
        return {
            "1": "DAPI",
            "2": "Tubulin",
            "4": "Actin",  # Note: w3 is not used
        }

    def get_well_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
        """
        Get well metadata from BBBC021_v1_image.csv.

        Would need to parse CSV to map wells to compounds.
        Return None for now - wells are just coordinates.
        """
        return None

    def get_site_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
        """Get site metadata - none available for BBBC021."""
        return None

    def get_z_index_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
        """Get z-index metadata - BBBC021 has no Z-stacks."""
        return None


class BBBC021Handler(MicroscopeHandler):
    """
    Microscope handler for BBBC021 dataset (ImageXpress format).

    BBBC021 is Human MCF7 cells from compound profiling experiment.
    Format: ImageXpress microscope, TIFF files with UUID pattern.
    """

    _microscope_type = 'bbbc021'
    _metadata_handler_class = None  # Set after class definition

    def __init__(self, filemanager: FileManager, pattern_format: Optional[str] = None):
        self.parser = BBBC021FilenameParser(filemanager, pattern_format)
        self.metadata_handler = BBBC021MetadataHandler(filemanager)
        super().__init__(parser=self.parser, metadata_handler=self.metadata_handler)

    @property
    def root_dir(self) -> str:
        """
        BBBC021 images are at plate root (no subdirectories).

        Returns "." for plate root.
        """
        return "."

    @property
    def microscope_type(self) -> str:
        return 'bbbc021'

    @property
    def metadata_handler_class(self) -> Type[MetadataHandler]:
        return BBBC021MetadataHandler

    @property
    def compatible_backends(self) -> List[Backend]:
        """BBBC021 uses standard DISK backend."""
        return [Backend.DISK]

    def _build_virtual_mapping(self, plate_path: Path, filemanager: FileManager) -> Path:
        """
        BBBC021 has no complex directory structure - files are already flat.

        Just ensure consistent naming (optional padding, etc).
        No virtual mapping needed.
        """
        logger.info(f"BBBC021 dataset at {plate_path} - no virtual mapping needed (already flat)")

        # Save minimal metadata
        self._save_virtual_workspace_metadata(plate_path, {})

        return plate_path


# ============================================================================
# BBBC038 Handler (Kaggle Nuclei Format - PNG)
# ============================================================================

class BBBC038FilenameParser(FilenameParser):
    """
    Parser for BBBC038 dataset (Kaggle 2018 Data Science Bowl).

    BBBC038 uses folder-based organization, not filename parsing:
    - stage1_train/{ImageId}/images/{ImageId}.png
    - stage1_train/{ImageId}/masks/{MaskId}.png

    ImageId is a hex string, not structured like well/site/channel.
    """

    def __init__(self, filemanager=None, pattern_format=None):
        super().__init__()
        self.filemanager = filemanager
        self.pattern_format = pattern_format

    @classmethod
    def can_parse(cls, filename: str) -> bool:
        """
        BBBC038 uses folder structure, not filename patterns.

        Accept .png files only.
        """
        return Path(filename).suffix.lower() == '.png'

    def parse_filename(self, filename: str) -> Optional[Dict[str, Any]]:
        """
        BBBC038 has no structured filenames - just ImageId.png.

        Return minimal metadata with well=ImageId (parent folder name).
        """
        path = Path(filename)

        # Extract ImageId from path: .../ImageId/images/ImageId.png
        if len(path.parts) >= 2:
            image_id = path.parts[-3] if 'images' in path.parts[-2] else path.stem
        else:
            image_id = path.stem

        return {
            'well': image_id,  # Use ImageId as "well" identifier
            'site': 1,
            'channel': 1,
            'z_index': 1,
            'extension': path.suffix,
        }

    def extract_component_coordinates(self, component_value: str) -> Tuple[str, str]:
        """
        BBBC038 has no plate layout - ImageId is not structured.

        Return ImageId as both row and column.
        """
        return (component_value[:8], component_value[8:] if len(component_value) > 8 else "")

    def construct_filename(self, extension: str = '.png', **component_values) -> str:
        """Construct filename from ImageId."""
        image_id = component_values.get('well', 'unknown')
        return f"{image_id}{extension}"


class BBBC038MetadataHandler(MetadataHandler):
    """
    Metadata handler for BBBC038 (Kaggle nuclei dataset).

    Metadata comes from:
    - metadata.xlsx
    - stage1_train_labels.csv (run-length encoded masks)
    - stage1_solution.csv (evaluation metrics)
    """

    def __init__(self, filemanager: FileManager):
        super().__init__()
        self.filemanager = filemanager

    def find_metadata_file(self, plate_path: Union[str, Path]) -> Path:
        """Find metadata.xlsx or stage1_train_labels.csv."""
        plate_path = Path(plate_path)

        candidates = [
            plate_path / "metadata.xlsx",
            plate_path / "stage1_train_labels.csv",
            plate_path.parent / "metadata.xlsx",
        ]

        for candidate in candidates:
            if candidate.exists():
                return candidate

        raise MetadataNotFoundError(
            f"BBBC038 metadata not found in {plate_path}. "
            "Download from https://data.broadinstitute.org/bbbc/BBBC038/"
        )

    def get_grid_dimensions(self, plate_path: Union[str, Path]) -> Tuple[int, int]:
        """BBBC038 has no grid layout."""
        return (1, 1)

    def get_pixel_size(self, plate_path: Union[str, Path]) -> float:
        """BBBC038 pixel size varies - return default."""
        return 1.0  # No standard pixel size (diverse imaging)

    def get_channel_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
        """BBBC038 is single-channel (nuclei stain)."""
        return {"1": "Nuclei"}

    def get_well_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
        return None

    def get_site_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
        return None

    def get_z_index_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
        return None


class BBBC038Handler(MicroscopeHandler):
    """
    Microscope handler for BBBC038 dataset (Kaggle nuclei, PNG format).

    BBBC038 uses folder-based organization, not standard microscopy layout.
    """

    _microscope_type = 'bbbc038'
    _metadata_handler_class = None

    def __init__(self, filemanager: FileManager, pattern_format: Optional[str] = None):
        self.parser = BBBC038FilenameParser(filemanager, pattern_format)
        self.metadata_handler = BBBC038MetadataHandler(filemanager)
        super().__init__(parser=self.parser, metadata_handler=self.metadata_handler)

    @property
    def root_dir(self) -> str:
        """BBBC038 images are in stage1_train/*/images/ subdirectories."""
        return "stage1_train"

    @property
    def microscope_type(self) -> str:
        return 'bbbc038'

    @property
    def metadata_handler_class(self) -> Type[MetadataHandler]:
        return BBBC038MetadataHandler

    @property
    def compatible_backends(self) -> List[Backend]:
        return [Backend.DISK]

    def _build_virtual_mapping(self, plate_path: Path, filemanager: FileManager) -> Path:
        """
        BBBC038 is organized by ImageId folders.

        No virtual mapping needed - use folder structure as-is.
        """
        logger.info(f"BBBC038 dataset at {plate_path} - folder-based organization")

        self._save_virtual_workspace_metadata(plate_path, {})

        # Return stage1_train directory where images are located
        return plate_path / "stage1_train"


# Register metadata handler classes for auto-discovery
BBBC021Handler._metadata_handler_class = BBBC021MetadataHandler
BBBC038Handler._metadata_handler_class = BBBC038MetadataHandler
