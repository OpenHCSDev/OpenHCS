# openhcs/io/omero_local.py
"""
OMERO Local Storage Backend - Zero-copy server-side OMERO access.

Reads directly from OMERO binary repository, saves results back to OMERO.
"""

import logging
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Union, Tuple
from collections import defaultdict
from datetime import datetime
import fcntl
import threading

import numpy as np

from openhcs.io.base import VirtualBackend
from openhcs.io.backend_registry import StorageBackendMeta
from openhcs.constants.constants import FileFormat

logger = logging.getLogger(__name__)


class OMEROFileFormatRegistry:
    """Registry for OMERO file format handlers (text files saved as FileAnnotations)."""

    def __init__(self):
        self._text_extensions: Set[str] = set()
        self._mimetypes: Dict[str, str] = {}

    def register_text_format(self, extensions: List[str], mimetype: str):
        """Register a text format that should be saved as FileAnnotation."""
        for ext in extensions:
            ext = ext.lower()
            self._text_extensions.add(ext)
            self._mimetypes[ext] = mimetype

    def is_text_format(self, ext: str) -> bool:
        """Check if extension is registered as text format."""
        return ext.lower() in self._text_extensions

    def get_mimetype(self, ext: str) -> str:
        """Get MIME type for extension."""
        return self._mimetypes.get(ext.lower(), 'text/plain')


@dataclass
class ImageStructure:
    """Metadata for a single OMERO image."""
    image_id: int
    sizeZ: int
    sizeC: int
    sizeT: int
    sizeY: int
    sizeX: int


@dataclass
class WellStructure:
    """Metadata for a single well."""
    sites: Dict[int, ImageStructure]  # site_idx → ImageStructure


@dataclass
class PlateStructure:
    """Lightweight metadata for entire plate."""
    plate_id: int
    parser_name: str
    microscope_type: str
    wells: Dict[str, WellStructure]  # well_id → WellStructure

    # Cached for quick access
    all_well_ids: Set[str]
    max_sites: int
    max_z: int
    max_c: int
    max_t: int


class OMEROLocalBackend(VirtualBackend, metaclass=StorageBackendMeta):
    """
    Virtual backend for OMERO server-side execution.

    Generates filenames on-demand from OMERO plate structure.
    No real filesystem operations - all paths are virtual.
    """

    _backend_type = 'omero_local'

    # Class-level lock dictionary for thread-safe well creation
    _well_locks: Dict[str, threading.Lock] = {}
    _well_locks_lock = threading.Lock()  # Lock for the lock dictionary itself

    def __init__(self, omero_data_dir: Optional[Path] = None, omero_conn=None):
        try:
            from omero.gateway import BlitzGateway
            self._BlitzGateway = BlitzGateway
        except ImportError:
            raise ImportError("omero-py required: pip install omero-py")

        if omero_data_dir:
            omero_data_dir = Path(omero_data_dir)
            if not omero_data_dir.exists():
                raise ValueError(f"OMERO data directory not found: {omero_data_dir}")

        self.omero_data_dir = omero_data_dir
        # DO NOT store omero_conn - it contains unpicklable IcePy.Communicator
        # Connection must be passed via kwargs or retrieved from global registry
        self._initial_conn = omero_conn  # Store temporarily for registration

        # Store connection parameters for reconnection in worker processes
        self._conn_params = None
        if omero_conn:
            try:
                self._conn_params = {
                    'host': omero_conn.host,
                    'port': omero_conn.port,
                    'username': omero_conn.getUser().getName(),
                    # Password not available from connection object
                }
            except:
                pass  # Connection params not available

        # Caches for virtual filesystem
        self._plate_metadata: Dict[int, PlateStructure] = {}
        self._parser_cache: Dict[int, Any] = {}  # plate_id → parser instance
        self._plate_name_cache: Dict[str, int] = {}  # plate_name → plate_id

        # File format registry
        self.format_registry = OMEROFileFormatRegistry()
        self._register_formats()

    def _register_formats(self):
        """Register supported text file formats for FileAnnotation storage."""
        # JSON files
        self.format_registry.register_text_format(
            FileFormat.JSON.value,
            'application/json'
        )

        # CSV files
        self.format_registry.register_text_format(
            FileFormat.CSV.value,
            'text/csv'
        )

        # Text files
        self.format_registry.register_text_format(
            FileFormat.TEXT.value,
            'text/plain'
        )

    def __getstate__(self):
        """Exclude unpicklable connection from pickle."""
        state = self.__dict__.copy()
        # Remove unpicklable connection
        state['_initial_conn'] = None
        return state

    def __setstate__(self, state):
        """Restore state after unpickling."""
        self.__dict__.update(state)
        # Connection will be retrieved from global registry in worker process

    def _get_connection(self, **kwargs):
        """
        Get OMERO connection from kwargs, instance, global registry, or create new one.

        This method handles multiple scenarios:
        1. Connection passed via kwargs (highest priority)
        2. Connection stored in this instance
        3. Connection from global registry backend
        4. Create new connection using stored params (worker process)

        This ensures the backend remains picklable for multiprocessing.
        """
        conn = kwargs.get('omero_conn')
        if not conn and self._initial_conn:
            conn = self._initial_conn

        if not conn:
            # Try to get from global registry
            # This handles the case where orchestrator copies the registry
            # but the copy's backend doesn't have the connection
            try:
                from openhcs.io.base import storage_registry
                backend = storage_registry.get('omero_local')
                if backend and backend is not self and hasattr(backend, '_initial_conn') and backend._initial_conn:
                    conn = backend._initial_conn
                    # Cache it in this instance too
                    self._initial_conn = conn
                    logger.debug("Retrieved OMERO connection from global registry backend")
            except Exception as e:
                logger.debug(f"Could not get connection from global registry: {e}")

        if not conn and self._conn_params:
            # Worker process or fresh instance: create new connection using stored params
            logger.info(f"Creating new OMERO connection to {self._conn_params.get('host')}:{self._conn_params.get('port')}")
            try:
                # Get password from environment or use default
                import os
                password = os.getenv('OMERO_PASSWORD', 'openhcs')

                conn = self._BlitzGateway(
                    self._conn_params['username'],
                    password,
                    host=self._conn_params['host'],
                    port=self._conn_params['port']
                )
                if not conn.connect():
                    raise ConnectionError(f"Failed to connect to OMERO at {self._conn_params['host']}:{self._conn_params['port']}")

                # Cache the connection
                self._initial_conn = conn
                logger.info("Successfully connected to OMERO")
            except Exception as e:
                logger.error(f"Failed to create OMERO connection: {e}")
                raise

        if not conn:
            raise ValueError(
                "No OMERO connection available. "
                "Pass omero_conn via kwargs, set in instance, ensure global registry has connection, "
                "or provide connection params for auto-reconnection."
            )
        return conn

    def _ensure_connection(self, **kwargs):
        """Validate OMERO connection is available."""
        self._get_connection(**kwargs)

    def _get_parser_from_plate_metadata(self, plate) -> str:
        """Get parser name from OMERO plate metadata."""
        for ann in plate.listAnnotations():
            if hasattr(ann, 'getNs') and ann.getNs() == "openhcs.metadata":
                metadata = {kv[0]: kv[1] for kv in ann.getValue()}
                parser_name = metadata.get("openhcs.parser")
                if parser_name:
                    return parser_name

        raise ValueError(f"Plate {plate.getId()} missing openhcs.parser metadata")

    def _get_microscope_type_from_plate_metadata(self, plate) -> str:
        """Get microscope type from OMERO plate metadata."""
        for ann in plate.listAnnotations():
            if hasattr(ann, 'getNs') and ann.getNs() == "openhcs.metadata":
                metadata = {kv[0]: kv[1] for kv in ann.getValue()}
                microscope_type = metadata.get("openhcs.microscope_type")
                if microscope_type:
                    return microscope_type

        raise ValueError(f"Plate {plate.getId()} missing openhcs.microscope_type metadata")

    def _load_parser(self, parser_name: str):
        """Dynamically load parser class by name."""
        # Import parser classes
        from openhcs.microscopes.imagexpress import ImageXpressFilenameParser
        from openhcs.microscopes.opera_phenix import OperaPhenixFilenameParser
        from openhcs.microscopes.omero import OMEROFilenameParser

        parser_map = {
            'ImageXpressFilenameParser': ImageXpressFilenameParser,
            'OperaPhenixFilenameParser': OperaPhenixFilenameParser,
            'OMEROFilenameParser': OMEROFilenameParser,
        }

        parser_class = parser_map.get(parser_name)
        if not parser_class:
            raise ValueError(f"Unknown parser: {parser_name}")

        return parser_class()

    def _load_plate_structure(self, plate_id: int, **kwargs) -> None:
        """
        Query OMERO once to build lightweight plate structure.

        Args:
            plate_id: OMERO Plate ID
            **kwargs: Must include omero_conn

        Raises:
            ValueError: If plate not found or missing metadata
        """
        conn = self._get_connection(**kwargs)

        # Query OMERO for plate
        plate = conn.getObject("Plate", plate_id)
        if not plate:
            raise ValueError(f"OMERO Plate not found: {plate_id}")

        # Get parser metadata
        parser_name = self._get_parser_from_plate_metadata(plate)
        microscope_type = self._get_microscope_type_from_plate_metadata(plate)

        # Load parser (cache it)
        if plate_id not in self._parser_cache:
            self._parser_cache[plate_id] = self._load_parser(parser_name)

        # Build structure
        wells = {}
        all_well_ids = set()
        max_sites = 0
        max_z = 0
        max_c = 0
        max_t = 0

        for well in plate.listChildren():
            # Handle both OMERO rtypes and plain Python types
            row = well.row.val if hasattr(well.row, 'val') else well.row
            col = well.column.val if hasattr(well.column, 'val') else well.column
            well_id = f"{chr(ord('A') + row)}{col + 1:02d}"
            all_well_ids.add(well_id)

            sites = {}
            for site_idx_0based, wellsample in enumerate(well.listChildren()):
                image = wellsample.getImage()
                # Use enumeration order as site index (0-based)
                # Convert to 1-based for OpenHCS
                site_idx = site_idx_0based + 1

                image_struct = ImageStructure(
                    image_id=image.getId(),
                    sizeZ=image.getSizeZ(),
                    sizeC=image.getSizeC(),
                    sizeT=image.getSizeT(),
                    sizeY=image.getSizeY(),
                    sizeX=image.getSizeX()
                )
                sites[site_idx] = image_struct

                # Track maximums
                max_sites = max(max_sites, site_idx)
                max_z = max(max_z, image.getSizeZ())
                max_c = max(max_c, image.getSizeC())
                max_t = max(max_t, image.getSizeT())

            wells[well_id] = WellStructure(sites=sites)

        # Store structure
        self._plate_metadata[plate_id] = PlateStructure(
            plate_id=plate_id,
            parser_name=parser_name,
            microscope_type=microscope_type,
            wells=wells,
            all_well_ids=all_well_ids,
            max_sites=max_sites,
            max_z=max_z,
            max_c=max_c,
            max_t=max_t
        )

        logger.info(f"Loaded plate structure for {plate_id}: "
                    f"{len(wells)} wells, {max_sites} sites, "
                    f"{max_z}Z × {max_c}C × {max_t}T")
    
    def load(self, file_path: Union[str, Path], **kwargs) -> np.ndarray:
        """
        Load by parsing filename to extract coordinates, then lookup image.

        Flow: path → extract plate_id → filename → parse → (well, site, z, c, t) → lookup structure → image_id → load plane

        Args:
            file_path: Full path including plate_id (e.g., "/omero/plate_59/A01_s001_w1_z001_t001.tif")
            **kwargs: Additional backend-specific arguments (unused)

        Returns:
            2D numpy array (single z-plane, single channel, single timepoint)
        """
        # Extract plate_id from path using parent directory
        # Path format: /omero/plate_59/A01_s001_w1_z001_t001.tif
        path_obj = Path(file_path)
        plate_dir = path_obj.parent  # /omero/plate_59

        # Extract plate_id from plate directory name
        import re
        plate_dir_name = plate_dir.name  # "plate_59" or "plate_59_outputs"
        match = re.match(r'plate_(\d+)', plate_dir_name)
        if not match:
            raise ValueError(f"Could not extract plate_id from path: {file_path}. Expected /omero/plate_<id>/filename format")

        plate_id = int(match.group(1))

        # Extract filename
        filename = path_obj.name

        # Ensure plate structure is loaded
        if plate_id not in self._plate_metadata:
            self._load_plate_structure(plate_id, **kwargs)

        plate_struct = self._plate_metadata[plate_id]
        parser = self._parser_cache[plate_id]

        # Parse filename to extract components
        parsed = parser.parse_filename(filename)
        if not parsed:
            raise ValueError(f"Cannot parse filename: {filename}")

        well_id = parsed['well']
        site_idx = parsed['site']
        z_idx = parsed['z_index'] - 1  # Convert to 0-based
        c_idx = parsed['channel'] - 1
        t_idx = parsed['timepoint'] - 1

        # Lookup image_id from structure
        if well_id not in plate_struct.wells:
            raise ValueError(f"Well {well_id} not found in plate {plate_id}")

        well_struct = plate_struct.wells[well_id]
        if site_idx not in well_struct.sites:
            raise ValueError(f"Site {site_idx} not found in well {well_id}")

        image_struct = well_struct.sites[site_idx]

        # Validate coordinates
        if z_idx >= image_struct.sizeZ:
            raise ValueError(f"Z-index {z_idx} out of range (max: {image_struct.sizeZ})")
        if c_idx >= image_struct.sizeC:
            raise ValueError(f"Channel {c_idx} out of range (max: {image_struct.sizeC})")
        if t_idx >= image_struct.sizeT:
            raise ValueError(f"Timepoint {t_idx} out of range (max: {image_struct.sizeT})")

        # Load plane from OMERO
        conn = self._get_connection(**kwargs)
        image = conn.getObject("Image", image_struct.image_id)
        if not image:
            raise ValueError(f"OMERO Image not found: {image_struct.image_id}")

        pixels = image.getPrimaryPixels()
        plane = pixels.getPlane(z_idx, c_idx, t_idx)  # Returns 2D numpy array

        logger.debug(f"Loaded {filename} → image {image_struct.image_id}, "
                     f"z={z_idx}, c={c_idx}, t={t_idx}, shape={plane.shape}")

        return plane

    def save(self, data: Any, output_path: Union[str, Path], **kwargs) -> None:
        """
        Save data to OMERO.

        For image data (numpy arrays): Creates a new image in a dataset
        For text data (JSON/CSV): Creates a FileAnnotation attached to plate/well/image
        """
        output_path = Path(output_path)

        # Detect if this is text data (JSON/CSV) or image data using registry
        if isinstance(data, str) and self.format_registry.is_text_format(output_path.suffix):
            # Text file - save as FileAnnotation
            self._save_text_annotation(data, output_path, **kwargs)
        else:
            # Image data - save as OMERO image
            self._save_image(data, output_path, **kwargs)

    def _save_text_annotation(self, text_content: str, output_path: Path, **kwargs) -> None:
        """Save text content as a FileAnnotation attached to OMERO object."""
        conn = self._get_connection(**kwargs)

        # Parse path to determine what to attach to
        # Format: /omero/plate_X/results/A01_cell_counts.json
        path_str = str(output_path)

        # Extract plate ID from path
        import re
        match = re.search(r'/omero/plate_(\d+)', path_str)
        if not match:
            raise ValueError(f"Cannot extract plate ID from path: {path_str}")
        plate_id = int(match.group(1))

        # Create FileAnnotation
        import omero
        from omero.gateway import FileAnnotationWrapper
        from omero.model import OriginalFileI, FileAnnotationI
        import tempfile

        # Write content to temporary file
        with tempfile.NamedTemporaryFile(mode='w', suffix=output_path.suffix, delete=False) as tmp:
            tmp.write(text_content)
            tmp_path = tmp.name

        try:
            # Upload file to OMERO with the actual filename from output_path
            # Get MIME type from registry
            mimetype = self.format_registry.get_mimetype(output_path.suffix)

            file_ann = conn.createFileAnnfromLocalFile(
                tmp_path,
                origFilePathAndName=output_path.name,  # Use actual filename, not temp name
                mimetype=mimetype,
                ns='openhcs.analysis.results',
                desc=f'Analysis results: {output_path.name}'
            )

            # Attach to plate
            plate = conn.getObject("Plate", plate_id)
            if plate:
                plate.linkAnnotation(file_ann)
                logger.info(f"Attached {output_path.name} as FileAnnotation to plate {plate_id}")
            else:
                logger.warning(f"Plate {plate_id} not found, FileAnnotation created but not linked")
        finally:
            # Clean up temp file
            import os
            os.unlink(tmp_path)

    def _save_image(self, data: Any, output_path: Path, **kwargs) -> None:
        """Save image data to OMERO as new image."""
        conn = self._get_connection(**kwargs)

        dataset_id = kwargs.get('dataset_id')
        if not dataset_id:
            raise ValueError("dataset_id required")

        dataset = conn.getObject("Dataset", dataset_id)
        if not dataset:
            raise ValueError(f"Dataset not found: {dataset_id}")

        image_name = output_path.stem

        # Get dimensions
        if data.ndim == 3:
            sizeZ, sizeY, sizeX = data.shape
            sizeC, sizeT = 1, 1
        elif data.ndim == 4:
            sizeZ, sizeC, sizeY, sizeX = data.shape
            sizeT = 1
        else:
            raise ValueError(f"Data must be 3D or 4D, got {data.shape}")

        # Plane generator
        def planes():
            if data.ndim == 3:
                for z in range(sizeZ):
                    yield data[z]
            else:
                for z in range(sizeZ):
                    for c in range(sizeC):
                        yield data[z, c]

        # Create image
        new_image = conn.createImageFromNumpySeq(
            planes(),
            image_name,
            sizeZ=sizeZ,
            sizeC=sizeC,
            sizeT=sizeT,
            description=kwargs.get('description', 'Processed by OpenHCS'),
            dataset=dataset
        )

        logger.info(f"Created OMERO image {new_image.getId()}: {image_name}")

    def exists(self, path: Union[str, Path], **kwargs) -> bool:
        """
        Check if a file/annotation exists in OMERO.

        For text files (JSON/CSV): Check if FileAnnotation exists
        For images: Check if image exists in plate
        """
        path = Path(path)

        # For text files, check FileAnnotations using registry
        if self.format_registry.is_text_format(path.suffix):
            # For now, return False to allow overwrite
            # TODO: Implement proper FileAnnotation lookup
            return False

        # For images, check if image exists
        # TODO: Implement proper image lookup
        return False

    def delete(self, path: Union[str, Path], **kwargs) -> bool:
        """
        Delete a file/annotation from OMERO.

        For text files (JSON/CSV): Delete FileAnnotation
        For images: Delete image (if allowed)
        """
        path = Path(path)

        # For text files, delete FileAnnotation using registry
        if self.format_registry.is_text_format(path.suffix):
            # For now, just log and return success
            # FileAnnotations will be overwritten on save
            logger.debug(f"Delete requested for {path} - will be overwritten on save")
            return True

        # For images, deletion not supported
        logger.warning(f"Delete not supported for OMERO images: {path}")
        return False

    def _parse_omero_path(self, path: Path) -> Tuple[str, int, bool]:
        """Extract (plate_name, base_id, is_derived) from path."""
        parts = path.parts
        if len(parts) < 2 or parts[0] != "/" or parts[1] != "omero":
            raise ValueError(f"Not an OMERO path: {path}")

        base_name = parts[2]  # "plate_55_outputs"
        subdirs = parts[3:-1] if len(parts) > 4 else []

        if not base_name.startswith("plate_"):
            raise ValueError(f"OMERO path must use 'plate_{{id}}' format: {base_name}")

        name_parts = base_name.split("_")
        if len(name_parts) < 2 or not name_parts[1].isdigit():
            raise ValueError(f"Cannot extract plate ID from: {base_name}")

        base_id = int(name_parts[1])
        plate_name = "_".join([base_name] + list(subdirs)) if subdirs else base_name
        is_derived = len(subdirs) > 0 or len(name_parts) > 2

        return plate_name, base_id, is_derived

    def _get_image_id(self, plate_id: int, well_id: str, site: int, **kwargs) -> int:
        """Get OMERO image ID for well and site."""
        if plate_id not in self._plate_metadata:
            self._load_plate_structure(plate_id, **kwargs)

        plate_struct = self._plate_metadata[plate_id]
        if well_id not in plate_struct.wells:
            raise ValueError(f"Well {well_id} not found in plate {plate_id}")
        if site not in plate_struct.wells[well_id].sites:
            raise ValueError(f"Site {site} not found in well {well_id}")

        return plate_struct.wells[well_id].sites[site].image_id

    def _find_plate_by_name(self, plate_name: str, **kwargs) -> Optional[int]:
        """Query OMERO for plate by name."""
        conn = self._get_connection(**kwargs)
        plates = conn.getObjects("Plate", attributes={"name": plate_name})
        for plate in plates:
            return plate.getId()
        return None

    def save_batch(self, data_list: List[Any], identifiers: List[Union[str, Path]], **kwargs) -> None:
        """Save multiple images to OMERO with plate creation and write support."""
        if not identifiers:
            return

        if len(data_list) != len(identifiers):
            raise ValueError(f"Length mismatch: {len(data_list)} vs {len(identifiers)}")

        parser_name = kwargs.get('parser_name')
        if not parser_name:
            raise ValueError("parser_name required for OMERO save_batch")

        microscope_type = kwargs.get('microscope_type')
        if not microscope_type:
            raise ValueError("microscope_type required for OMERO save_batch")

        # Validate all paths are in same plate
        plate_names = set()
        for path in identifiers:
            plate_name, _, _ = self._parse_omero_path(Path(path))
            plate_names.add(plate_name)

        if len(plate_names) > 1:
            raise ValueError(f"Cannot save batch across multiple plates: {plate_names}")

        parser = self._load_parser(parser_name)
        plate_name, base_id, is_derived = self._parse_omero_path(Path(identifiers[0]))

        # Group data by image (well + site)
        images = defaultdict(lambda: {'planes': {}, 'max_z': 0, 'max_c': 0, 'max_t': 0})
        for data, path in zip(data_list, identifiers):
            parsed = parser.parse_filename(Path(path).name)
            well_id, site = parsed['well'], parsed['site']
            z, c, t = parsed.get('z_index', 1) - 1, parsed.get('channel', 1) - 1, parsed.get('timepoint', 1) - 1

            image_key = (well_id, site)
            images[image_key]['planes'][(z, c, t)] = data
            images[image_key]['max_z'] = max(images[image_key]['max_z'], z + 1)
            images[image_key]['max_c'] = max(images[image_key]['max_c'], c + 1)
            images[image_key]['max_t'] = max(images[image_key]['max_t'], t + 1)

        # Get or create plate with locking
        plate_id = self._plate_name_cache.get(plate_name)
        if plate_id is None:
            # Remove parser_name and microscope_type from kwargs to avoid duplicate argument error
            # (they're already passed as positional arguments)
            filtered_kwargs = {k: v for k, v in kwargs.items() if k not in ('parser_name', 'microscope_type')}
            plate_id = self._get_or_create_plate_with_lock(
                plate_name, base_id, parser_name, microscope_type, images, **filtered_kwargs
            )
            self._plate_name_cache[plate_name] = plate_id

        # Write planes
        self._write_planes_to_plate(plate_id, images, **kwargs)

    def _get_or_create_plate_with_lock(self, plate_name, base_id, parser_name, microscope_type, images, **kwargs):
        """Create plate with file locking (like zarr metadata)."""
        lock_dir = Path.home() / '.openhcs' / 'omero_locks'
        lock_dir.mkdir(parents=True, exist_ok=True)
        lock_path = lock_dir / f"{plate_name}.lock"

        try:
            with open(lock_path, 'w') as lock_file:
                fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)

                existing_id = self._find_plate_by_name(plate_name, **kwargs)
                if existing_id:
                    self._load_plate_structure(existing_id, **kwargs)
                    return existing_id

                return self._create_derived_plate(plate_name, base_id, parser_name, microscope_type, images, **kwargs)
        finally:
            if lock_path.exists():
                try:
                    lock_path.unlink()
                except:
                    pass

    def _create_derived_plate(self, plate_name, base_id, parser_name, microscope_type, images, **kwargs):
        """Create plate from grouped image data."""
        conn = self._get_connection(**kwargs)

        # Import OMERO model classes
        import omero.model
        from omero.rtypes import rstring, rint
        from omero.model import NamedValue

        update_service = conn.getUpdateService()

        # Extract structure with MAX dimensions (Napari pattern)
        wells_structure = defaultdict(lambda: {'sites': {}})
        for (well_id, site), img_data in images.items():
            max_height = max_width = 0
            dtype = None
            for plane_data in img_data['planes'].values():
                h, w = plane_data.shape
                max_height, max_width = max(max_height, h), max(max_width, w)
                if dtype is None:
                    dtype = plane_data.dtype

            wells_structure[well_id]['sites'][site] = {
                'sizeZ': img_data['max_z'], 'sizeC': img_data['max_c'], 'sizeT': img_data['max_t'],
                'height': max_height, 'width': max_width, 'dtype': dtype
            }

        # Create plate
        plate = omero.model.PlateI()
        plate.setName(rstring(plate_name))
        plate.setColumnNamingConvention(rstring("number"))
        plate.setRowNamingConvention(rstring("letter"))
        plate = update_service.saveAndReturnObject(plate)
        plate_id = plate.getId().getValue()

        # Attach metadata
        metadata_ann = omero.model.MapAnnotationI()
        metadata_ann.setNs(rstring("openhcs.metadata"))
        metadata_ann.setMapValue([
            NamedValue("openhcs.parser", parser_name),
            NamedValue("openhcs.microscope_type", microscope_type)
        ])
        plate.linkAnnotation(metadata_ann)

        prov_ann = omero.model.MapAnnotationI()
        prov_ann.setNs(rstring("openhcs.provenance"))
        prov_ann.setMapValue([
            NamedValue("source_plate_id", str(base_id)),
            NamedValue("created_by", "OpenHCS"),
            NamedValue("timestamp", datetime.now().isoformat())
        ])
        plate.linkAnnotation(prov_ann)
        update_service.saveObject(plate)

        # Create wells WITHOUT images
        # Images will be created with actual data in _write_planes_to_plate
        # This fixes the bug where placeholder zero images caused first well to be black
        for well_id, well_data in wells_structure.items():
            row, col = ord(well_id[0]) - ord('A'), int(well_id[1:]) - 1
            well = omero.model.WellI()
            well.setPlate(plate)
            well.setRow(rint(row))
            well.setColumn(rint(col))
            update_service.saveAndReturnObject(well)

        # Don't load plate structure yet - it will be loaded after images are written
        # Store parser for later use
        self._parser_cache[plate_id] = self._load_parser(parser_name)
        return plate_id

    def _write_planes_to_plate(self, plate_id, images, **kwargs):
        """Write planes by creating complete images with all data at once."""
        conn = self._get_connection(**kwargs)
        import omero.model
        from omero.rtypes import rint

        for (well_id, site), img_data in images.items():
            # Check if well/site already exists
            try:
                image_id = self._get_image_id(plate_id, well_id, site)
                # Image exists - skip it (already written)
                logger.info(f"Image for {well_id} site {site} already exists in plate {plate_id}, skipping")
                continue
            except ValueError:
                # Image doesn't exist - create it with all planes
                pass

            # Calculate max dimensions for padding
            max_height = max_width = 0
            dtype = None
            for plane_data in img_data['planes'].values():
                h, w = plane_data.shape
                max_height, max_width = max(max_height, h), max(max_width, w)
                if dtype is None:
                    dtype = plane_data.dtype

            sizeZ = img_data['max_z']
            sizeC = img_data['max_c']
            sizeT = img_data['max_t']

            # Generate all planes in ZCT order with padding
            def plane_generator():
                for t in range(sizeT):
                    for c in range(sizeC):
                        for z in range(sizeZ):
                            key = (z, c, t)
                            if key in img_data['planes']:
                                data = img_data['planes'][key]
                                h, w = data.shape

                                # Pad if needed
                                if h < max_height or w < max_width:
                                    padded = np.zeros((max_height, max_width), dtype=dtype)
                                    padded[:h, :w] = data
                                    yield padded
                                else:
                                    yield data
                            else:
                                # Missing plane - yield zeros
                                yield np.zeros((max_height, max_width), dtype=dtype)

            # Create complete image with all planes at once
            image = conn.createImageFromNumpySeq(
                zctPlanes=plane_generator(),
                imageName=f"{well_id}_s{site:03d}",
                sizeZ=sizeZ,
                sizeC=sizeC,
                sizeT=sizeT,
                description=f"OpenHCS processed image for well {well_id}, site {site}"
            )

            # Link image to well
            row, col = ord(well_id[0]) - ord('A'), int(well_id[1:]) - 1

            # Check if well exists, create if not
            query_service = conn.getQueryService()
            params = omero.sys.ParametersI()
            params.addLong("pid", plate_id)
            params.add("row", rint(row))
            params.add("col", rint(col))

            query = "select w from Well as w where w.plate.id = :pid and w.row = :row and w.column = :col"

            # Get or create lock for this specific well
            lock_key = f"plate_{plate_id}_well_{row}_{col}"
            with self._well_locks_lock:
                if lock_key not in self._well_locks:
                    self._well_locks[lock_key] = threading.Lock()
                well_lock = self._well_locks[lock_key]

            # Use threading lock for thread safety + file lock for process safety
            with well_lock:
                lock_dir = Path.home() / '.openhcs' / 'omero_locks'
                lock_dir.mkdir(parents=True, exist_ok=True)
                lock_path = lock_dir / f"{lock_key}.lock"

                try:
                    with open(lock_path, 'w') as lock_file:
                        fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)

                        # Re-check if well exists after acquiring both locks
                        # Use findAllByQuery since findByQuery throws exception on null
                        wells = query_service.findAllByQuery(query, params)
                        well_obj = wells[0] if wells else None

                        if not well_obj:
                            # Create new well
                            update_service = conn.getUpdateService()
                            well = omero.model.WellI()
                            well.setPlate(omero.model.PlateI(plate_id, False))
                            well.setRow(rint(row))
                            well.setColumn(rint(col))
                            well_obj = update_service.saveAndReturnObject(well)
                finally:
                    if lock_path.exists():
                        try:
                            lock_path.unlink()
                        except:
                            pass

            # Link image to well
            # Reload well with wellSamples collection loaded
            well_obj_loaded = conn.getObject("Well", well_obj.getId().getValue())
            # Force load the wellSamples collection by accessing it
            _ = list(well_obj_loaded.listChildren())  # This loads the collection

            ws = omero.model.WellSampleI()
            ws.setImage(omero.model.ImageI(image.getId(), False))
            ws.setWell(well_obj_loaded._obj)
            well_obj_loaded._obj.addWellSample(ws)
            conn.getUpdateService().saveObject(well_obj_loaded._obj)

        # Reload plate structure to include new wells/images
        self._load_plate_structure(plate_id)

    def list_files(self, directory: Union[str, Path], pattern: str = "*",
                   extensions: Set[str] = None, recursive: bool = False, **kwargs) -> List[str]:
        """
        Generate filenames on-demand from plate structure.

        Args:
            directory: Path containing plate ID (e.g., "/17/Images" or "17")
            pattern: File pattern (currently ignored)
            extensions: File extensions (currently ignored)
            recursive: Recursion flag (currently ignored)
            **kwargs: Additional backend-specific arguments (unused)

        Returns:
            List of filenames: ["A01_s001_w1_z001_t001.tif", ...]
        """
        # Extract plate_id from path
        # Path could be: "/omero/plate_55/Images" or "/17/Images" or "17/Images" or just "17"
        path_parts = Path(directory).parts

        # Find the numeric plate_id in the path
        plate_id = None
        for part in path_parts:
            # Handle both "55" and "plate_55" formats
            if part.isdigit():
                plate_id = int(part)
                break
            elif part.startswith("plate_"):
                try:
                    plate_id = int(part.split("_")[1])
                    break
                except (IndexError, ValueError):
                    continue

        if plate_id is None:
            raise ValueError(f"Could not extract numeric plate_id from path: {directory}")

        # Load plate structure if not cached
        if plate_id not in self._plate_metadata:
            self._load_plate_structure(plate_id)

        plate_struct = self._plate_metadata[plate_id]
        parser = self._parser_cache[plate_id]

        # Generate filenames on-the-fly
        filenames = []
        for well_id, well_struct in plate_struct.wells.items():
            for site_idx, image_struct in well_struct.sites.items():
                # Generate filename for each (z, c, t) combination
                for t in range(image_struct.sizeT):
                    for z in range(image_struct.sizeZ):
                        for c in range(image_struct.sizeC):
                            filename = parser.construct_filename(
                                well=well_id,
                                site=site_idx,
                                channel=c + 1,
                                z_index=z + 1,
                                timepoint=t + 1,
                                extension='.tif'
                            )
                            filenames.append(filename)

        logger.debug(f"Generated {len(filenames)} filenames on-demand for plate {plate_id}")
        return filenames

    def exists(self, path: Union[str, Path]) -> bool:
        """
        Check if a virtual OMERO path exists.

        For OMERO virtual backend, paths always "exist" if they're valid OMERO paths.
        This is because OMERO generates filenames on-demand from plate structure.

        Args:
            path: Virtual OMERO path to check

        Returns:
            True if path is a valid OMERO path format, False otherwise
        """
        try:
            # Check if path is valid OMERO format
            path_str = str(path)
            if not path_str.startswith("/omero/"):
                return False

            # Try to parse the path - if it parses, it's valid
            self._parse_omero_path(Path(path))
            return True
        except (ValueError, IndexError):
            return False

    def ensure_directory(self, directory: Union[str, Path]) -> None:
        """
        Ensure directory exists (no-op for OMERO virtual backend).

        OMERO is a virtual filesystem - directories don't exist as real entities.
        Plates are created on-demand during save_batch operations.
        This method exists to satisfy the backend interface but does nothing.

        Args:
            directory: Virtual directory path (ignored)
        """
        # No-op for virtual backend - directories are implicit in OMERO
        pass

    def load_batch(self, file_paths: List[Union[str, Path]], **kwargs) -> List[Any]:
        """Load multiple images from OMERO."""
        return [self.load(fp, **kwargs) for fp in file_paths]
