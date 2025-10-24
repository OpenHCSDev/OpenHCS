Microscope Handler Integration
==============================

OpenHCS achieves microscope-agnostic processing through a handler system that abstracts the unique characteristics of different imaging platforms while providing a unified interface to the pipeline system.

Why Microscope Abstraction Matters
-----------------------------------

High-content screening involves diverse microscope platforms (Opera Phenix, ImageXpress, etc.), each with distinct:

- **Directory structures**: Flat vs hierarchical organization
- **Filename patterns**: Different field, well, and channel encoding schemes
- **Metadata formats**: XML, proprietary formats, embedded TIFF tags
- **File organization**: Single files vs multi-file series

Without abstraction, pipelines would need platform-specific logic throughout, making them brittle and hard to maintain. The handler system isolates these differences behind a clean interface.

Architecture: Composition Over Inheritance
-------------------------------------------

The handler system uses composition rather than monolithic inheritance, separating concerns into specialized components:

.. code:: python

   class MicroscopeHandler(ABC):
       @property
       @abstractmethod
       def parser(self) -> FilenameParser:
           """Extracts well, field, channel from filenames."""

       @property
       @abstractmethod
       def metadata_handler(self) -> MetadataHandler:
           """Reads acquisition parameters and plate layout."""

This design enables:

- **Independent evolution**: Parser and metadata logic can change separately
- **Testability**: Each component can be tested in isolation
- **Reusability**: Common parsing logic can be shared across similar formats
- **Extensibility**: New microscope formats require minimal code

Filename Parsers and Metadata Handlers
---------------------------------------

The core of microscope abstraction lies in two critical components that handle format-specific details:

Filename Parser Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Each microscope format has unique filename conventions. Parsers extract semantic information from these patterns using the :doc:`parser_metaprogramming_system` for dynamic interface generation:

.. code-block:: python

   class ImageXpressFilenameParser(FilenameParser):
       """Parser for ImageXpress filename format with centralized component configuration."""

       # FILENAME_COMPONENTS is automatically set to AllComponents + ['extension']
       # by the FilenameParser.__init__() → GenericFilenameParser.__init__() chain

       # Actual regex pattern from codebase - supports placeholders and optional components
       _pattern = re.compile(r'(?:.*?_)?([A-Z]\d+)(?:_s(\d+|\{[^\}]*\}))?(?:_w(\d+|\{[^\}]*\}))?(?:_z(\d+|\{[^\}]*\}))?(\.\w+)?$')

       def parse_filename(self, filename: str) -> Optional[Dict[str, Any]]:
           """Parse ImageXpress filename, handling placeholders like {iii}."""
           basename = Path(str(filename)).name
           match = self._pattern.match(basename)

           if match:
               well, site_str, channel_str, z_str, ext = match.groups()

               # Helper to parse components or return None for placeholders
               parse_comp = lambda s: None if not s or '{' in s else int(s)

               return {
                   'well': well,
                   'site': parse_comp(site_str),
                   'channel': parse_comp(channel_str),
                   'z_index': parse_comp(z_str),
                   'extension': ext if ext else '.tif'
               }
           return None

   # Component-specific methods are automatically generated at runtime:
   # - self.validate_well(), self.validate_site(), etc.
   # - self.extract_well(), self.extract_site(), etc.
   # - All based on AllComponents configuration

   class OperaPhenixFilenameParser(FilenameParser):
       """Parser for Opera Phenix format with centralized component configuration."""

       # FILENAME_COMPONENTS is automatically set to AllComponents + ['extension']
       # by the FilenameParser.__init__() → GenericFilenameParser.__init__() chain

       # Actual regex pattern - much more complex than documentation showed
       _pattern = re.compile(r"r(\d{1,2})c(\d{1,2})f(\d+|\{[^\}]*\})p(\d+|\{[^\}]*\})-ch(\d+|\{[^\}]*\})(?:sk\d+)?(?:fk\d+)?(?:fl\d+)?(\.\w+)$", re.I)

       def parse_filename(self, filename: str) -> Optional[Dict[str, Any]]:
           """Parse Opera Phenix filename with row/col to well conversion."""
           basename = os.path.basename(filename)
           match = self._pattern.match(basename)

           if match:
               row, col, site_str, z_str, channel_str, ext = match.groups()

               # Helper function for placeholder handling
               def parse_comp(s):
                   if not s or '{' in s:
                       return None
                   return int(s)

               # Convert row/col to well format (R01C01)
               well = f"R{int(row):02d}C{int(col):02d}"

               return {
                   'well': well,
                   'site': parse_comp(site_str),
                   'channel': parse_comp(channel_str),
                   'wavelength': parse_comp(channel_str),  # Backward compatibility
                   'z_index': parse_comp(z_str),
                   'extension': ext if ext else '.tif'
               }
           return None

   # Component-specific methods are automatically generated at runtime:
   # - self.validate_well(), self.validate_site(), etc.
   # - self.extract_well(), self.extract_site(), etc.
   # - All based on AllComponents configuration

Metadata Handler Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Metadata handlers extract acquisition parameters and plate layout information:

.. code-block:: python

   class ImageXpressMetadataHandler(MetadataHandler):
       """Handles ImageXpress .HTD and .MES files."""

       def read_plate_metadata(self, plate_dir: Path) -> PlateMetadata:
           htd_file = plate_dir / f"{plate_dir.name}.HTD"
           if not htd_file.exists():
               raise FileNotFoundError(f"HTD file not found: {htd_file}")

           # Parse HTD file for plate layout
           with open(htd_file, 'r') as f:
               htd_data = self._parse_htd_format(f.read())

           return PlateMetadata(
               plate_name=htd_data['PlateName'],
               wells=htd_data['Wells'],
               sites_per_well=htd_data['SitesPerWell'],
               channels=htd_data['Wavelengths'],
               acquisition_date=htd_data['AcquisitionDate']
           )

       def read_acquisition_metadata(self, image_path: Path) -> AcquisitionMetadata:
           """Extract metadata from MES files or TIFF tags."""
           mes_file = image_path.with_suffix('.MES')
           if mes_file.exists():
               return self._parse_mes_file(mes_file)
           else:
               # Fallback to TIFF metadata
               return self._extract_tiff_metadata(image_path)

   class OperaPhenixMetadataHandler(MetadataHandler):
       """Handles Opera Phenix XML metadata files."""

       def read_plate_metadata(self, plate_dir: Path) -> PlateMetadata:
           # Opera Phenix uses XML files for metadata
           xml_files = list(plate_dir.glob("*.xml"))
           if not xml_files:
               raise FileNotFoundError("No XML metadata files found")

           metadata_xml = xml_files[0]  # Usually Index.idx.xml
           tree = ET.parse(metadata_xml)
           root = tree.getroot()

           # Extract plate information from XML structure
           wells = self._extract_wells_from_xml(root)
           channels = self._extract_channels_from_xml(root)

           return PlateMetadata(
               plate_name=root.get('PlateName', 'Unknown'),
               wells=wells,
               channels=channels,
               acquisition_date=self._parse_xml_timestamp(root)
           )

Key Architectural Components
----------------------------

Workspace Preparation
~~~~~~~~~~~~~~~~~~~~~

Each microscope format requires different workspace preparation to normalize directory structures for pipeline processing:

.. code-block:: python

   class ImageXpressHandler(MicroscopeHandler):
       @property
       def root_dir(self) -> str:
           """Root directory where virtual workspace preparation starts.

           Returns "." (plate root) because ImageXpress TimePoint/ZStep folders
           are flattened starting from the plate root, and virtual paths have no prefix.
           """
           return "."

       def _build_virtual_mapping(self, plate_path: Path, filemanager: FileManager) -> Path:
           """Build virtual workspace mapping for nested folder structures."""
           workspace_mapping = {}

           # Apply virtual workspace preparation starting from root_dir
           # For ImageXpress, root_dir is "." (plate root), so we process the plate directly
           start_dir = plate_path if self.root_dir == "." else plate_path / self.root_dir

           # Flatten TimePoint and ZStep folders virtually (no physical file operations)
           self._flatten_timepoints(start_dir, filemanager, workspace_mapping, plate_path)
           self._flatten_zsteps(start_dir, filemanager, workspace_mapping, plate_path)

           # Save virtual workspace mapping to metadata using root_dir as subdirectory key
           writer.merge_subdirectory_metadata(metadata_path, {
               self.root_dir: {
                   "workspace_mapping": workspace_mapping,
                   "available_backends": {"disk": True, "virtual_workspace": True}
               }
           })

           return plate_path

       def _flatten_zsteps(self, directory: Path, filemanager: FileManager):
           """Flatten ZStep_N directories and normalize filenames."""
           # Implementation handles Z-step flattening and filename normalization
           # Uses filemanager for all file operations to respect VFS boundaries

   class OperaPhenixHandler(MicroscopeHandler):
       def _prepare_workspace(self, workspace_path: Path, filemanager: FileManager) -> Path:
           """Apply spatial layout remapping to Opera Phenix filenames."""
           # Check if already processed (temp directory exists)
           temp_dir_name = "__opera_phenix_temp"
           entries = filemanager.list_dir(workspace_path, Backend.DISK.value)

           for entry in entries:
               entry_path = Path(workspace_path) / entry
               if entry_path.is_dir() and entry_path.name == temp_dir_name:
                   return workspace_path  # Already processed

           # Apply spatial remapping using XML metadata
           # Creates temporary directory, processes files, then replaces originals
           # Uses filemanager for all operations to maintain VFS compliance

           return workspace_path

This workspace preparation ensures pipelines always see a consistent flat structure regardless of the original microscope organization.

Unified Image File Discovery
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

All microscope handlers use a unified approach to discover image files by reading from OpenHCS metadata:

.. code-block:: python

   class MetadataHandler(ABC):
       def get_image_files(self, plate_path: Union[str, Path]) -> list[str]:
           """Get list of image files from OpenHCS metadata.

           Default implementation reads from openhcs_metadata.json after virtual workspace preparation.
           Derives image list from workspace_mapping keys if available, otherwise from image_files list.
           """
           # Read from OpenHCS metadata (unified approach for all microscopes)
           from openhcs.microscopes.openhcs import OpenHCSMetadataHandler
           openhcs_handler = OpenHCSMetadataHandler(self.filemanager)

           metadata = openhcs_handler._load_metadata_dict(plate_path)
           subdirs = metadata.get("subdirectories", {})

           # Find main subdirectory (marked with "main": true)
           main_subdir_key = next((key for key, data in subdirs.items() if data.get("main")), None)
           if not main_subdir_key:
               main_subdir_key = next(iter(subdirs.keys()))

           subdir_data = subdirs[main_subdir_key]

           # Prefer workspace_mapping keys (virtual paths) if available
           if workspace_mapping := subdir_data.get("workspace_mapping"):
               return list(workspace_mapping.keys())

           # Otherwise use image_files list
           return subdir_data.get("image_files", [])

**Key Design Points**:

- **Single Source of Truth**: Metadata is authoritative, not filesystem
- **No Filesystem Searching**: Eliminates defensive directory detection logic
- **Unified API**: workspace_mapping keys and image_files use same format (subdirectory/filename)
- **Fail-Loud**: No fallback logic - if metadata doesn't exist, return empty list

**Image Path Format**:

- **ImageXpress**: ``"A01_s001_w1_z001_t001.tif"`` (no prefix, root_dir is ``"."``)
- **OperaPhenix**: ``"Images/remapped_file.tif"`` (includes ``Images/`` prefix, root_dir is ``"Images"``)
- **Zarr**: ``"zarr/A01_s001_w1_z001_t001.tif"`` (includes ``zarr/`` prefix)

Pattern Detection and File Discovery
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Handlers implement automatic pattern detection to identify image files and extract metadata:

.. code-block:: python

   class MicroscopeHandler(ABC):
       def auto_detect_patterns(self, input_dir: Path, well_id: str) -> List[ImagePattern]:
           """Detect all image patterns for a specific well."""
           patterns = []

           # Use parser to identify files belonging to this well
           for image_file in input_dir.glob("*.tif*"):
               try:
                   parsed = self.parser.parse_filename(image_file.name)
                   if parsed.well == well_id:
                       # Group by site and channel to create patterns
                       pattern = ImagePattern(
                           well=parsed.well,
                           site=parsed.site,
                           channel=parsed.channel,
                           file_path=image_file
                       )
                       patterns.append(pattern)
               except ValueError:
                   # Skip files that don't match expected pattern
                   continue

           return self._group_patterns_by_acquisition(patterns)

       def path_list_from_pattern(self, pattern: ImagePattern, input_dir: Path) -> List[Path]:
           """Generate file paths matching a specific pattern."""
           file_paths = []

           # Use parser to construct expected filenames
           for site in pattern.sites:
               for channel in pattern.channels:
                   filename = self.parser.construct_filename(
                       well=pattern.well,
                       site=site,
                       channel=channel
                   )
                   file_path = input_dir / filename
                   if file_path.exists():
                       file_paths.append(file_path)

           return file_paths

This abstraction allows pipelines to discover images without knowing the underlying filename conventions or directory structures.

Parser Metaprogramming System Integration
-----------------------------------------

The microscope handler system integrates with the :doc:`parser_metaprogramming_system` to provide dynamic interface generation for filename parsers.

Dynamic Interface Generation
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Each parser automatically generates component-specific interfaces using the DynamicParserMeta metaclass:

.. code-block:: python

   # Parser defines its component structure
   class CustomFilenameParser(GenericFilenameParser):
       FILENAME_COMPONENTS = ['well', 'site', 'channel', 'timepoint']

       def parse_filename(self, filename: str) -> Optional[Dict[str, Any]]:
           # Parser implementation...
           pass

   # Interface automatically generated with component-specific methods
   CustomInterface = DynamicParserMeta.create_interface(
       CustomFilenameParser,
       interface_name="CustomInterface"
   )

   # Generated interface provides:
   # - get_well_keys()
   # - get_site_keys()
   # - get_channel_keys()
   # - get_timepoint_keys()
   # - construct_filename(well=..., site=..., channel=..., timepoint=...)

**Integration Benefits**:

1. **Component-Agnostic Design**: Parsers work with any component configuration
2. **Dynamic Method Generation**: Interface methods generated based on FILENAME_COMPONENTS
3. **Type Safety**: Generated methods provide proper type hints and validation
4. **Consistent API**: All parsers expose the same interface pattern regardless of components

Generic Parser Base Class
~~~~~~~~~~~~~~~~~~~~~~~~~

The GenericFilenameParser provides the foundation for all microscope-specific parsers:

.. code-block:: python

   class GenericFilenameParser(ABC):
       """Base class for all filename parsers with centralized component configuration."""

       def __init__(self, component_enum: Type[T]):
           """Initialize with component enum - FILENAME_COMPONENTS set automatically."""
           self.component_enum = component_enum
           # FILENAME_COMPONENTS automatically set to all component values + extension
           self.FILENAME_COMPONENTS = [c.value for c in component_enum] + ['extension']
           self.PLACEHOLDER_PATTERN = '{iii}'
           self._generate_dynamic_methods()

       @abstractmethod
       def parse_filename(self, filename: str) -> Optional[Dict[str, Any]]:
           """Parse filename and return component dictionary."""
           pass

       def construct_filename(self, **kwargs) -> str:
           """Construct filename from component values."""
           # Generic implementation using component configuration
           pass

       def get_component_keys(self, component: str, filenames: List[str]) -> List[str]:
           """Extract unique values for a specific component."""
           # Generic implementation that works with any component
           pass

**Generic Design Benefits**:

1. **Extensibility**: New parsers only need to implement parse_filename()
2. **Consistency**: All parsers inherit common functionality
3. **Component Independence**: Base class works with any component structure
4. **Interface Compatibility**: Automatic compatibility with dynamic interface generation

Integration with Pipeline System
---------------------------------

Handler Factory and Selection
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

OpenHCS automatically selects the appropriate handler based on directory structure analysis:

.. code-block:: python

   class MicroscopeHandlerFactory:
       @staticmethod
       def create_handler(input_dir: Path, microscope_type: Optional[str] = None) -> MicroscopeHandler:
           """Create appropriate handler based on directory structure or explicit type."""

           if microscope_type:
               # Explicit selection
               return MicroscopeHandlerFactory._create_explicit_handler(microscope_type)

           # Automatic detection based on directory structure
           if MicroscopeHandlerFactory._is_imagexpress_format(input_dir):
               return ImageXpressHandler()
           elif MicroscopeHandlerFactory._is_opera_phenix_format(input_dir):
               return OperaPhenixHandler()
           elif MicroscopeHandlerFactory._is_openhcs_format(input_dir):
               return OpenHCSHandler()
           else:
               # Fallback to generic handler
               return GenericHandler()

       @staticmethod
       def _is_imagexpress_format(input_dir: Path) -> bool:
           """Detect ImageXpress format by looking for TimePoint directories and .HTD files."""
           has_timepoint_dirs = any(input_dir.glob("TimePoint_*"))
           has_htd_file = any(input_dir.glob("*.HTD"))
           return has_timepoint_dirs or has_htd_file

       @staticmethod
       def _is_opera_phenix_format(input_dir: Path) -> bool:
           """Detect Opera Phenix format by looking for XML metadata and filename patterns."""
           has_xml_metadata = any(input_dir.glob("*.xml"))
           has_opera_filenames = any(input_dir.glob("*r??c??f??p??-ch*.tiff"))
           return has_xml_metadata and has_opera_filenames

       @staticmethod
       def _is_openhcs_format(input_dir: Path) -> bool:
           """Detect OpenHCS format by looking for openhcsmetadata.json."""
           return (input_dir / "openhcsmetadata.json").exists()

FileManager Integration
~~~~~~~~~~~~~~~~~~~~~~~

Handlers work seamlessly with OpenHCS's VFS system, supporting both disk and memory backends:

- **Workspace preparation** operates through FileManager abstraction
- **Pattern detection** works across different storage backends
- **File discovery** respects backend-specific optimizations

Metaclass Registration System
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

OpenHCS uses a metaclass-based registration system that automatically registers new handler classes:

.. code-block:: python

   class MicroscopeHandlerMeta(ABCMeta):
       """Metaclass that automatically registers handler classes."""

       _registry: Dict[str, Type[MicroscopeHandler]] = {}

       def __new__(mcs, name, bases, namespace, **kwargs):
           # Create the class
           cls = super().__new__(mcs, name, bases, namespace, **kwargs)

           # Register non-abstract handlers
           if not getattr(cls, '__abstractmethods__', None):
               # Extract handler type from class name (e.g., "ImageXpress" from "ImageXpressHandler")
               handler_type = name.replace('Handler', '').lower()
               mcs._registry[handler_type] = cls
               print(f"Registered microscope handler: {handler_type} -> {cls}")

           return cls

       @classmethod
       def get_handler_class(mcs, handler_type: str) -> Type[MicroscopeHandler]:
           """Get handler class by type name."""
           return mcs._registry.get(handler_type.lower())

       @classmethod
       def list_available_handlers(mcs) -> List[str]:
           """List all registered handler types."""
           return list(mcs._registry.keys())

   class MicroscopeHandler(ABC, metaclass=MicroscopeHandlerMeta):
       """Base class with automatic registration."""

The metaclass automatically:

- **Registers handlers** upon class definition (no manual registration needed)
- **Validates implementation** of required abstract methods
- **Maintains handler registry** for factory pattern selection
- **Enables automatic detection** based on handler capabilities

This design ensures that new microscope formats are automatically available to the system once their handler class is defined.

OpenHCS Native Handler
~~~~~~~~~~~~~~~~~~~~~~

The OpenHCS handler represents a special case that leverages existing handler components while using OpenHCS-specific metadata:

.. code-block:: python

   class OpenHCSMicroscopeHandler(MicroscopeHandler):
       """Handler for OpenHCS pre-processed format with JSON metadata."""

       def __init__(self, filemanager: FileManager, pattern_format: Optional[str] = None):
           self.filemanager = filemanager
           self.metadata_handler = OpenHCSMetadataHandler(filemanager)
           self._parser: Optional[FilenameParser] = None
           self.plate_folder: Optional[Path] = None
           self.pattern_format = pattern_format

           # Parser is loaded dynamically based on metadata
           super().__init__(parser=None, metadata_handler=self.metadata_handler)

       @property
       def parser(self) -> FilenameParser:
           """Dynamically load parser based on metadata."""
           if self._parser is None:
               parser_name = self.metadata_handler.get_source_filename_parser_name(self.plate_folder)
               available_parsers = _get_available_filename_parsers()
               ParserClass = available_parsers.get(parser_name)

               if not ParserClass:
                   raise ValueError(f"Unknown parser '{parser_name}' in metadata")

               self._parser = ParserClass(pattern_format=self.pattern_format)

           return self._parser

       def _prepare_workspace(self, workspace_path: Path, filemanager: FileManager) -> Path:
           """OpenHCS format is already normalized, no preparation needed."""
           # Ensure plate_folder is set for dynamic parser loading
           if self.plate_folder is None:
               self.plate_folder = Path(workspace_path)
           return workspace_path

   class OpenHCSMetadataHandler(MetadataHandler):
       """Handles OpenHCS JSON metadata format."""

       METADATA_FILENAME = "openhcs_metadata.json"

       def get_source_filename_parser_name(self, plate_path: Path) -> str:
           """Get the original filename parser used for this plate."""
           metadata = self._load_metadata(plate_path)
           return metadata.get("source_filename_parser_name")

       def determine_main_subdirectory(self, plate_path: Path) -> str:
           """Determine which subdirectory contains the main input images."""
           metadata_dict = self._load_metadata_dict(plate_path)

           # Handle subdirectory-keyed format
           if subdirs := metadata_dict.get("subdirectories"):
               # Find subdirectory marked as main, or use first available
               for subdir, subdir_metadata in subdirs.items():
                   if subdir_metadata.get("main", False):
                       return subdir
               return next(iter(subdirs.keys()))  # Fallback to first

           # Legacy format fallback
           return "images"

**Key Architectural Features**:

- **Component reuse**: Leverages existing parser and metadata handler infrastructure
- **JSON-based metadata**: Uses `openhcsmetadata.json` instead of microscope-specific formats
- **Structured metadata**: Standardized JSON schema for plate layout, acquisition parameters, and file organization
- **Self-describing datasets**: Datasets carry their own metadata, making them portable and self-contained

**OpenHCS Metadata Structure**:
The `openhcs_metadata.json` file uses a subdirectory-keyed format to organize metadata by processing step:

.. code-block:: json

   {
     "subdirectories": {
       "images": {
         "microscope_handler_name": "imagexpress",
         "source_filename_parser_name": "ImageXpressFilenameParser",
         "grid_dimensions": [2048, 2048],
         "pixel_size": 0.325,
         "image_files": [
           "images/A01_s1_w1.tif",
           "images/A01_s1_w2.tif",
           "images/A01_s2_w1.tif"
         ],
         "channels": {"1": "DAPI", "2": "GFP"},
         "wells": {"A01": "Control", "A02": "Treatment"},
         "sites": {"1": "Site1", "2": "Site2"},
         "z_indexes": null,
         "available_backends": {"disk": true},
         "main": true
       },
       "processed": {
         "microscope_handler_name": "imagexpress",
         "source_filename_parser_name": "ImageXpressFilenameParser",
         "grid_dimensions": [2048, 2048],
         "pixel_size": 0.325,
         "image_files": [
           "processed/A01_s1_w1_filtered.tif",
           "processed/A01_s1_w2_filtered.tif"
         ],
         "channels": {"1": "DAPI", "2": "GFP"},
         "wells": {"A01": "Control"},
         "sites": {"1": "Site1"},
         "z_indexes": null,
         "available_backends": {"disk": true},
         "main": false
       }
     }
   }

This approach enables OpenHCS to create fully self-describing datasets that can be processed consistently regardless of the original microscope platform.

Extensibility: Adding New Microscope Formats
---------------------------------------------

The handler architecture makes adding support for new microscope formats straightforward:

1. Implement the ABC Contract
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Create a new handler class implementing the required abstract methods:

.. code:: python

   class NewMicroscopeHandler(MicroscopeHandler):
       @property
       def parser(self) -> FilenameParser:
           return NewMicroscopeParser()

       @property
       def metadata_handler(self) -> MetadataHandler:
           return NewMicroscopeMetadataHandler()

2. Define Format-Specific Logic
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

- **Directory structure**: What directories indicate this format?
- **Workspace preparation**: What transformations are needed?
- **Filename patterns**: How are wells, fields, channels encoded?
- **Metadata sources**: XML files, embedded TIFF tags, etc.?

3. Register with Factory
~~~~~~~~~~~~~~~~~~~~~~~~

The handler factory automatically detects and uses new handlers based on directory structure patterns.

Design Benefits
---------------

**Separation of Concerns**
- **Parser**: Handles filename pattern extraction and construction
- **Metadata Handler**: Manages acquisition parameters and plate layout
- **Workspace Preparation**: Normalizes directory structures
- **Handler**: Orchestrates components and provides unified interface

**Testability and Maintainability**
- Each component can be tested independently
- Format-specific logic is isolated and contained
- Changes to one microscope format don't affect others
- Common functionality can be shared across similar formats

**Pipeline Integration**
- Pipelines remain microscope-agnostic
- Automatic format detection reduces user configuration
- Consistent interface regardless of underlying complexity
- Seamless integration with VFS and memory management systems

This architecture enables OpenHCS to process data from any supported microscope platform through a single, consistent pipeline interface, while handling the complex format-specific details transparently.

See Also
--------

- :doc:`parser_metaprogramming_system` - Dynamic interface generation for filename parsers
- :doc:`component_configuration_framework` - Generic component configuration system
- :doc:`component_validation_system` - Component validation and constraint checking
- :doc:`../api/microscope_handlers` - Complete microscope handler API reference
- :doc:`../development/adding-microscope-formats` - Guide for adding new microscope formats

