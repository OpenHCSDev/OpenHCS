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

   class MicroscopeHandler(ABC, metaclass=MicroscopeHandlerMeta):
       """Composed class for handling microscope-specific functionality."""

       def __init__(self, parser: Optional[FilenameParser], metadata_handler: MetadataHandler):
           """Initialize with parser and metadata handler instances."""
           self.parser = parser
           self.metadata_handler = metadata_handler
           self.plate_folder: Optional[Path] = None

       @property
       @abstractmethod
       def root_dir(self) -> str:
           """Root directory where virtual workspace preparation starts."""
           pass

       @property
       @abstractmethod
       def compatible_backends(self) -> List[Backend]:
           """Storage backends this handler is compatible with, in priority order."""
           pass

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
       # Supports: well, site, channel, z_index, timepoint
       _pattern = re.compile(r'(?:.*?_)?([A-Z]\d+)(?:_s(\d+|\{[^\}]*\}))?(?:_w(\d+|\{[^\}]*\}))?(?:_z(\d+|\{[^\}]*\}))?(?:_t(\d+|\{[^\}]*\}))?(?:_.*?)?(\.\w+)?$')

       def parse_filename(self, filename: str) -> Optional[Dict[str, Any]]:
           """Parse ImageXpress filename, handling placeholders like {iii}."""
           basename = Path(str(filename)).name
           match = self._pattern.match(basename)

           if match:
               well, site_str, channel_str, z_str, t_str, ext = match.groups()

               # Helper to parse components or return None for placeholders
               parse_comp = lambda s: None if not s or '{' in s else int(s)

               return {
                   'well': well,
                   'site': parse_comp(site_str),
                   'channel': parse_comp(channel_str),
                   'z_index': parse_comp(z_str),
                   'timepoint': parse_comp(t_str),
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

       # Actual regex pattern - supports row, col, site (field), z_index (plane), channel, timepoint (sk)
       # sk = stack/timepoint, fk = field stack, fl = focal level (optional)
       _pattern = re.compile(r"r(\d{1,2})c(\d{1,2})f(\d+|\{[^\}]*\})p(\d+|\{[^\}]*\})-ch(\d+|\{[^\}]*\})(?:sk(\d+|\{[^\}]*\}))?(?:fk\d+)?(?:fl\d+)?(?:_.*?)?(\.\w+)$", re.I)

       def parse_filename(self, filename: str) -> Optional[Dict[str, Any]]:
           """Parse Opera Phenix filename with row/col to well conversion."""
           basename = os.path.basename(filename)
           match = self._pattern.match(basename)

           if match:
               row, col, site_str, z_str, channel_str, sk_str, ext = match.groups()

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
                   'timepoint': parse_comp(sk_str),  # sk = stack/timepoint
                   'extension': ext if ext else '.tif'
               }
           return None

   # Component-specific methods are automatically generated at runtime:
   # - self.validate_well(), self.validate_site(), etc.
   # - self.extract_well(), self.extract_site(), etc.
   # - All based on AllComponents configuration

Metadata Handler Implementation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Metadata handlers extract acquisition parameters and plate layout information. All handlers implement the :class:`MetadataHandler` ABC:

.. code-block:: python

   class MetadataHandler(ABC):
       """Abstract base class for handling microscope metadata."""

       @abstractmethod
       def find_metadata_file(self, plate_path: Union[str, Path]) -> Path:
           """Find the metadata file for a plate (e.g., .HTD, .xml)."""
           pass

       @abstractmethod
       def get_grid_dimensions(self, plate_path: Union[str, Path]) -> Tuple[int, int]:
           """Get grid dimensions for stitching from metadata."""
           pass

       @abstractmethod
       def get_pixel_size(self, plate_path: Union[str, Path]) -> float:
           """Get the pixel size from metadata in micrometers."""
           pass

       @abstractmethod
       def get_channel_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
           """Get channel key→name mapping from metadata."""
           pass

       @abstractmethod
       def get_well_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
           """Get well key→name mapping from metadata."""
           pass

       @abstractmethod
       def get_site_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
           """Get site key→name mapping from metadata."""
           pass

       @abstractmethod
       def get_z_index_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
           """Get z_index key→name mapping from metadata."""
           pass

       def get_image_files(self, plate_path: Union[str, Path]) -> list[str]:
           """Get list of image files from OpenHCS metadata (default implementation)."""
           pass

       def parse_metadata(self, plate_path: Union[str, Path]) -> Dict[str, Dict[str, Optional[str]]]:
           """Parse all metadata using dynamic method resolution (default implementation)."""
           pass

   class ImageXpressMetadataHandler(MetadataHandler):
       """Handles ImageXpress .HTD and .MES files."""

       def find_metadata_file(self, plate_path: Union[str, Path]) -> Path:
           """Find .HTD file for the plate."""
           plate_path = Path(plate_path)
           htd_file = plate_path / f"{plate_path.name}.HTD"
           if not htd_file.exists():
               raise FileNotFoundError(f"HTD file not found: {htd_file}")
           return htd_file

       def get_pixel_size(self, plate_path: Union[str, Path]) -> float:
           """Extract pixel size from HTD metadata."""
           # Parses HTD file and returns pixel size in micrometers
           pass

       def get_channel_values(self, plate_path: Union[str, Path]) -> Optional[Dict[str, Optional[str]]]:
           """Extract channel names from HTD metadata."""
           # Returns mapping like {"1": "HOECHST 33342", "2": "Calcein"}
           pass

   class OperaPhenixMetadataHandler(MetadataHandler):
       """Handles Opera Phenix XML metadata files."""

       def find_metadata_file(self, plate_path: Union[str, Path]) -> Path:
           """Find XML metadata file (usually Index.idx.xml)."""
           plate_path = Path(plate_path)
           xml_files = list(plate_path.glob("*.xml"))
           if not xml_files:
               raise FileNotFoundError("No XML metadata files found")
           return xml_files[0]

       def get_grid_dimensions(self, plate_path: Union[str, Path]) -> Tuple[int, int]:
           """Extract grid dimensions from XML metadata."""
           # Parses XML and returns (grid_x, grid_y) for stitching
           pass

       def get_pixel_size(self, plate_path: Union[str, Path]) -> float:
           """Extract pixel size from XML metadata."""
           pass

Key Architectural Components
----------------------------

Workspace Preparation
~~~~~~~~~~~~~~~~~~~~~

Each microscope format requires different workspace preparation to normalize directory structures for pipeline processing. The key method is :meth:`_build_virtual_mapping()` which creates a virtual mapping dict (plate-relative paths) and saves it to ``openhcs_metadata.json``:

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
           """Build virtual workspace mapping by flattening nested folder structures.

           Creates plate-relative mappings for TimePoint and Z-step folders.
           No physical file operations - all virtual.
           """
           workspace_mapping = {}

           # Flatten TimePoint and ZStep folders virtually
           self._flatten_timepoints(plate_path, filemanager, workspace_mapping, plate_path)
           self._flatten_zsteps(plate_path, filemanager, workspace_mapping, plate_path)

           # Save to metadata using root_dir as subdirectory key
           metadata_path = plate_path / "openhcs_metadata.json"
           writer = AtomicMetadataWriter()
           writer.merge_subdirectory_metadata(metadata_path, {
               self.root_dir: {
                   "workspace_mapping": workspace_mapping,  # Plate-relative paths
                   "available_backends": {"disk": True, "virtual_workspace": True}
               }
           })

           return plate_path

   class OperaPhenixHandler(MicroscopeHandler):
       @property
       def root_dir(self) -> str:
           """Root directory for Opera Phenix virtual workspace preparation.

           Returns "Images" because field remapping is applied to images
           in the Images/ subdirectory.
           """
           return "Images"

       def _build_virtual_mapping(self, plate_path: Path, filemanager: FileManager) -> Path:
           """Build virtual workspace mapping with field remapping.

           Remaps field IDs to follow top-left to bottom-right pattern
           based on spatial layout from Index.xml.
           """
           image_dir = plate_path / self.root_dir
           workspace_mapping = {}

           # Load field mapping from Index.xml
           xml_parser = OperaPhenixXmlParser(image_dir / "Index.xml")
           field_mapping = xml_parser.get_field_id_mapping(exclude_orphans=True)

           # Build virtual mapping with field remapping
           for real_file in filemanager.list_files(image_dir, Backend.DISK.value):
               parsed = self.parser.parse_filename(real_file)
               if not parsed or parsed['site'] is None:
                   continue

               original_field = parsed['site']
               if original_field in field_mapping:
                   virtual_field = field_mapping[original_field]
                   parsed['site'] = virtual_field
                   virtual_filename = self.parser.construct_filename(**parsed)

                   # Build plate-relative paths
                   virtual_path = (Path(self.root_dir) / virtual_filename).as_posix()
                   real_path = (Path(self.root_dir) / real_file).as_posix()
                   workspace_mapping[virtual_path] = real_path

           # Save to metadata
           metadata_path = plate_path / "openhcs_metadata.json"
           writer = AtomicMetadataWriter()
           writer.merge_subdirectory_metadata(metadata_path, {
               self.root_dir: {
                   "workspace_mapping": workspace_mapping,
                   "available_backends": {"disk": True, "virtual_workspace": True}
               }
           })

           return image_dir

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

Handlers delegate pattern detection to the :class:`PatternDiscoveryEngine`, which uses the parser to identify and group image files:

.. code-block:: python

   class MicroscopeHandler(ABC):
       def auto_detect_patterns(self, folder_path: Union[str, Path], filemanager: FileManager, backend: str,
                               extensions=None, group_by=None, variable_components=None, **kwargs):
           """Detect all image patterns in a folder.

           Args:
               folder_path: Path to folder containing images
               filemanager: FileManager instance for file operations
               backend: Backend to use (e.g., 'disk', 'virtual_workspace')
               extensions: Optional list of file extensions to include
               group_by: GroupBy enum to group patterns by (e.g., GroupBy.CHANNEL)
               variable_components: List of components that can vary (e.g., ['site', 'z_index'])
               **kwargs: Dynamic filter parameters (e.g., well_filter=['A01', 'A02'])

           Returns:
               Dict mapping well IDs to lists of pattern strings
           """
           from openhcs.formats.pattern.pattern_discovery import PatternDiscoveryEngine
           pattern_engine = PatternDiscoveryEngine(self.parser, filemanager)

           return pattern_engine.auto_detect_patterns(
               folder_path,
               extensions=extensions,
               group_by=group_by,
               variable_components=variable_components,
               backend=backend,
               **kwargs
           )

       def path_list_from_pattern(self, directory: Union[str, Path], pattern: str,
                                 filemanager: FileManager, backend: str,
                                 variable_components: Optional[List[str]] = None) -> List[str]:
           """Generate file paths matching a specific pattern.

           Args:
               directory: Directory to search
               pattern: Pattern string with optional {iii} placeholders
               filemanager: FileManager instance for file operations
               backend: Backend to use for file operations
               variable_components: List of components that can vary

           Returns:
               List of matching filenames
           """
           from openhcs.formats.pattern.pattern_discovery import PatternDiscoveryEngine
           pattern_engine = PatternDiscoveryEngine(self.parser, filemanager)

           return pattern_engine.path_list_from_pattern(
               directory, pattern, backend=backend,
               variable_components=variable_components
           )

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

OpenHCS provides a factory function that creates the appropriate handler based on explicit type or automatic detection:

.. code-block:: python

   def create_microscope_handler(microscope_type: str = 'auto',
                                 plate_folder: Optional[Union[str, Path]] = None,
                                 filemanager: Optional[FileManager] = None,
                                 pattern_format: Optional[str] = None,
                                 allowed_auto_types: Optional[List[str]] = None) -> MicroscopeHandler:
       """
       Factory function to create a microscope handler.

       Enforces explicit dependency injection by requiring a FileManager instance.

       Args:
           microscope_type: 'auto', 'imagexpress', 'opera_phenix', 'openhcs'
           plate_folder: Required for 'auto' detection
           filemanager: FileManager instance (required, no fallback)
           pattern_format: Optional pattern format name
           allowed_auto_types: For 'auto' mode, limit detection to these types

       Returns:
           Initialized MicroscopeHandler instance

       Raises:
           ValueError: If filemanager is None or microscope_type cannot be determined
       """
       if filemanager is None:
           raise ValueError("FileManager must be provided to create_microscope_handler")

       # Auto-detect microscope type if needed
       if microscope_type == 'auto':
           if not plate_folder:
               raise ValueError("plate_folder is required for auto-detection")

           microscope_type = _auto_detect_microscope_type(plate_folder, filemanager,
                                                         allowed_types=allowed_auto_types)

       # Get handler class from registry
       handler_class = MICROSCOPE_HANDLERS.get(microscope_type.lower())
       if not handler_class:
           raise ValueError(f"Unsupported microscope type: {microscope_type}")

       # Create and return handler
       return handler_class(filemanager, pattern_format=pattern_format)

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
       _microscope_type = 'new_format'
       _metadata_handler_class = None  # Set after class definition

       def __init__(self, filemanager: FileManager, pattern_format: Optional[str] = None):
           self.parser = NewMicroscopeParser(filemanager, pattern_format)
           self.metadata_handler = NewMicroscopeMetadataHandler(filemanager)
           super().__init__(parser=self.parser, metadata_handler=self.metadata_handler)

       @property
       def root_dir(self) -> str:
           """Root directory for virtual workspace preparation."""
           return "."  # or "Images" or other subdirectory

       @property
       def microscope_type(self) -> str:
           return 'new_format'

       @property
       def metadata_handler_class(self) -> Type[MetadataHandler]:
           return NewMicroscopeMetadataHandler

       @property
       def compatible_backends(self) -> List[Backend]:
           return [Backend.DISK]  # or [Backend.ZARR, Backend.DISK]

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
- :doc:`../api/index` - API reference (autogenerated from source code)

