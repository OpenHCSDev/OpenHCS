"""
Global configuration dataclasses for OpenHCS.

This module defines the primary configuration objects used throughout the application,
such as VFSConfig, PathPlanningConfig, and the overarching GlobalPipelineConfig.
Configuration is intended to be immutable and provided as Python objects.
"""

import logging
import os # For a potentially more dynamic default for num_workers
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional, Union, Any, List
from enum import Enum
from abc import ABC, abstractmethod
from openhcs.constants import Microscope
from openhcs.constants.constants import Backend

# Import decorator for automatic decorator creation
from openhcs.config_framework import auto_create_decorator

logger = logging.getLogger(__name__)


class ZarrCompressor(Enum):
    """Available compression algorithms for zarr storage."""
    BLOSC = "blosc"
    ZLIB = "zlib"
    LZ4 = "lz4"
    ZSTD = "zstd"
    NONE = "none"

    def create_compressor(self, compression_level: int, shuffle: bool = True) -> Optional[Any]:
        """Create the actual zarr compressor instance.

        Args:
            compression_level: Compression level (1-22 for ZSTD, 1-9 for others)
            shuffle: Enable byte shuffling for better compression (blosc only)

        Returns:
            Configured zarr compressor instance or None for no compression
        """
        import zarr

        match self:
            case ZarrCompressor.NONE:
                return None
            case ZarrCompressor.BLOSC:
                return zarr.Blosc(cname='lz4', clevel=compression_level, shuffle=shuffle)
            case ZarrCompressor.ZLIB:
                return zarr.Zlib(level=compression_level)
            case ZarrCompressor.LZ4:
                return zarr.LZ4(acceleration=compression_level)
            case ZarrCompressor.ZSTD:
                return zarr.Zstd(level=compression_level)


class ZarrChunkStrategy(Enum):
    """Chunking strategies for zarr arrays."""
    WELL = "well"  # Single chunk per well (optimal for batch I/O)
    FILE = "file"  # One chunk per file (better for random access)


class MaterializationBackend(Enum):
    """Available backends for materialization (persistent storage only)."""
    AUTO = "auto"
    ZARR = "zarr"
    DISK = "disk"
    OMERO_LOCAL = "omero_local"


class WellFilterMode(Enum):
    """Well filtering modes for selective materialization."""
    INCLUDE = "include"  # Materialize only specified wells
    EXCLUDE = "exclude"  # Materialize all wells except specified ones

@auto_create_decorator
@dataclass(frozen=True)
class GlobalPipelineConfig:
    """
    Root configuration object for an OpenHCS pipeline session.
    This object is intended to be instantiated at application startup and treated as immutable.
    """
    num_workers: int = 1
    """Number of worker processes/threads for parallelizable tasks."""

    test_str_field: str = "test"

    materialization_results_path: Path = Path("results")
    """
    Path for materialized analysis results (CSV, JSON files from special outputs).

    This is a pipeline-wide setting that controls where all special output materialization
    functions save their analysis results, regardless of which step produces them.

    Can be relative to plate folder or absolute path.
    Default: "results" creates a results/ folder in the plate directory.
    Examples: "results", "./analysis", "/data/analysis_results", "../shared_results"

    Note: This is separate from per-step image materialization, which is controlled
    by the sub_dir field in each step's step_materialization_config.
    """

    microscope: Microscope = Microscope.AUTO
    """Default microscope type for auto-detection."""

    #use_threading: bool = field(default_factory=lambda: os.getenv('OPENHCS_USE_THREADING', 'false').lower() == 'true')
    use_threading: bool = field(default_factory=lambda: os.getenv('OPENHCS_USE_THREADING', 'false').lower() == 'true')
    """Use ThreadPoolExecutor instead of ProcessPoolExecutor for debugging. Reads from OPENHCS_USE_THREADING environment variable."""

    # Future extension point:
    # logging_config: Optional[Dict[str, Any]] = None # For configuring logging levels, handlers
    # plugin_settings: Dict[str, Any] = field(default_factory=dict) # For plugin-specific settings


# PipelineConfig will be created automatically by the injection system
# (GlobalPipelineConfig → PipelineConfig by removing "Global" prefix)



# Import utilities for dynamic config creation
from openhcs.utils.enum_factory import create_colormap_enum
from openhcs.utils.display_config_factory import create_napari_display_config, create_fiji_display_config

# Create the colormap enum using pure introspection
NapariColormap = create_colormap_enum()


class NapariDimensionMode(Enum):
    """How to handle different dimensions in napari visualization."""
    SLICE = "slice"  # Show as 2D slice (take middle slice)
    STACK = "stack"  # Show as 3D stack/volume


class NapariVariableSizeHandling(Enum):
    """How to handle images with different sizes in the same layer."""
    SEPARATE_LAYERS = "separate_layers"  # Create separate layers per well (preserves exact data)
    PAD_TO_MAX = "pad_to_max"  # Pad smaller images to match largest (enables stacking)


# Create NapariDisplayConfig using factory
from openhcs.constants import VirtualComponents

NapariDisplayConfig = create_napari_display_config(
    colormap_enum=NapariColormap,
    dimension_mode_enum=NapariDimensionMode,
    variable_size_handling_enum=NapariVariableSizeHandling,
    virtual_components=VirtualComponents,
    component_order=[
        'step_name',
        'step_index',
        'source',
        'well',
        'site',
        'channel',
        'z_index',
        'timepoint'
    ],
    virtual_component_defaults={
        'step_name': NapariDimensionMode.SLICE,
        'step_index': NapariDimensionMode.SLICE,
        'source': NapariDimensionMode.SLICE
    }
)

# Apply the global pipeline config decorator with ui_hidden=True
# This config is only inherited by NapariStreamingConfig, so hide it from UI
NapariDisplayConfig = global_pipeline_config(ui_hidden=True)(NapariDisplayConfig)
# Mark the class directly as well for UI layer checks
NapariDisplayConfig._ui_hidden = True


# ============================================================================
# Fiji Display Configuration
# ============================================================================

class FijiLUT(Enum):
    """Fiji/ImageJ LUT options."""
    GRAYS = "Grays"
    FIRE = "Fire"
    ICE = "Ice"
    SPECTRUM = "Spectrum"
    RED = "Red"
    GREEN = "Green"
    BLUE = "Blue"


class FijiDimensionMode(Enum):
    """
    How to map OpenHCS dimensions to ImageJ hyperstack dimensions.

    ImageJ hyperstacks have 3 dimensions: Channels (C), Slices (Z), Frames (T).
    Each OpenHCS component (site, channel, z_index, timepoint) can be mapped to one of these.

    - WINDOW: Create separate windows for each value (like Napari SLICE mode)
    - CHANNEL: Map to ImageJ Channel dimension (C)
    - SLICE: Map to ImageJ Slice dimension (Z)
    - FRAME: Map to ImageJ Frame dimension (T)
    """
    WINDOW = "window"  # Separate windows (like Napari SLICE mode)
    CHANNEL = "channel"  # ImageJ Channel dimension (C)
    SLICE = "slice"  # ImageJ Slice dimension (Z)
    FRAME = "frame"  # ImageJ Frame dimension (T)


# Create FijiDisplayConfig using factory (with component-specific fields like Napari)
# NOTE: step_name and step_index are EXCLUDED from component_order for Fiji
# They are unreliable for ROIs (come from materialization context, not filename)
# Only source and well are used for window grouping
FijiDisplayConfig = create_fiji_display_config(
    lut_enum=FijiLUT,
    dimension_mode_enum=FijiDimensionMode,
    virtual_components=VirtualComponents,
    component_order=[
        'source',
        'well',
        'site',
        'channel',
        'z_index',
        'timepoint'
    ],
    virtual_component_defaults={
        # Only source is WINDOW for ROI->image mapping (well is already WINDOW in component_defaults)
        'source': FijiDimensionMode.WINDOW
    }
)

# Apply the global pipeline config decorator with ui_hidden=True
# This config is only inherited by FijiStreamingConfig, so hide it from UI
FijiDisplayConfig = global_pipeline_config(ui_hidden=True)(FijiDisplayConfig)
# Mark the class directly as well for UI layer checks
FijiDisplayConfig._ui_hidden = True


@global_pipeline_config
@dataclass(frozen=True)
class WellFilterConfig:
    """Base configuration for well filtering functionality."""
    well_filter: Optional[Union[List[str], str, int]] = None
    """Well filter specification: list of wells, pattern string, or max count integer. None means all wells."""

    well_filter_mode: WellFilterMode = WellFilterMode.INCLUDE
    """Whether well_filter is an include list or exclude list."""


@global_pipeline_config
@dataclass(frozen=True)
class ZarrConfig:
    """Configuration for Zarr storage backend.

    OME-ZARR metadata and plate metadata are always enabled for HCS compliance.
    Shuffle filter is always enabled for Blosc compressor (ignored for others).
    """
    compressor: ZarrCompressor = ZarrCompressor.ZLIB
    """Compression algorithm to use."""

    compression_level: int = 3
    """Compression level (1-9 for LZ4, higher = more compression)."""

    chunk_strategy: ZarrChunkStrategy = ZarrChunkStrategy.WELL
    """Chunking strategy: WELL (single chunk per well) or FILE (one chunk per file)."""


@global_pipeline_config
@dataclass(frozen=True)
class VFSConfig:
    """Configuration for Virtual File System (VFS) related operations."""
    read_backend: Backend = Backend.AUTO
    """Backend for reading input data. AUTO uses metadata-based detection for OpenHCS plates."""

    intermediate_backend: Backend = Backend.MEMORY
    """Backend for storing intermediate step results that are not explicitly materialized."""

    materialization_backend: MaterializationBackend = MaterializationBackend.DISK
    """Backend for explicitly materialized outputs (e.g., final results, user-requested saves)."""


@global_pipeline_config
@dataclass(frozen=True)
class AnalysisConsolidationConfig:
    """Configuration for automatic analysis results consolidation."""
    enabled: bool = True
    """Whether to automatically run analysis consolidation after pipeline completion."""

    metaxpress_style: bool = True
    """Whether to generate MetaXpress-compatible output format with headers."""

    well_pattern: str = r"([A-Z]\d{2})"
    """Regex pattern for extracting well IDs from filenames."""

    file_extensions: tuple[str, ...] = (".csv",)
    """File extensions to include in consolidation."""

    exclude_patterns: tuple[str, ...] = (r".*consolidated.*", r".*metaxpress.*", r".*summary.*")
    """Filename patterns to exclude from consolidation."""

    output_filename: str = "metaxpress_style_summary.csv"
    """Name of the consolidated output file."""


@global_pipeline_config
@dataclass(frozen=True)
class PlateMetadataConfig:
    """Configuration for plate metadata in MetaXpress-style output."""
    barcode: Optional[str] = None
    """Plate barcode. If None, will be auto-generated from plate name."""

    plate_name: Optional[str] = None
    """Plate name. If None, will be derived from plate path."""

    plate_id: Optional[str] = None
    """Plate ID. If None, will be auto-generated."""

    description: Optional[str] = None
    """Experiment description. If None, will be auto-generated."""

    acquisition_user: str = "OpenHCS"
    """User who acquired the data."""

    z_step: str = "1"
    """Z-step information for MetaXpress compatibility."""


@global_pipeline_config
@dataclass(frozen=True)
class ExperimentalAnalysisConfig:
    """Configuration for experimental analysis system."""
    enabled: bool = True
    """Whether experimental analysis is enabled."""

    config_file_name: str = "config.xlsx"
    """Name of the experimental configuration Excel file."""

    design_sheet_name: str = "drug_curve_map"
    """Name of the sheet containing experimental design."""

    plate_groups_sheet_name: str = "plate_groups"
    """Name of the sheet containing plate group mappings."""

    normalization_method: str = "fold_change"
    """Normalization method: fold_change, z_score, percent_control."""

    export_raw_results: bool = True
    """Whether to export raw (non-normalized) results."""

    export_heatmaps: bool = True
    """Whether to generate heatmap visualizations."""

    auto_detect_format: bool = True
    """Whether to automatically detect microscope format."""

    default_format: Optional[str] = None
    """Default format to use if auto-detection fails."""

    enable_wells_exclusion: bool = True
    """Whether to support wells exclusion from analysis (via 'Exclude Wells' row in config)."""

    metaxpress_summary_enabled: bool = True
    """Whether to generate MetaXpress-style summary output by default."""


@global_pipeline_config
@dataclass(frozen=True)
class PathPlanningConfig(WellFilterConfig):
    """
    Configuration for pipeline path planning and directory structure.

    This class handles path construction concerns including plate root directories,
    output directory suffixes, and subdirectory organization. It does not handle
    analysis results location, which is controlled at the pipeline level.

    Inherits well filtering functionality from WellFilterConfig.
    """
    output_dir_suffix: str = "_openhcs"
    """Default suffix for general step output directories."""

    global_output_folder: Optional[Path] = None
    """
    Optional global output folder where all plate workspaces and outputs will be created.
    If specified, plate workspaces will be created as {global_output_folder}/{plate_name}_workspace/
    and outputs as {global_output_folder}/{plate_name}_workspace_outputs/.
    If None, uses the current behavior (workspace and outputs in same directory as plate).
    Example: "/data/results" or "/mnt/hcs_output"
    """

    sub_dir: str = "images"
    """
    Subdirectory within plate folder for storing processed data.
    Examples: "images", "processed", "data/images"
    """

@global_pipeline_config
@dataclass(frozen=True)
class StepWellFilterConfig(WellFilterConfig):
    """Well filter configuration specialized for step-level configs with different defaults."""
    # Override defaults for step-level configurations
    #well_filter: Optional[Union[List[str], str, int]] = 1
    pass

@global_pipeline_config
@dataclass(frozen=True)
class StepMaterializationConfig(StepWellFilterConfig, PathPlanningConfig):
    """
    Configuration for per-step materialization - configurable in UI.

    This dataclass appears in the UI like any other configuration, allowing users
    to set pipeline-level defaults for step materialization behavior. All step
    materialization instances will inherit these defaults unless explicitly overridden.

    Uses multiple inheritance from PathPlanningConfig and StepWellFilterConfig.
    """

    #Override sub_dir for materialization-specific default
    sub_dir: str = "checkpoints"
    """Subdirectory for materialized outputs (different from global 'images')."""


@global_pipeline_config
@dataclass(frozen=True)
class FunctionRegistryConfig:
    """Configuration for function registry behavior across all libraries."""
    enable_scalar_functions: bool = True
    """
    Whether to register functions that return scalars.
    When True: Scalar-returning functions are wrapped as (array, scalar) tuples.
    When False: Scalar-returning functions are filtered out entirely.
    Applies uniformly to all libraries (CuPy, scikit-image, pyclesperanto).
    """


@global_pipeline_config
@dataclass(frozen=True)
class VisualizerConfig:
    """Configuration for shared visualization system settings."""
    temp_directory: Optional[Path] = None
    """Directory for temporary visualization files. If None, will auto-create in system temp."""

@global_pipeline_config
@dataclass(frozen=True)
class StreamingDefaults:
    """Default configuration for streaming to visualizers."""
    persistent: bool = True
    """Whether viewer stays open after pipeline completion."""

@global_pipeline_config(ui_hidden=True)
@dataclass(frozen=True)
class StreamingConfig(StepWellFilterConfig, StreamingDefaults, ABC):
    """Abstract base configuration for streaming to visualizers.

    Uses multiple inheritance from StepWellFilterConfig and StreamingDefaults.
    Inherited fields are automatically set to None by @global_pipeline_config(inherit_as_none=True).
    """

    @property
    @abstractmethod
    def backend(self) -> Backend:
        """Backend enum for this streaming type."""
        pass

    @property
    @abstractmethod
    def step_plan_output_key(self) -> str:
        """Key to use in step_plan for this config's output paths."""
        pass

    @abstractmethod
    def get_streaming_kwargs(self, global_config) -> dict:
        """Return kwargs needed for this streaming backend."""
        pass

    @abstractmethod
    def create_visualizer(self, filemanager, visualizer_config):
        """Create and return the appropriate visualizer for this streaming config."""
        pass


@global_pipeline_config
@dataclass(frozen=True)
class NapariStreamingConfig(StreamingConfig,NapariDisplayConfig):
    """Configuration for napari streaming."""
    napari_port: int = 5555
    """Port for napari streaming communication."""

    napari_host: str = 'localhost'
    """Host for napari streaming communication. Use 'localhost' for local, or remote IP for network streaming."""

    @property
    def backend(self) -> Backend:
        return Backend.NAPARI_STREAM

    @property
    def step_plan_output_key(self) -> str:
        return "napari_streaming_paths"

    def get_streaming_kwargs(self, context) -> dict:
        kwargs = {
            "napari_port": self.napari_port,
            "napari_host": self.napari_host,
            "display_config": self  # self is now the display config
        }

        # Include microscope handler for component parsing
        if context:
            kwargs["microscope_handler"] = context.microscope_handler

        return kwargs

    def create_visualizer(self, filemanager, visualizer_config):
        from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer
        return NapariStreamVisualizer(
            filemanager,
            visualizer_config,
            viewer_title="OpenHCS Pipeline Visualization",
            persistent=self.persistent,
            napari_port=self.napari_port,
            display_config=self  # self is now the display config
        )


@global_pipeline_config
@dataclass(frozen=True)
class FijiStreamingConfig(StreamingConfig, FijiDisplayConfig):
    """
    Configuration for Fiji streaming with display options.

    Inherits from both StreamingConfig and FijiDisplayConfig to provide
    feature parity with NapariStreamingConfig.
    """
    fiji_port: int = 5565  # Non-overlapping with Napari (5555-5564)
    """Port for Fiji streaming communication (different default from Napari)."""

    fiji_host: str = 'localhost'
    """Host for Fiji streaming communication. Use 'localhost' for local, or remote IP for network streaming."""

    fiji_executable_path: Optional[Path] = None
    """Path to Fiji/ImageJ executable. If None, will auto-detect."""

    @property
    def backend(self) -> Backend:
        return Backend.FIJI_STREAM

    @property
    def step_plan_output_key(self) -> str:
        return "fiji_streaming_paths"

    def get_streaming_kwargs(self, context) -> dict:
        """Return kwargs needed for Fiji streaming backend (matches Napari pattern)."""
        kwargs = {
            "fiji_port": self.fiji_port,
            "fiji_host": self.fiji_host,
            "fiji_executable_path": self.fiji_executable_path,
            "display_config": self  # self is now the display config
        }

        # Include microscope handler for component parsing
        if context:
            kwargs["microscope_handler"] = context.microscope_handler

        return kwargs

    def create_visualizer(self, filemanager, visualizer_config):
        from openhcs.runtime.fiji_stream_visualizer import FijiStreamVisualizer
        return FijiStreamVisualizer(
            filemanager,
            visualizer_config,
            viewer_title="OpenHCS Fiji Visualization",
            persistent=self.persistent,
            fiji_port=self.fiji_port,
            display_config=self
        )

# Inject all accumulated fields at the end of module loading
from openhcs.config_framework.lazy_factory import _inject_all_pending_fields
_inject_all_pending_fields()


# ============================================================================
# Configuration Framework Initialization
# ============================================================================

# Initialize configuration framework with OpenHCS types
from openhcs.config_framework import set_base_config_type

set_base_config_type(GlobalPipelineConfig)

# Note: We use the framework's default MRO-based priority function.
# More derived classes automatically get higher priority through MRO depth.
# No custom priority function needed - the framework handles it generically.

logger.debug("Configuration framework initialized with OpenHCS types")

# PERFORMANCE OPTIMIZATION: Pre-warm analysis caches at import time
# This eliminates the 1000ms+ first-load penalty when opening config windows
try:
    from openhcs.config_framework import prewarm_config_analysis_cache
    # Warm config hierarchy cache (for config windows)
    prewarm_config_analysis_cache(GlobalPipelineConfig)
except ImportError:
    # Circular import during subprocess initialization - cache warming not needed
    # for non-UI execution contexts (ZMQ server, workers, etc.)
    logger.debug("Skipping config cache warming (circular import during subprocess init)")

# NOTE: Step editor cache warming is done in openhcs.core.steps.__init__ to avoid circular imports
