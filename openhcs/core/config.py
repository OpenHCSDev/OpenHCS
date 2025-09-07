"""
Global configuration dataclasses for OpenHCS.

This module defines the primary configuration objects used throughout the application,
such as VFSConfig, PathPlanningConfig, and the overarching GlobalPipelineConfig.
Configuration is intended to be immutable and provided as Python objects.
"""

import logging
import os # For a potentially more dynamic default for num_workers
import threading
import dataclasses
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal, Optional, Union, Dict, Any, List, Type
from enum import Enum
from abc import ABC, abstractmethod
from openhcs.constants import Microscope
from openhcs.constants.constants import Backend

# Import decorator for automatic decorator creation
from openhcs.core.lazy_config import auto_create_decorator

# Import TilingLayout for TUI configuration
try:
    from textual_window import TilingLayout
except ImportError:
    # Fallback for when textual-window is not available
    from enum import Enum
    class TilingLayout(Enum):
        FLOATING = "floating"
        MASTER_DETAIL = "master_detail"

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
    SINGLE = "single"  # Single chunk per array (optimal for batch I/O)
    AUTO = "auto"      # Let zarr decide chunk size
    CUSTOM = "custom"  # User-defined chunk sizes


class MaterializationBackend(Enum):
    """Available backends for materialization (persistent storage only)."""
    ZARR = "zarr"
    DISK = "disk"


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
    by the sub_dir field in each step's materialization_config.
    """

    microscope: Microscope = Microscope.AUTO
    """Default microscope type for auto-detection."""

    use_threading: bool = field(default_factory=lambda: os.getenv('OPENHCS_USE_THREADING', 'false').lower() == 'true')
    """Use ThreadPoolExecutor instead of ProcessPoolExecutor for debugging. Reads from OPENHCS_USE_THREADING environment variable."""

    # Future extension point:
    # logging_config: Optional[Dict[str, Any]] = None # For configuring logging levels, handlers
    # plugin_settings: Dict[str, Any] = field(default_factory=dict) # For plugin-specific settings


# PipelineConfig will be created automatically by the injection system
# (GlobalPipelineConfig → PipelineConfig by removing "Global" prefix)


@global_pipeline_config
@dataclass(frozen=True)
class WellFilterConfig:
    """Base configuration for well filtering functionality."""
    well_filter: Optional[List[str]] = 8
    """List of wells to include/exclude. None means all wells."""

    well_filter_mode: WellFilterMode = WellFilterMode.INCLUDE
    """Whether well_filter is an include list or exclude list."""


@global_pipeline_config
@dataclass(frozen=True)
class ZarrConfig:
    """Configuration for Zarr storage backend."""
    store_name: str = "images"
    """Name of the zarr store directory."""

    compressor: ZarrCompressor = ZarrCompressor.ZLIB
    """Compression algorithm to use."""

    compression_level: int = 3
    """Compression level (1-9 for LZ4, higher = more compression)."""

    shuffle: bool = True
    """Enable byte shuffling for better compression (blosc only)."""

    chunk_strategy: ZarrChunkStrategy = ZarrChunkStrategy.SINGLE
    """Chunking strategy for zarr arrays."""

    ome_zarr_metadata: bool = True
    """Generate OME-ZARR compatible metadata and structure."""

    write_plate_metadata: bool = True
    """Write plate-level metadata for HCS viewing (required for OME-ZARR viewers like napari)."""


@global_pipeline_config
@dataclass(frozen=True)
class VFSConfig:
    """Configuration for Virtual File System (VFS) related operations."""
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
    well_filter: Optional[List[str]] = 1

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
    """
    # Override to None to enable lazy resolution from StepWellFilterConfig
    #well_filter: Optional[List[str]] = None

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
class NapariStreamingConfig(StreamingConfig):
    """Configuration for napari streaming."""
    napari_port: int = 5555
    """Port for napari streaming communication."""

    @property
    def backend(self) -> Backend:
        return Backend.NAPARI_STREAM

    @property
    def step_plan_output_key(self) -> str:
        return "napari_streaming_paths"

    def get_streaming_kwargs(self, global_config) -> dict:
        return {"napari_port": self.napari_port}

    def create_visualizer(self, filemanager, visualizer_config):
        from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer
        return NapariStreamVisualizer(
            filemanager,
            visualizer_config,
            viewer_title="OpenHCS Pipeline Visualization",
            persistent=self.persistent,
            napari_port=self.napari_port
        )


@global_pipeline_config
@dataclass(frozen=True)
class FijiStreamingConfig(StreamingConfig):
    """Configuration for fiji streaming."""
    fiji_executable_path: Optional[Path] = None
    """Path to Fiji/ImageJ executable. If None, will auto-detect."""

    @property
    def backend(self) -> Backend:
        return Backend.FIJI_STREAM

    @property
    def step_plan_output_key(self) -> str:
        return "fiji_streaming_paths"

    def get_streaming_kwargs(self, global_config) -> dict:
        return {"fiji_executable_path": self.fiji_executable_path}

    def create_visualizer(self, filemanager, visualizer_config):
        from openhcs.runtime.fiji_stream_visualizer import FijiStreamVisualizer
        return FijiStreamVisualizer(
            filemanager,
            viewer_title="OpenHCS Fiji Visualization",
            visualizer_config=visualizer_config,
            persistent=self.persistent
        )

@dataclass(frozen=True)
class TilingKeybinding:
    """Declarative mapping between key combination and window manager method."""
    key: str
    action: str  # method name that already exists
    description: str

@dataclass(frozen=True)
class TilingKeybindings:
    """Declarative mapping of tiling keybindings to existing methods."""

    # Focus controls
    focus_next: TilingKeybinding = TilingKeybinding("ctrl+j", "focus_next_window", "Focus Next Window")
    focus_prev: TilingKeybinding = TilingKeybinding("ctrl+k", "focus_previous_window", "Focus Previous Window")

    # Layout controls - map to wrapper methods
    horizontal_split: TilingKeybinding = TilingKeybinding("ctrl+shift+h", "set_horizontal_split", "Horizontal Split")
    vertical_split: TilingKeybinding = TilingKeybinding("ctrl+shift+v", "set_vertical_split", "Vertical Split")
    grid_layout: TilingKeybinding = TilingKeybinding("ctrl+shift+g", "set_grid_layout", "Grid Layout")
    master_detail: TilingKeybinding = TilingKeybinding("ctrl+shift+m", "set_master_detail", "Master Detail")
    toggle_floating: TilingKeybinding = TilingKeybinding("ctrl+shift+f", "toggle_floating", "Toggle Floating")

    # Window movement - map to extracted window_manager methods
    move_window_prev: TilingKeybinding = TilingKeybinding("ctrl+shift+left", "move_focused_window_prev", "Move Window Left")
    move_window_next: TilingKeybinding = TilingKeybinding("ctrl+shift+right", "move_focused_window_next", "Move Window Right")
    rotate_left: TilingKeybinding = TilingKeybinding("ctrl+alt+left", "rotate_window_order_left", "Rotate Windows Left")
    rotate_right: TilingKeybinding = TilingKeybinding("ctrl+alt+right", "rotate_window_order_right", "Rotate Windows Right")

    # Gap controls
    gap_increase: TilingKeybinding = TilingKeybinding("ctrl+plus", "gap_increase", "Increase Gap")
    gap_decrease: TilingKeybinding = TilingKeybinding("ctrl+minus", "gap_decrease", "Decrease Gap")

    # Bulk operations
    minimize_all: TilingKeybinding = TilingKeybinding("ctrl+shift+d", "minimize_all_windows", "Minimize All")
    open_all: TilingKeybinding = TilingKeybinding("ctrl+shift+o", "open_all_windows", "Open All")



@dataclass(frozen=True)
class TUIConfig:
    """Configuration for OpenHCS Textual User Interface."""
    default_tiling_layout: TilingLayout = TilingLayout.MASTER_DETAIL
    """Default tiling layout for window manager on startup."""

    default_window_gap: int = 1
    """Default gap between windows in tiling mode (in characters)."""

    enable_startup_notification: bool = True
    """Whether to show notification about tiling mode on startup."""

    keybindings: TilingKeybindings = field(default_factory=TilingKeybindings)
    """Declarative mapping of all tiling keybindings."""


# Inject all accumulated fields at the end of module loading
from openhcs.core.lazy_config import _inject_all_pending_fields
_inject_all_pending_fields()

