Configuration Reference
===============================

This section provides a reference of the configuration system of OpenHCS.

How the configuration system works
----------------------

In OpenHCS, there are multiple levels of configuration that determine how the software behaves. These levels include:
1. **Global Configuration**: This is the configuration that applies to the entire OpenHCS installation. 
2. **Plate Configuration**: Each plate can have its own configuration settings that override the global settings.
3. **Step Configuration**: Each step within a plate's pipeline can have its own configuration settings that
4. **Materialization/Napari Viewer Configuration**: For each individaul step, you can materialize its output, and save it to disk, or stream it to Napari. This also has its own configuration system.

Configurations automatically inherit from higher levels, and can be overridden at lower levels.  Some specific options also inherit horizontally, which will be explained in the relevant sections.
Some levels do not have all configuration options - for example, the materialization configuration only has options relevant to materialization.


Appendix: Relevant Configuration Options (Ripped straight from config.py, needs work)
--------------------------------------------------

There are several configuration options available in OpenHCS. Below is a list of some of the most commonly used options:
(Note: Each configuration option also has a tooltip in the GUI that explains its purpose and usage. Hit the (?) button next to any option to see its tooltip.)

Top-level enums and choices
- ZarrCompressor
  - Which compressor to use for Zarr storage (blosc, zlib, lz4, zstd, or none).
- ZarrChunkStrategy
  - How to chunk Zarr arrays: per-well (good for batching) or per-file (good for random access).
- MaterializationBackend
  - Where to write materialized outputs: automatic choice, zarr, plain disk, or OMERO local.
- WellFilterMode
  - Whether a well list is an INCLUDE list (only those wells) or an EXCLUDE list (skip those wells).

GlobalPipelineConfig (main app/pipeline defaults)
- num_workers
  - How many parallel workers to run for processing (higher = more CPU usage).
- materialization_results_path
  - Directory name where non-image analysis results (CSV/JSON) are written by default.
- microscope
  - Default microscope type for auto-detection (uses constants like AUTO).
- use_threading
  - If true, use threads instead of processes (useful for debugging or some environments).

Display / streaming helper enums
- NapariColormap, NapariDimensionMode, NapariVariableSizeHandling
  - Controls how Napari shows images: color maps, whether to show slices or stacks, and how to handle images of different sizes.
- FijiLUT, FijiDimensionMode
  - Similar controls for Fiji/ImageJ display mapping (LUTs and channel/slice/frame choices).

WellFilterConfig
- well_filter
  - List, pattern, or integer limiting which wells are included (None = all wells).
- well_filter_mode
  - INCLUDE or EXCLUDE behavior for the well_filter field.

ZarrConfig
- compressor
  - Which Zarr compressor to use for image storage.
- compression_level
  - Compression level (higher = smaller files but slower).
- chunk_strategy
  - Choose WELL or FILE chunking strategy.

VFSConfig
- read_backend
  - Backend used to read input files (auto-detected or explicit choice).
- intermediate_backend
  - Backend for temporary intermediate results (memory, disk, etc.).
- materialization_backend
  - Backend used for explicit materialized outputs (e.g., zarr vs disk).

AnalysisConsolidationConfig
- enabled
  - Run automatic consolidation of step outputs into summary files.
- metaxpress_style
  - Produce MetaXpress-compatible summary format.
- well_pattern, file_extensions, exclude_patterns, output_filename
  - Controls for which files to include/exclude and the consolidated output name.

PlateMetadataConfig
- barcode, plate_name, plate_id, description
  - Optional metadata fields for the plate; auto-filled if None.
- acquisition_user
  - User string to record as the data acquirer.
- z_step
  - Z-step string used for MetaXpress compatibility.

ExperimentalAnalysisConfig
- enabled
  - Toggle the experimental analysis pipeline features.
- config_file_name, design_sheet_name, plate_groups_sheet_name
  - Names/locations for Excel sheets that define experiment design.
- normalization_method
  - How to normalize results (e.g., fold_change or z_score).
- export_raw_results, export_heatmaps
  - Whether to produce raw CSVs and heatmap visualizations.
- auto_detect_format, default_format
  - Try to detect microscope format automatically; fallback format if detection fails.
- enable_wells_exclusion, metaxpress_summary_enabled
  - Extra toggles for analysis behavior and outputs.

PathPlanningConfig (directory / output naming)
- output_dir_suffix
  - Suffix appended to generated output folders (default "_openhcs").
- global_output_folder
  - Optional root folder to place all plate workspaces and outputs.
- sub_dir
  - Subdirectory name used for image outputs inside a workspace.

StepWellFilterConfig and StepMaterializationConfig
- Step-level versions of well filtering and path planning.
- StepMaterializationConfig.sub_dir
  - Default folder for step-level materializations (default "checkpoints").

FunctionRegistryConfig
- enable_scalar_functions
  - Whether functions that return scalars are included in the registry (affects available functions).

VisualizerConfig
- temp_directory
  - Directory for temporary visualization files (if None, system temp is used).

StreamingDefaults
- persistent
  - Whether streamed viewers stay open after a pipeline finishes.

StreamingConfig (abstract)
- Abstract base for streaming backends (Napari, Fiji). Concrete configs provide:
  - backend: enum identifying the streaming backend
  - step_plan_output_key: key used to store streaming artifacts in the plan
  - get_streaming_kwargs / create_visualizer: helper methods used at runtime

NapariStreamingConfig
- napari_port, napari_host
  - Network settings for Napari streaming.
- backend / step_plan_output_key
  - Backend enum and plan key used internally.

FijiStreamingConfig
- fiji_port, fiji_host, fiji_executable_path
  - Settings for Fiji/ImageJ streaming and the local executable location.

Notes and where to change things
- Global defaults live in openhcs/core/config.py and are wired into the config framework.
- Per-plate or per-step overrides can be saved with plate metadata or step materialization configs.
- For environment-level changes (install path, GPU choices) edit GlobalPipelineConfig or provide overrides at app startup.
- If you plan to change defaults that affect storage or GPU backends, test on a small dataset first.

