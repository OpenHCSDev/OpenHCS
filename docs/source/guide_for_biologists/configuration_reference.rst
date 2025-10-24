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


Appendix: Relevant Configuration Options
--------------------------------------------------

There are several configuration options available in OpenHCS. Below is a list of some of the most commonly used options:
(Note: Each configuration option also has a tooltip in the GUI that explains its purpose and usage. Hit the (?) button next to any option to see its tooltip.)

GlobalPipelineConfig (main app/pipeline defaults)
- Num Workers
  - How many parallel workers to run for processing (higher = more CPU usage).
- Materialization Results Path
  - Directory name where non-image analysis results (CSV/JSON) are written by default.
- Use Threading
  - If true, use threads instead of processes (useful for debugging or some environments).

WellFilterConfig
- well_filter
  - List, pattern, or integer limiting which wells are included (None = all wells).
- well_filter_mode
  - INCLUDE or EXCLUDE the above wells.

ZarrConfig
- Compression Level
  - Compression level (higher = smaller files but slower).

VFSConfig
- Read Backend
  - Backend used to read input files (should typically leave as Auto).
- Intermediate Backend
  - Backend for storing temporary intermediate results (memory, disk, etc.).
- Materialization Backend
  - Backend used for explicit materialized outputs (e.g., zarr vs disk).

For the above 2 options, the 3 choices that should be used is typically ZARR, Disk, or Memory. Memory stores to the temporary system memory (RAM), Disk and ZARR both store to disk, but ZARR uses the Zarr format which is more efficient and takes up less storage, while DISK uses Tiff files.

AnalysisConsolidationConfig
- Enabled
  - Run automatic consolidation of step outputs into summary files.
- MetaXpress Summary
  - Produce MetaXpress-compatible summary format.
- well_pattern, file_extensions, exclude_patterns, output_filename
  - Controls for which files to include/exclude and the consolidated output name.

PlateMetadataConfig
- Barcode, Plate Name, Plate ID, Description, Acquisition User
  - Optional metadata fields for the plate; auto-filled if None.

PathPlanningConfig (directory / output naming)
- Well Filter/Well Filter Mode
  - Inherited from StepWellFilterConfig unless overridden.
- Output Dir Suffix
  - Suffix appended to generated output folders (default "_openhcs").  For example, if your input folder is "data/plate1", the output folder will be "data/plate1_openhcs".
- Global Output Folder
  - Optional root folder to place all plate workspaces and outputs.
- Sub Dir
  - Subdirectory name used for image outputs inside a workspace.

StepWellFilterConfig and StepMaterializationConfig
- Step-level versions of well filtering and path planning.
- Inherits from higher levels unless overridden. (Materialization config inherits from global path planning config).
- StepMaterializationConfig.sub_dir
  - Default folder for step-level materializations (default "checkpoints").

VisualizerConfig
- temp_directory
  - Directory for temporary visualization files (if None, system temp is used).

StreamingConfig (abstract)
- Persistent
  - If true, keeps the streaming service open after initial use.

NapariStreamingConfig
- Colormap
  - Colormap to use for visualization.
- Variable size handling
  - How to handle variable-sized images (pad, rescale, etc.).
- Site/Channel/Timepoint/Well/Z-Index/Step Name/Step Index/Source Mode
  - Options for whether you'd like to group different variables by slice or stack.
- Persistent
  - If true, keeps the streaming service open after initial use.
- Well Filter/Well Filter Mode
  - Inherited from StepWellFilterConfig unless overridden.  
- napari_port, napari_host
  - Network settings for Napari streaming.

FijiStreamingConfig
- Lut
  - Colormap to use for visualization.
- Auto Contrast
  - If true, applies auto-contrast to images.
- Site/Channel/Timepoint/Well/Z-Index/Step Name/Step Index/Source Mode
  - Options for whether you'd like to group different variables by slice or stack.
- Persistent
  - If true, keeps the streaming service open after initial use.
- Well Filter/Well Filter Mode
  - Inherited from StepWellFilterConfig unless overridden.
- fiji_port, fiji_host, fiji_executable_path
  - Settings for Fiji/ImageJ streaming and the local executable location.

Note: The above mentions all the configuration options that are relevant to biologists using OpenHCS. There are many more configuration options available for advanced users and developers, which can be found in the code documentation. If you don't know what something does, its usually best to leave it at its default value.