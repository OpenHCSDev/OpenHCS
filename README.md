# OpenHCS: Open High-Content Screening
<!--
<div align="center">
  <img src="https://raw.githubusercontent.com/trissim/openhcs/main/docs/source/_static/ezstitcher_logo.png" alt="OpenHCS Logo" width="400">
</div>
-->

[![PyPI version](https://img.shields.io/pypi/v/openhcs.svg)](https://pypi.org/project/openhcs/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Python 3.12+](https://img.shields.io/badge/python-3.12+-blue.svg)](https://www.python.org/downloads/)
[![GPU Accelerated](https://img.shields.io/badge/GPU-Accelerated-green.svg)](https://github.com/trissim/openhcs)
[![Documentation Status](https://readthedocs.org/projects/openhcs/badge/?version=latest)](https://openhcs.readthedocs.io/en/latest/?badge=latest)

## Bioimage Analysis Platform for High-Content Screening

OpenHCS addresses the computational challenges of high-content screening datasets that exceed the capabilities of traditional image analysis tools. The platform provides unified access to GPU-accelerated image processing libraries with automatic memory management for large-scale microscopy data analysis.

**Evolution from EZStitcher**: OpenHCS evolved from the EZStitcher microscopy stitching library into a comprehensive bioimage analysis platform. The system implements a 5-phase compilation architecture that validates entire processing chains before execution, addressing the runtime failures common in traditional image analysis workflows.

## Flexible Pipeline Platform

### General-Purpose Bioimage Analysis
OpenHCS provides a flexible platform for creating custom image analysis pipelines, similar to CellProfiler but with expanded capabilities. Researchers can combine processing functions to build workflows tailored to their specific experimental needs, from basic image preprocessing to complex multi-step analysis protocols.

### Extensive Function Library
The platform automatically discovers and integrates 574+ functions from multiple libraries (pyclesperanto, CuPy, PyTorch, JAX, TensorFlow, scikit-image), providing a comprehensive toolkit for image processing, segmentation, measurement, and analysis. This unified access eliminates the need to learn multiple software packages.

### Easy Function Integration
Adding custom functions requires minimal code changes. Researchers can integrate their own algorithms by following simple function signature conventions, enabling the platform to automatically discover and incorporate new processing capabilities without modifying core code.

### Scalable Processing Architecture
OpenHCS scales to arbitrary CPU cores and GPU devices given sufficient RAM availability. The platform uses configurable worker processes with automatic GPU resource assignment and load balancing. OME-ZARR compression with configurable algorithms (LZ4, ZLIB, ZSTD, Blosc) provides efficient storage for large datasets with automatic backend switching between memory, disk, and ZARR storage.

## Supported Microscope Systems

OpenHCS provides unified interfaces for multiple microscope formats with automatic format detection:

- **ImageXpress (Molecular Devices)**: Complete support for high-content screening systems including metadata parsing and multi-well organization
- **Opera Phenix (PerkinElmer)**: Automated microscopy platform integration with full metadata support
- **OpenHCS Format**: Optimized internal format for maximum performance and compression
- **Extensible Architecture**: Framework for adding new microscope types without code changes

## Desktop Interface and Workflow

### Visual Pipeline Editor
The PyQt6 desktop interface provides drag-and-drop pipeline creation, real-time parameter adjustment, and live preview of processing results. Users can design complex analysis workflows without programming knowledge.

### Bidirectional Code Integration
Unique UI-to-code conversion allows researchers to export visual pipelines as executable Python scripts for advanced customization, then re-import modified code back to the interface. This bridges the gap between visual tools and programmatic analysis.

### Real-Time Visualization
Integrated napari viewers provide immediate visualization of processing results. Persistent viewers survive pipeline completion, allowing researchers to examine intermediate results and validate analysis parameters.

## Installation

OpenHCS is available on PyPI and requires Python 3.11+ with optional GPU acceleration support for CUDA 12.x.

### Quick Start

```bash
# Desktop GUI (recommended for most users)
pip install openhcs[gui]

# Then launch the application
openhcs
```

### Installation Options

```bash
# Headless (servers, CI, programmatic use - no GUI)
pip install openhcs

# Desktop GUI only
pip install openhcs[gui]

# GUI + Napari viewer
pip install openhcs[gui,napari]

# GUI + Fiji/ImageJ viewer
pip install openhcs[gui,fiji]

# GUI + both viewers
pip install openhcs[gui,viz]

# Full installation (GUI + viewers + GPU)
pip install openhcs[gui,viz,gpu]

# Headless with GPU (server processing)
pip install openhcs[gpu]

# OMERO integration
pip install openhcs[omero]
```

**Optional Advanced Features**:
```bash
# GPU-accelerated Viterbi decoding for neurite tracing
pip install git+https://github.com/trissim/torbi.git

# JAX-based BaSiC illumination correction (optional, numpy/cupy versions included)
pip install basicpy
```

### Development Installation

```bash
# Clone the repository
git clone https://github.com/trissim/openhcs.git
cd openhcs

# Install with all features for development
pip install -e ".[all]"
```

### GPU Requirements

GPU acceleration requires CUDA 12.x. For CPU-only operation:

```bash
# Skip GPU dependencies entirely
export OPENHCS_CPU_ONLY=true
pip install openhcs[gui]
```

### Launch Application

After installing with `[gui]`, launch the desktop interface:

```bash
# Launch GUI (requires openhcs[gui])
openhcs

# Alternative commands
openhcs-gui                    # Same as 'openhcs'
python -m openhcs.pyqt_gui     # Module invocation

# With debug logging
openhcs --log-level DEBUG

# Show help
openhcs --help
```

**Note**: The `openhcs` command requires GUI dependencies. If you installed headless (`pip install openhcs`), you'll get a helpful error message telling you to install `openhcs[gui]`.

## Basic Usage

### Getting Started

OpenHCS provides a desktop interface for interactive pipeline creation and execution. The application guides users through microscopy data selection, pipeline configuration, and analysis execution.

```python
from openhcs.core.orchestrator.pipeline_orchestrator import PipelineOrchestrator
from openhcs.core.config import GlobalPipelineConfig

# Initialize OpenHCS
orchestrator = PipelineOrchestrator(
    input_dir="path/to/microscopy/data",
    global_config=GlobalPipelineConfig(num_workers=4)
)

# Initialize the orchestrator
orchestrator.initialize()

# Run complete analysis pipeline (requires pipeline definition)
# Use the desktop interface to create pipelines interactively
```

### Pipeline Definition

OpenHCS pipelines consist of FunctionStep objects that define processing operations. Each step specifies the function to execute, parameters, and data organization strategy:

```python
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.processors.cupy_processor import (
    stack_percentile_normalize, tophat, create_composite
)
from openhcs.processing.backends.analysis.cell_counting_cupy import count_cells_single_channel
from openhcs.processing.backends.pos_gen.ashlar_main_gpu import ashlar_compute_tile_positions_gpu
from openhcs.processing.backends.assemblers.assemble_stack_cupy import assemble_stack_cupy
from openhcs.constants.constants import VariableComponents

# Define processing pipeline
steps = [
    # Image preprocessing
    FunctionStep(
        func=[stack_percentile_normalize],
        name="normalize",
        variable_components=[VariableComponents.SITE]
    ),
    FunctionStep(
        func=[(tophat, {'selem_radius': 25})],
        name="enhance",
        variable_components=[VariableComponents.SITE]
    ),

    # Position generation for stitching
    FunctionStep(
        func=[ashlar_compute_tile_positions_gpu],
        name="positions",
        variable_components=[VariableComponents.SITE]
    ),

    # Image assembly using calculated positions
    FunctionStep(
        func=[assemble_stack_cupy],
        name="assemble",
        variable_components=[VariableComponents.SITE]
    ),

    # Cell analysis
    FunctionStep(
        func=[count_cells_single_channel],
        name="count_cells",
        variable_components=[VariableComponents.SITE]
    )
]

# Complete working examples available in openhcs/debug/example_export.py
```

## Processing Functions

OpenHCS provides access to over 574 image processing functions through automatic discovery from multiple libraries:

### Image Processing
The platform includes comprehensive image processing capabilities: normalization and denoising for preprocessing, Gaussian and median filtering for noise reduction, morphological operations including opening and closing, and projection operations for dimensionality reduction.

### Cell Analysis
Cell analysis functions support detection through blob detection algorithms (LOG, DOG, DOH), watershed segmentation, and threshold-based methods. GPU-accelerated watershed and region growing provide efficient segmentation. Measurement functions extract intensity, morphology, and texture features from segmented regions.

### Stitching Algorithms
OpenHCS implements GPU-accelerated versions of established stitching algorithms. MIST provides phase correlation with robust optimization for tile position calculation. Ashlar offers edge-based alignment with GPU acceleration. Assembly functions perform subpixel positioning and blending for final image reconstruction.

### Neurite Analysis
Specialized neurite analysis includes GPU-accelerated morphological thinning for skeletonization, SKAN-based neurite tracing with HMM models, and quantification of length, branching, and connectivity metrics.

## Documentation

Comprehensive documentation covers all aspects of OpenHCS architecture and usage:

- **[Read the Docs](https://openhcs.readthedocs.io/)** - Complete API documentation, tutorials, and guides
- **[Coverage Reports](https://trissim.github.io/openhcs/coverage/)** - Test coverage analysis
- **[API Reference](https://openhcs.readthedocs.io/en/latest/api/)** - Detailed function and class documentation
- **[User Guide](https://openhcs.readthedocs.io/en/latest/user_guide/)** - Step-by-step tutorials and examples

### Key Documentation Sections
- **Architecture**: [Pipeline System](https://openhcs.readthedocs.io/en/latest/architecture/pipeline-compilation-system.html) | [GPU Processing](https://openhcs.readthedocs.io/en/latest/architecture/gpu-resource-management.html) | [VFS](https://openhcs.readthedocs.io/en/latest/architecture/vfs-system.html)
- **Getting Started**: [Installation](https://openhcs.readthedocs.io/en/latest/getting_started/installation.html) | [First Pipeline](https://openhcs.readthedocs.io/en/latest/getting_started/first_pipeline.html)
- **Advanced Topics**: [GPU Optimization](https://openhcs.readthedocs.io/en/latest/guides/gpu_optimization.html) | [Large Datasets](https://openhcs.readthedocs.io/en/latest/guides/large_datasets.html)

## Advanced Technical Architecture

### Bidirectional UI-Code Interconversion
OpenHCS implements live conversion between graphical interface and executable Python code. Users can design pipelines visually, export to Python for complex editing, then re-import changes back to the interface. The three-tier generation system (function patterns → pipeline steps → orchestrator configuration) maintains perfect round-trip integrity between representations.

### Process-Isolated Real-Time Visualization
Automatic napari integration runs visualization in separate processes communicating via ZeroMQ, eliminating Qt threading conflicts. Persistent viewers survive pipeline completion, smart filtering shows only materialized outputs, and shared memory optimization handles large datasets efficiently without impacting pipeline performance.

### Automatic Function Discovery and Registration
The platform automatically discovers and integrates 574+ functions from multiple GPU libraries (pyclesperanto, CuPy, PyTorch, JAX, TensorFlow, scikit-image). Contract analysis determines 3D processing behavior, unified registration provides type-safe integration, and zero-copy GPU operations enable direct memory sharing between libraries.

### 5-Phase Pipeline Compilation System
Declarative compilation architecture separates pipeline definition from execution through five sequential phases: step plan initialization, ZARR store declaration, materialization planning, memory contract validation, and GPU resource assignment. This enables compile-time validation of entire processing chains and prevents runtime failures common in traditional image analysis tools.

The compiler transforms pipeline definitions into optimized execution plans:

1. **Step Plan Initialization**: Creates execution plans and resolves input/output paths within the virtual file system
2. **ZARR Store Declaration**: Declares necessary ZARR stores for large dataset compression
3. **Materialization Planning**: Determines which steps require persistent storage output
4. **Memory Contract Validation**: Validates GPU memory requirements and function compatibility
5. **GPU Resource Assignment**: Assigns specific GPU devices ensuring balanced utilization

```python
# Compilation produces immutable execution contexts
for well_id in wells_to_process:
    context = self.create_context(well_id)

    # 5-Phase Compilation
    PipelineCompiler.initialize_step_plans_for_context(context, pipeline_definition)
    PipelineCompiler.declare_zarr_stores_for_context(context, pipeline_definition, self)
    PipelineCompiler.plan_materialization_flags_for_context(context, pipeline_definition, self)
    PipelineCompiler.validate_memory_contracts_for_context(context, pipeline_definition, self)
    PipelineCompiler.assign_gpu_resources_for_context(context)

    context.freeze()  # Immutable execution context
    compiled_contexts[well_id] = context
```

### Dual-Axis Configuration System
Sophisticated configuration architecture combines context hierarchy (global → pipeline → step) with class inheritance. Lazy dataclass generation creates runtime configuration classes with custom resolution behavior. Field-level inheritance allows individual parameters to inherit from different sources while maintaining user overrides.

### Evolution-Proof UI Generation
Type-based UI generation automatically creates forms from Python type annotations. The system analyzes AbstractStep constructors via introspection, maps types to appropriate widgets, and adapts automatically when signatures change. Framework-independent logic works across PyQt6 and Textual interfaces.

### Strict Memory Type Management
Explicit memory type discipline enforces 3D output contracts, GPU device consistency, and compile-time validation of memory type compatibility. Automatic conversion between array types (NumPy, CuPy, PyTorch, JAX, TensorFlow) enables seamless multi-library integration with zero-copy operations where possible.

### Virtual File System with Backend Abstraction
Handles datasets exceeding 100GB through automatic backend switching between memory, disk, and ZARR storage. ZARR compression with adaptive chunking provides efficient storage for large microscopy datasets, while memory overlay systems manage intermediate data during processing.

### Extensible Microscope Format Support
Automatic handler discovery enables addition of new microscope formats without core code changes. Unified metadata interfaces provide consistent APIs across vendor formats (ImageXpress, Opera Phenix, OpenHCS), while format auto-detection identifies microscope types from directory structure.



## Example Workflows

Complete analysis workflows demonstrate OpenHCS capabilities:

```bash
# View complete production examples
git clone https://github.com/trissim/openhcs.git
cat openhcs/examples/example_export.py
```

Example workflows include preprocessing, stitching, and analysis steps with GPU acceleration, large dataset handling through ZARR compression, parallel processing with resource monitoring, and comprehensive configuration management.

## Contributing

OpenHCS welcomes contributions from the scientific computing community. The platform is actively developed for neuroscience research applications.

### Development Setup

```bash
# Clone the repository
git clone https://github.com/trissim/openhcs.git
cd openhcs

# Install in development mode with all features
pip install -e ".[all,dev]"

# Run tests
pytest tests/
```

### Contribution Areas
- **Microscope Formats**: Add support for additional imaging systems
- **Processing Functions**: Contribute specialized analysis algorithms
- **GPU Backends**: Extend support for new GPU computing libraries
- **Documentation**: Improve guides and examples

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Acknowledgments

OpenHCS builds upon EZStitcher and incorporates algorithms and concepts from established image analysis libraries including Ashlar for image stitching algorithms, MIST for phase correlation methods, pyclesperanto for GPU-accelerated image processing, and scikit-image for comprehensive image analysis tools.
