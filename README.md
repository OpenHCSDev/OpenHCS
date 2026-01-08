# OpenHCS: Open High-Content Screening
<!--
<div align="center">
  <img src="https://raw.githubusercontent.com/trissim/openhcs/main/docs/source/_static/ezstitcher_logo.png" alt="OpenHCS Logo" width="400">
</div>
-->

[![PyPI version](https://img.shields.io/pypi/v/openhcs.svg)](https://pypi.org/project/openhcs/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Python 3.12+](https://img.shields.io/badge/python-3.11+-blue.svg)](https://www.python.org/downloads/)
[![GPU Accelerated](https://img.shields.io/badge/GPU-Accelerated-green.svg)](https://github.com/trissim/openhcs)
[![Documentation Status](https://readthedocs.org/projects/openhcs/badge/?version=latest)](https://openhcs.readthedocs.io/en/latest/?badge=latest)

**A bioimage analysis platform for high-content screening with compile-time validation and bidirectional GUI-code conversion.**

OpenHCS is designed to handle large microscopy datasets (100GB+) with an architecture that emphasizes early error detection and flexible workflows. The platform provides compile-time pipeline validation, live configuration updates across windows, and bidirectional conversion between GUI and code representations.

## Key Features

### 1. Compile-Time Pipeline Validation

Many bioimage analysis tools validate pipelines at runtime, which can lead to failures after hours of processing. OpenHCS uses a 5-phase compilation system to catch errors before execution starts:

```python
# Compilation produces immutable execution contexts
for well_id in wells_to_process:
    context = self.create_context(well_id)

    # 5-Phase Compilation - fails BEFORE execution starts
    PipelineCompiler.initialize_step_plans_for_context(context, pipeline_definition)
    PipelineCompiler.declare_zarr_stores_for_context(context, pipeline_definition, self)
    PipelineCompiler.plan_materialization_flags_for_context(context, pipeline_definition, self)
    PipelineCompiler.validate_memory_contracts_for_context(context, pipeline_definition, self)
    PipelineCompiler.assign_gpu_resources_for_context(context)

    context.freeze()  # Immutable - prevents state mutation during execution
    compiled_contexts[well_id] = context
```

This approach catches errors at compile time rather than after hours of processing. Immutable frozen contexts help prevent state mutation bugs during execution.

### 2. Live Cross-Window Configuration Updates

Configuration changes propagate across windows in real-time using lazy resolution with Python's contextvars and MRO-based inheritance:

- Open 3 windows simultaneously: GlobalPipelineConfig, PipelineConfig, StepConfig
- Edit a value in GlobalPipelineConfig
- Watch placeholders update in real-time in PipelineConfig and StepConfig windows
- Proper inheritance chain: Global → Pipeline → Step with scope isolation per orchestrator
- Save PipelineConfig, and step editors immediately use the new saved values

This uses a class-level registry of active form managers, Qt signals for cross-window updates, and contextvars-based context stacking with MRO-based dual-axis resolution.

### 3. Bidirectional UI-Code Conversion

Pipelines can be designed in the GUI, exported to Python code, edited as code, and re-imported back to the GUI with full fidelity:

1. **Design in GUI**: Build pipeline visually with drag-and-drop
2. **Export to Code**: Click "Code" button → get complete executable Python script
3. **Edit in Code**: Bulk modifications, complex parameter tuning, version control
4. **Re-import to GUI**: Save edited code → GUI updates with all changes
5. **Repeat**: Switch between representations seamlessly

**Three-Tier Generation Architecture**:
```
Function Patterns (Tier 1)
       ↓ (encapsulates imports)
Pipeline Steps (Tier 2)
       ↓ (encapsulates all pattern imports)
Orchestrator Config (Tier 3)
       ↓ (encapsulates all pipeline imports)
Complete Executable Script
```

This enables visual tools for rapid prototyping, code editing for complex modifications, and version control for collaboration.

### 4. Large Dataset Support

OpenHCS is designed to handle large high-content screening datasets (100GB+):

- **Virtual File System**: Automatic backend switching between memory, disk, and ZARR storage
- **OME-ZARR Compression**: Configurable algorithms (LZ4, ZLIB, ZSTD, Blosc) with adaptive chunking
- **GPU Resource Management**: Automatic assignment and load balancing across multiple GPUs
- **Parallel Processing**: Scales to arbitrary CPU cores with configurable worker processes

For example, processing entire 96-well plates with 9 sites per well, 4 channels, and 100+ timepoints (100GB+ per plate).

## Background

OpenHCS evolved from EZStitcher, a microscopy stitching library, into a more general bioimage analysis platform. The architecture addresses some common challenges in scientific software:

- Early error detection through compile-time validation
- Flexible workflows that work both in GUI and as code
- Handling datasets that exceed available memory
- Multi-GPU resource management

### Architecture

The codebase implements several patterns that may be of interest:

1. **Dual-Axis Configuration Framework**: Combines context hierarchy (global → pipeline → step) with class inheritance (MRO) for configuration resolution. Extracted as standalone library: [objectstate](https://github.com/trissim/objectstate)

2. **Lazy Dataclass Factory**: Runtime generation of configuration classes with `__getattribute__` interception for on-demand resolution.

3. **Cross-Window Live Updates**: Class-level registry of active form managers with Qt signals for propagating changes across windows.

4. **5-Phase Pipeline Compiler**: Separates pipeline definition from execution to enable compile-time validation.

5. **Bidirectional Code Generation**: Three-tier generation system (function patterns → pipeline steps → orchestrator) for round-trip conversion between GUI and code.

**See**: [Architecture Documentation](https://openhcs.readthedocs.io/en/latest/architecture/) for detailed technical analysis.

## Flexible Pipeline Platform

### General-Purpose Bioimage Analysis
OpenHCS provides a flexible platform for creating custom image analysis pipelines. Researchers can combine processing functions to build workflows tailored to their experimental needs.

### Function Library
The platform automatically discovers and integrates 574+ functions from multiple libraries (pyclesperanto, CuPy, PyTorch, JAX, TensorFlow, scikit-image), providing unified access to image processing, segmentation, and analysis tools.

### Custom Function Integration
Adding custom functions requires following simple signature conventions, allowing the platform to automatically discover and incorporate new processing capabilities.

## Supported Microscope Systems

OpenHCS provides unified interfaces for multiple microscope formats with automatic format detection:

- **ImageXpress (Molecular Devices)**: Complete support for high-content screening systems including metadata parsing and multi-well organization
- **Opera Phenix (PerkinElmer)**: Automated microscopy platform integration with full metadata support
- **OpenHCS Format**: Optimized internal format for maximum performance and compression
- **Extensible Architecture**: Framework for adding new microscope types without code changes

## Desktop Interface and Workflow

### Visual Pipeline Editor
The PyQt6 desktop interface provides drag-and-drop pipeline creation with real-time parameter adjustment and live preview of processing results.

### Bidirectional Code Integration
Pipelines can be exported as executable Python scripts for customization, then re-imported back to the interface.

### Real-Time Visualization
Integrated napari viewers provide immediate visualization of processing results, with persistent viewers that survive pipeline completion for examining intermediate results.

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

## Technical Architecture Deep Dive

OpenHCS demonstrates several architectural patterns applicable beyond microscopy. The codebase is worth studying for its novel approaches to common software engineering challenges.

### 5-Phase Pipeline Compilation System

**Problem**: Traditional scientific software fails at runtime after hours of processing.

**Solution**: Declarative compilation architecture that validates entire processing chains before execution.

**Implementation**:
```python
# Compilation produces immutable execution contexts
for well_id in wells_to_process:
    context = self.create_context(well_id)

    # 5-Phase Compilation - fails BEFORE execution starts
    PipelineCompiler.initialize_step_plans_for_context(context, pipeline_definition)
    PipelineCompiler.declare_zarr_stores_for_context(context, pipeline_definition, self)
    PipelineCompiler.plan_materialization_flags_for_context(context, pipeline_definition, self)
    PipelineCompiler.validate_memory_contracts_for_context(context, pipeline_definition, self)
    PipelineCompiler.assign_gpu_resources_for_context(context)

    context.freeze()  # Immutable - prevents state mutation during execution
    compiled_contexts[well_id] = context
```

**Key Innovations**:
- Immutable frozen contexts prevent state mutation bugs
- Compile-time validation catches errors before execution
- Separation of compilation and execution phases
- GPU resource assignment at compile time, not runtime

**See**: [Pipeline Compilation System](https://openhcs.readthedocs.io/en/latest/architecture/pipeline-compilation-system.html)

### Dual-Axis Configuration Framework

**Problem**: Configuration systems typically support either hierarchy (global → local) OR inheritance (class-based), not both.

**Solution**: Dual-axis resolution combining context hierarchy with class inheritance (MRO).

**Implementation**:
```python
# Lazy dataclass with __getattribute__ interception
class LazyPipelineConfig(PipelineConfig):
    def __getattribute__(self, name):
        # Stage 1: Check instance attributes (user overrides)
        # Stage 2: Check context stack (global → pipeline → step)
        # Stage 3: Walk MRO for class-level defaults
        # Stage 4: Return None if no value found
```

**Key Innovations**:
- Preserves None vs concrete value distinction for proper inheritance
- Contextvars-based context stacking for thread-safe resolution
- MRO-based dual-axis resolution (context + class hierarchy)
- Field-level inheritance (different fields can inherit from different sources)

**Extracted as standalone library**: [objectstate](https://github.com/trissim/objectstate)

**See**: [Configuration Framework](https://openhcs.readthedocs.io/en/latest/architecture/configuration_framework.html)

### Cross-Window Live Updates

**Problem**: Most GUI applications treat each window as isolated. Configuration changes require close-reopen cycles.

**Solution**: Class-level registry of active form managers with Qt signals for cross-window updates.

**Implementation**:
```python
# Class-level registry tracks all active form managers
_active_form_managers = []

# When a value changes in one window
def _emit_cross_window_change(self, param_name: str, value: object):
    field_path = f"{self.field_id}.{param_name}"
    self.context_value_changed.emit(field_path, value,
                                    self.object_instance, self.context_obj)

# Other windows receive the signal and refresh
def _on_cross_window_context_changed(self, field_path, new_value,
                                     editing_object, context_object):
    if not self._is_affected_by_context_change(editing_object, context_object):
        return
    self._schedule_cross_window_refresh()  # Debounced refresh
```

**Key Innovations**:
- Live context collection from other open windows
- Scope isolation (per-orchestrator) prevents cross-contamination
- Debounced updates prevent excessive refreshes
- Cascading placeholder refreshes (Global → Pipeline → Step)

**See**: [Parameter Form Lifecycle](https://openhcs.readthedocs.io/en/latest/architecture/parameter_form_lifecycle.html)

### Bidirectional UI-Code Interconversion

**Problem**: GUI tools can export to code but can't re-import. You're forced to choose between GUI or code.

**Solution**: Three-tier generation system with perfect round-trip integrity.

**Implementation**:
```python
# Tier 1: Function Pattern Generation
pattern = gaussian_filter(sigma=2.0, preserve_dtype=True)

# Tier 2: Pipeline Step Generation (encapsulates Tier 1 imports)
step_1 = FunctionStep(
    func=(gaussian_filter, {'sigma': 2.0, 'preserve_dtype': True}),
    name="gaussian_filter",
    variable_components=[VariableComponents.PLATE]
)

# Tier 3: Orchestrator Config (encapsulates Tier 1 + 2 imports)
global_config = GlobalPipelineConfig(num_workers=16)
pipeline_data = {plate_path: [step_1, step_2, ...]}
```

**Key Innovations**:
- Upward import encapsulation (each tier includes all lower tier imports)
- AST-based code parsing for re-import
- Lazy dataclass constructor patching preserves None vs concrete distinction
- Complete executability (generated code runs without additional imports)

**See**: [Code/UI Interconversion](https://openhcs.readthedocs.io/en/latest/architecture/code_ui_interconversion.html)

### Additional Architectural Patterns

**Process-Isolated Real-Time Visualization**: Napari integration via ZeroMQ eliminates Qt threading conflicts. Persistent viewers survive pipeline completion.

**Automatic Function Discovery**: 574+ functions from multiple GPU libraries with contract analysis and type-safe integration.

**Virtual File System**: Automatic backend switching (memory, disk, ZARR) for 100GB+ datasets with adaptive chunking.

**Strict Memory Type Management**: Compile-time validation of memory type compatibility with automatic conversion between array types.

**Evolution-Proof UI Generation**: Type-based form generation from Python annotations. Adapts automatically when signatures change.

**See**: [Complete Architecture Documentation](https://openhcs.readthedocs.io/en/latest/architecture/)



## Example Workflows

Complete analysis workflows demonstrate OpenHCS capabilities:

```bash
# View complete production examples
git clone https://github.com/trissim/openhcs.git
cat openhcs/examples/example_export.py
```

Example workflows include preprocessing, stitching, and analysis steps with GPU acceleration, large dataset handling through ZARR compression, parallel processing with resource monitoring, and comprehensive configuration management.

## Who Should Use OpenHCS?

### For Biologists and Microscopists

**Use OpenHCS if you**:
- Process high-content screening data (96-well plates, multi-site, multi-channel)
- Need to analyze 100GB+ datasets that break CellProfiler or ImageJ
- Want compile-time validation to catch errors before hours of processing
- Need GPU acceleration for faster analysis
- Want to switch between GUI and code without losing work

**Don't use OpenHCS if you**:
- Have simple analysis needs (single images, basic measurements) - use ImageJ/Fiji
- Need established community plugins - use CellProfiler
- Don't have Python 3.11+ or can't install dependencies

### For Software Engineers and Computer Scientists

**Study OpenHCS if you're interested in**:
- Novel configuration frameworks (dual-axis resolution, lazy dataclasses)
- Compile-time validation for scientific pipelines
- Cross-window live updates in GUI applications
- Bidirectional UI-code conversion with round-trip integrity
- Metaprogramming patterns (lazy dataclass factory, MRO-based resolution)

**The codebase demonstrates**:
- Contextvars-based context stacking for thread-safe resolution
- Immutable frozen contexts preventing state mutation
- Class-level registries for cross-window communication
- AST-based code generation and parsing
- Type-based UI generation from Python annotations

**Extracted libraries**:
- [objectstate](https://github.com/trissim/objectstate) - Hierarchical configuration framework

**Potential research contributions**:
- Configuration framework patterns (publishable in JOSS or PL conferences)
- Compile-time validation for scientific workflows
- Cross-window live updates architecture

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

# Run OMERO integration tests (requires Docker)
# See OMERO_TESTING_GUIDE.md for setup instructions
cd openhcs/omero && docker-compose up -d && ./wait_for_omero.sh && cd ../..
pytest tests/integration/test_main.py --it-microscopes=OMERO --it-backends=disk -v
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
