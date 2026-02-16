# Figures Plan

**Target**: 6-8 figures for Nature Methods

---

## Figure 1: Conceptual Overview & Problem Statement

**Type**: Schematic diagram

**Panels**:
- **a)** HCS dimensional complexity visualization
  - Show data cube with multiple axes (X, Y, Z, T, C, Well, Condition)
  - Illustrate explosion of combinations
  - Example: 96-well × 4 channels × 10 timepoints × 3 Z-planes = 11,520 images

- **b)** Common failure modes with existing tools
  - Dimensional mismatch errors
  - Lost metadata
  - Broken pipelines when design changes

- **c)** OpenHCS solution overview
  - Declarative config → Dimensional compiler → Type-safe execution
  - Automatic dimensional bookkeeping
  - Provenance tracking

**Message**: Dimensional complexity is the fundamental challenge; OpenHCS solves it through dimensional reasoning.

---

## Figure 2: Architecture & Dimensional Dataflow Compiler

**Type**: Technical diagram

**Panels**:
- **a)** System architecture
  - Config layer (declarative YAML/Python)
  - Compiler layer (dimensional reasoning, type checking)
  - Execution layer (GPU-accelerated processing)
  - Provenance layer (tracking and visualization)

- **b)** Dimensional dataflow example
  - Show how dimensions flow through pipeline steps
  - Type annotations at each stage
  - Automatic validation and error detection

- **c)** Config system hierarchy
  - Global pipeline config
  - Step-specific configs
  - Dual-axis resolution (saved vs live)

**Message**: Novel compiler architecture enables correctness by construction.

---

## Figure 3: Declarative Composition & Usability

**Type**: Code comparison + workflow diagram

**Panels**:
- **a)** Side-by-side comparison
  - OpenHCS declarative config (20-30 lines)
  - Equivalent CellProfiler pipeline (screenshot)
  - Equivalent ImageJ macro (50-100 lines)

- **b)** Composability demonstration
  - Show how steps compose
  - Reusable components
  - Type-safe connections

- **c)** Complexity reduction metrics
  - Lines of code comparison
  - Configuration complexity
  - Time to implement

**Message**: Declarative approach dramatically reduces complexity while improving correctness.

---

## Figure 4: Interactive Provenance & GUI

**Type**: GUI screenshots + interaction diagram

**Panels**:
- **a)** Main GUI overview
  - Config editor
  - Pipeline visualization
  - Napari integration

- **b)** Click-to-provenance workflow
  - User clicks on result in napari
  - System traces back through pipeline
  - Shows all intermediate steps and parameters

- **c)** Debugging scenario
  - Identify unexpected result
  - Trace provenance
  - Find root cause

**Message**: First-class provenance enables interactive exploration and debugging.

---

## Figure 5: Performance Benchmarks

**Type**: Quantitative plots

**Panels**:
- **a)** Processing speed comparison
  - OpenHCS vs CellProfiler vs ImageJ
  - Various dataset sizes
  - Show GPU acceleration benefit

- **b)** Memory efficiency
  - Peak memory usage
  - Scalability to large datasets

- **c)** Caching benefits
  - Time saved on re-runs
  - Interactive iteration speed

- **d)** Scalability demonstration
  - Performance vs dataset size
  - Linear scaling with parallelization

**Message**: Real performance improvements enable new scales of analysis.

---

## Figure 6: Biological Validation - iPSC Microfluidic Analysis

**Type**: Biological results + analysis workflow

**Panels**:
- **a)** Experimental design
  - iPSC microfluidic device schematic
  - Imaging strategy
  - Dimensional structure of dataset

- **b)** Analysis pipeline
  - OpenHCS workflow diagram
  - Key processing steps
  - Dimensional transformations

- **c)** Biological results
  - Quantitative phenotypes extracted
  - Statistical analysis
  - Biological insights

- **d)** Comparison to existing tools
  - What's possible with OpenHCS vs CellProfiler
  - Analysis that would be impractical otherwise

**Message**: OpenHCS enables biological discoveries through complex multi-dimensional analysis.

---

## Figure 7: Extensibility & Integration

**Type**: Code examples + ecosystem diagram

**Panels**:
- **a)** Custom step implementation
  - Show how easy it is to add new step
  - Minimal boilerplate
  - Automatic integration with compiler

- **b)** Ecosystem integration
  - pyclesperanto for GPU processing
  - napari for visualization
  - Standard file formats (OME-ZARR, etc.)

- **c)** Community extensions
  - Example custom steps from users
  - Plugin architecture

**Message**: Platform designed for community-driven extension.

---

## Figure 8: Use Cases Across Domains (Optional)

**Type**: Gallery of applications

**Panels**:
- Multiple brief examples showing versatility
- Different biological systems
- Different imaging modalities
- Different analysis goals

**Message**: General platform applicable across HCS domains.

---

## Supplementary Figures (Ideas)

- **S1**: Detailed architecture diagrams
- **S2**: Complete benchmark suite
- **S3**: Additional biological validation examples
- **S4**: Config schema documentation
- **S5**: Performance profiling details
- **S6**: Comparison matrix: OpenHCS vs all major tools

---

## Figure Creation TODO

- [ ] Create schematic diagrams (Inkscape/Illustrator)
- [ ] Generate architecture diagrams (from code or manual)
- [ ] Run benchmarks and create plots
- [ ] Capture GUI screenshots
- [ ] Analyze iPSC data and create result figures
- [ ] Code comparison examples
- [ ] Ensure all figures follow Nature Methods style guide

