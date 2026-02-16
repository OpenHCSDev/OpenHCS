# Benchmarking Plan for OpenHCS

## Overview

Benchmarking is critical for Nature Methods papers. We need to demonstrate **quantitative performance improvements** over existing tools, ideally showing order-of-magnitude gains where possible.

---

## Standard Benchmark Datasets

### 1. Broad Bioimage Benchmark Collection (BBBC)

**Source**: https://bbbc.broadinstitute.org/

The BBBC is the gold standard for bioimage analysis benchmarking, cited in 500+ studies. Key datasets for HCS:

#### Recommended BBBC Datasets for OpenHCS:

- **BBBC021** - Human MCF7 cells (DMSO vs. treated)
  - Multi-well, multi-channel
  - Standard HCS workflow
  - Good for dimensional reasoning demonstration

- **BBBC022** - Human U2OS cells (Cell Painting)
  - 5-channel Cell Painting assay
  - 55 compounds, 38 concentrations
  - Perfect for showing OpenHCS handles complex multi-dimensional data

- **BBBC038** - Kaggle 2018 Data Science Bowl (nuclei segmentation)
  - Large dataset (670 images)
  - Diverse cell types and imaging conditions
  - Good for scalability testing

- **BBBC039** - U2OS cells in chemical screen
  - 200 images, fluorescent nuclei
  - Multi-well plate format
  - Demonstrates typical HCS use case

#### Why BBBC?
- **Widely recognized**: Standard in the field
- **Publicly available**: Reproducible benchmarks
- **Diverse**: Multiple imaging modalities and biological systems
- **Cited**: Using BBBC makes comparisons to other papers easier

---

## Benchmark Categories

### 1. **Processing Speed**

**What to measure**:
- Time to complete full pipeline (end-to-end)
- Time per image
- Time per well
- Time for specific operations (segmentation, feature extraction, etc.)

**Comparisons**:
- OpenHCS vs CellProfiler
- OpenHCS vs ImageJ/FIJI macros
- OpenHCS vs custom Python scripts

**Datasets**:
- BBBC021 (small-medium scale)
- BBBC022 (medium scale, complex)
- BBBC038 (large scale)

**Expected results**:
- GPU acceleration should show significant speedup
- Intelligent caching should reduce re-run time dramatically
- Dimensional compiler overhead should be minimal

**Metrics to report**:
- Total processing time (seconds/minutes)
- Images per second
- Speedup factor (e.g., "5× faster than CellProfiler")

---

### 2. **Memory Efficiency**

**What to measure**:
- Peak memory usage
- Memory usage vs dataset size
- Memory scaling with parallelization

**Comparisons**:
- OpenHCS vs CellProfiler
- OpenHCS vs custom scripts

**Datasets**:
- Vary dataset sizes (10 images → 1000 images)
- BBBC038 (large dataset)

**Expected results**:
- Efficient dimensional bookkeeping should minimize memory overhead
- Lazy evaluation where possible

**Metrics to report**:
- Peak RAM usage (GB)
- Memory per image (MB/image)
- Scalability curve (memory vs dataset size)

---

### 3. **Scalability**

**What to measure**:
- Performance vs dataset size
- Parallelization efficiency
- GPU utilization

**Datasets**:
- Synthetic datasets of varying sizes
- BBBC datasets at different scales

**Expected results**:
- Linear or better scaling with dataset size
- Efficient parallelization (near-linear speedup with cores)
- High GPU utilization for pyclesperanto operations

**Metrics to report**:
- Processing time vs dataset size (plot)
- Speedup vs number of cores (plot)
- GPU utilization percentage

---

### 4. **Caching Benefits**

**What to measure**:
- Time for initial run vs re-run with cached results
- Time saved when changing only downstream steps
- Interactive iteration speed

**Scenarios**:
- Full pipeline re-run (should use cache)
- Change final analysis step (should only recompute that step)
- Change intermediate step (should recompute from that point)

**Expected results**:
- Dramatic speedup for re-runs (10-100×)
- Intelligent partial recomputation

**Metrics to report**:
- Initial run time vs cached re-run time
- Time saved percentage
- Speedup factor for iterative development

---

### 5. **Correctness / Accuracy**

**What to measure**:
- Numerical accuracy compared to reference implementations
- Consistency of results across runs
- Dimensional correctness (no mismatches)

**Datasets**:
- BBBC datasets with ground truth
- Synthetic data with known answers

**Expected results**:
- Identical or near-identical results to reference implementations
- Zero dimensional mismatch errors (vs common errors in manual pipelines)

**Metrics to report**:
- Correlation with reference results (R² > 0.99)
- Number of dimensional errors (should be 0)
- Reproducibility (identical results across runs)

---

## Comparison Tools

### Primary Comparisons:

1. **CellProfiler** (v4.2.1 or latest)
   - Industry standard for HCS
   - Most direct comparison
   - Well-documented, widely used

2. **ImageJ/FIJI** (with macros)
   - Common alternative
   - Represents "expert scripting" approach
   - Good for showing usability improvements

3. **Custom Python Scripts** (using scikit-image, scipy)
   - Represents "from scratch" approach
   - Shows value of platform vs DIY

### Secondary Comparisons (if time permits):

4. **QuPath** (for whole-slide imaging comparison)
5. **Icy** (another bioimage analysis platform)

---

## Benchmark Execution Plan

### Phase 1: Setup (Week 1)
- [ ] Download BBBC datasets (BBBC021, BBBC022, BBBC038, BBBC039)
- [ ] Create equivalent pipelines in:
  - OpenHCS (declarative config)
  - CellProfiler (pipeline file)
  - ImageJ (macro)
  - Python script (scikit-image)
- [ ] Verify all pipelines produce equivalent results

### Phase 2: Performance Benchmarks (Week 2)
- [ ] Run processing speed tests (multiple runs, average)
- [ ] Run memory profiling tests
- [ ] Run scalability tests (varying dataset sizes)
- [ ] Run caching benefit tests

### Phase 3: Analysis & Visualization (Week 3)
- [ ] Analyze results
- [ ] Create benchmark plots (speed, memory, scalability)
- [ ] Generate comparison tables
- [ ] Write benchmark results section for paper

---

## Expected Quantitative Results (Hypotheses)

Based on OpenHCS architecture, we expect:

- **Processing speed**: 5-10× faster than CellProfiler (GPU acceleration)
- **Memory efficiency**: Similar or better than CellProfiler
- **Caching benefits**: 10-100× speedup for re-runs
- **Scalability**: Linear scaling with dataset size
- **Correctness**: Zero dimensional errors (vs common manual errors)

---

## Benchmark Reporting Format

For the paper, report results as:

**Table 1: Performance Comparison**
| Tool | Dataset | Time (s) | Memory (GB) | Speedup |
|------|---------|----------|-------------|---------|
| OpenHCS | BBBC021 | X | Y | 1.0× |
| CellProfiler | BBBC021 | X | Y | 0.2× |
| ImageJ | BBBC021 | X | Y | 0.1× |

**Figure 5: Performance Benchmarks**
- Panel A: Processing speed comparison (bar chart)
- Panel B: Memory usage comparison (bar chart)
- Panel C: Scalability (line plot: time vs dataset size)
- Panel D: Caching benefits (bar chart: initial vs re-run)

---

## Notes

- All benchmarks should be run on the same hardware (document specs)
- Multiple runs (n=3 minimum) with error bars
- Report both mean and standard deviation
- Include system specs in methods section
- Make benchmark scripts publicly available (reproducibility)

