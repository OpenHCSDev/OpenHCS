# OpenHCS Nature Methods Paper

## Working Title
**OpenHCS: A dimensional dataflow platform for composable high-content screening analysis**

## Paper Structure

### Files
- `01_abstract.md` - Abstract (150-200 words)
- `02_introduction.md` - Introduction (~1000 words)
- `03_results.md` - Results (main content)
- `04_discussion.md` - Discussion (~800 words)
- `05_methods.md` - Methods (detailed implementation)
- `06_figures.md` - Figure descriptions and planning
- `07_references.md` - Bibliography
- `notes.md` - Working notes and ideas

### Target Journal
**Nature Methods**
- Focus: Novel methods with broad applicability
- Emphasis: Biological validation + technical innovation
- Format: ~3000-4000 words main text, 6-8 figures

## Key Messages

1. **Problem**: HCS generates massive dimensional data (spatial × temporal × multi-channel × multi-well × multi-condition), but existing tools force researchers into rigid pipelines or complex scripting

2. **Innovation**: Dimensional dataflow compiler with declarative composition
   - Automatic dimensional bookkeeping
   - Correctness by construction
   - First-class provenance tracking

3. **Validation**: iPSC microfluidic device analysis
   - Biological insights enabled by OpenHCS
   - Performance benchmarks vs CellProfiler, ImageJ
   - Extensibility demonstrations

4. **Impact**: Platform for community, not just a tool
   - Open source, well-documented
   - Integration with pyclesperanto, napari
   - Enables analyses impractical with existing tools

## Differentiators from Existing Tools

- **vs CellProfiler**: Declarative composition, dimensional reasoning, type safety
- **vs ImageJ/FIJI**: Structured pipelines, provenance, reproducibility
- **vs Custom Scripts**: Correctness by construction, reusability, GUI

## TODO

- [ ] Draft abstract
- [ ] Write introduction
- [ ] Plan figures (6-8 total)
- [ ] Run performance benchmarks
- [ ] Analyze iPSC validation data
- [ ] Create architecture diagrams
- [ ] Write results section
- [ ] Draft discussion
- [ ] Compile methods section
- [ ] Gather references
- [ ] Create supplementary materials plan

## Collaboration Notes

- Robert Haase (pyclesperanto) - potential co-author
- Stowers Institute (Sumner Magruder) - institutional backing, validation data
- Need to discuss authorship strategy

## Timeline

TBD - discuss with Tristan

