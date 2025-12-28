# Introduction

**Target**: ~1000 words

---

## Outline

1. **The HCS Data Complexity Problem** (2-3 paragraphs)
   - HCS generates multi-dimensional data
   - Dimensions: spatial (XY, Z), temporal (T), channels (C), wells, conditions, replicates
   - Data volumes growing faster than analysis capabilities
   - Example: typical HCS experiment scale

2. **Limitations of Existing Tools** (2-3 paragraphs)
   - CellProfiler: powerful but rigid pipelines, manual dimensional management
   - ImageJ/FIJI: flexible but requires expert scripting, no provenance
   - Custom scripts: error-prone, not reusable, hard to validate
   - Common failure mode: dimensional mismatches, lost metadata, irreproducible analyses

3. **The Need for Dimensional Reasoning** (1-2 paragraphs)
   - Dimensions should be first-class abstractions, not implementation details
   - Type systems can prevent entire classes of errors
   - Declarative composition enables reusability and validation

4. **OpenHCS Solution** (2-3 paragraphs)
   - Dimensional dataflow compiler with automatic bookkeeping
   - Declarative configuration with type safety
   - First-class provenance tracking
   - GPU acceleration and intelligent caching
   - Platform for community extension

5. **Paper Overview** (1 paragraph)
   - What we demonstrate
   - Key results preview
   - Biological validation

---

## Draft Paragraphs

### Opening

High-content screening (HCS) has become a cornerstone of modern biological research, enabling systematic interrogation of cellular phenotypes across genetic, chemical, and environmental perturbations. Modern HCS experiments routinely generate terabyte-scale datasets spanning multiple dimensions: spatial (XY, Z-stacks), temporal (time-lapse), spectral (multi-channel fluorescence), experimental (multi-well plates, conditions, replicates), and biological (cell populations, organelles, molecular markers). This dimensional complexity, while scientifically powerful, poses fundamental challenges for analysis: researchers must track data transformations across all axes, maintain metadata consistency, ensure reproducibility, and compose complex multi-step pipelines—all while avoiding the subtle errors that arise from dimensional mismatches.

### Existing Tools Limitations

Current analysis tools approach this complexity through two divergent strategies, each with significant limitations. Graphical pipeline builders like CellProfiler provide accessible interfaces and validated modules but require manual management of dimensional structure, leading to brittle pipelines that break when experimental designs change. Scripting environments like ImageJ/FIJI offer flexibility but place the burden of dimensional bookkeeping entirely on the user, resulting in error-prone code that is difficult to validate, reproduce, or share. Both approaches treat dimensions as implementation details rather than first-class abstractions, forcing researchers to repeatedly solve the same dimensional reasoning problems in each new analysis.

### [Continue with remaining sections...]

---

## Key Points to Emphasize

- **Problem is fundamental, not incremental**: Dimensional complexity is THE challenge
- **Existing tools aren't bad, they're limited by design**: Be respectful but clear
- **Type systems and declarative programming are proven paradigms**: Not inventing new CS
- **Biological research needs this**: Connect to real scientific problems

## References Needed

- [ ] HCS review papers (data scale, applications)
- [ ] CellProfiler papers (cite respectfully)
- [ ] ImageJ/FIJI papers
- [ ] Type systems in scientific computing
- [ ] Provenance in computational biology
- [ ] GPU acceleration for image processing (pyclesperanto)

## Tone

- Authoritative but not arrogant
- Problem-focused, not tool-bashing
- Emphasize enabling science
- Clear about what's novel (dimensional reasoning) vs what's integration (GPU, napari)

