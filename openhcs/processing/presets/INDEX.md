# Pipeline Presets Documentation Index

**Complete guide to OpenHCS pipeline presets and pattern analysis**

---

## 📚 Documentation Structure

This directory contains production-tested pipeline examples and comprehensive analysis for building a preset system. Documentation is organized by audience and purpose:

### For End Users

1. **[QUICK_REFERENCE.md](QUICK_REFERENCE.md)** - Start here!
   - Fast lookup guide for choosing pipelines
   - Common customizations
   - Quick start instructions
   - Troubleshooting tips
   - **Read time**: 5 minutes

2. **[README.md](README.md)** - Complete user guide
   - Detailed pipeline descriptions
   - Usage examples (GUI and programmatic)
   - Common parameter reference
   - Advanced patterns
   - Contributing guidelines
   - **Read time**: 15 minutes

### For Developers & Designers

3. **[../../docs/pipeline_preset_patterns.md](../../docs/pipeline_preset_patterns.md)** - Technical analysis
   - Detailed pattern analysis
   - Archetype definitions
   - GPU vs CPU implementation study
   - Preset system design recommendations
   - File-by-file breakdowns
   - **Read time**: 30 minutes

4. **[../../docs/PIPELINE_PRESETS_SUMMARY.md](../../docs/PIPELINE_PRESETS_SUMMARY.md)** - Executive summary
   - Task completion overview
   - Key findings
   - Statistics and metrics
   - Next steps for implementation
   - **Read time**: 10 minutes

---

## 🎯 Quick Navigation

### I want to...

**Use a pipeline right now**
→ [QUICK_REFERENCE.md](QUICK_REFERENCE.md) - Choose your pipeline and go

**Understand what's available**
→ [README.md](README.md) - Browse the complete catalog

**Design a preset system**
→ [pipeline_preset_patterns.md](../../docs/pipeline_preset_patterns.md) - Deep technical analysis

**Get project overview**
→ [PIPELINE_PRESETS_SUMMARY.md](../../docs/PIPELINE_PRESETS_SUMMARY.md) - High-level summary

---

## 📁 Pipeline Files

All pipeline examples are in the `pipelines/` subdirectory:

```
pipelines/
├── 10x_mfd_stitch_gpu.py                          # Multi-channel stitching (GPU)
├── 10x_mfd_stitch_ashlar_cpu.py                   # Multi-channel stitching (CPU)
├── imx_96_well_neurite_outgrowth_pipeline_gpu.py  # Full workflow (GPU)
├── imx_96_well_neurite_outgrowth_pipeline_cpu.py  # Full workflow (CPU)
├── 10x_mfd_crop_analyze.py                        # Device analysis (2-channel)
├── 10x_mfd_crop_analyze_dapi-fitc-cy5.py          # Device analysis (3-channel)
├── cy5_axon_cell_body_crop_analysis.py            # Dual-compartment analysis
├── cy5_ctb_cell_count.py                          # Simple preprocessing
└── test.py                                        # Minimal test pipeline
```

**Total**: 9 pipelines, 773 lines of code

---

## 📊 Documentation Statistics

| Document | Lines | Purpose | Audience |
|----------|-------|---------|----------|
| QUICK_REFERENCE.md | 219 | Fast lookup | End users |
| README.md | 305 | Complete guide | End users |
| pipeline_preset_patterns.md | 498 | Technical analysis | Developers |
| PIPELINE_PRESETS_SUMMARY.md | 384 | Executive summary | Stakeholders |
| **Total** | **1,406** | **Complete documentation** | **All** |

---

## 🔍 Key Findings at a Glance

### 4 Pipeline Archetypes

1. **Stitching** - Multi-site image assembly
2. **Crop + Analysis** - Microfluidic device workflows
3. **Dual-Compartment** - Separate spatial region analysis
4. **Simple Processing** - Basic filtering workflows

### GPU vs CPU

- **Difference**: Only the stitching function (1 line change)
- **Implication**: Single preset with GPU toggle is sufficient

### Common Parameters

- **Normalization**: `low_percentile: 0.1-1.0`, `high_percentile: 99.0-99.9`
- **Stitching**: `stitch_alpha: 0.2` (universal constant)
- **Cell counting**: Size-based variants (40-200 for small, 100-1000 for large)

---

## 🚀 Getting Started

### 1. Choose Your Path

**New User?** → Start with [QUICK_REFERENCE.md](QUICK_REFERENCE.md)

**Building Pipelines?** → Read [README.md](README.md)

**Designing Presets?** → Study [pipeline_preset_patterns.md](../../docs/pipeline_preset_patterns.md)

### 2. Pick a Pipeline

Browse the [pipeline comparison table](QUICK_REFERENCE.md#-pipeline-comparison-table) to find the right starting point.

### 3. Customize

Copy a pipeline and modify parameters for your specific needs.

### 4. Execute

Load in the GUI or run programmatically.

---

## 🎓 Learning Path

### Beginner

1. Read [QUICK_REFERENCE.md](QUICK_REFERENCE.md)
2. Copy a simple pipeline (`cy5_ctb_cell_count.py`)
3. Modify basic parameters (normalization, crop dimensions)
4. Execute in GUI

### Intermediate

1. Read [README.md](README.md) sections on your use case
2. Copy a complex pipeline (stitching or analysis)
3. Customize per-channel processing
4. Use advanced patterns (input source branching)

### Advanced

1. Study [pipeline_preset_patterns.md](../../docs/pipeline_preset_patterns.md)
2. Understand archetype patterns
3. Design custom workflows combining patterns
4. Contribute new presets

---

## 🔗 Related Documentation

### OpenHCS Core Documentation

- **Complete Examples**: `docs/source/guides/complete_examples.rst`
- **Production Examples**: `docs/source/user_guide/production_examples.rst`
- **Architecture**: `docs/source/architecture/`

### Pipeline System

- **Pipeline Class**: `openhcs/core/pipeline.py`
- **Function Steps**: `openhcs/core/steps/function_step.py`
- **Orchestrator**: `openhcs/core/orchestrator/orchestrator.py`

### Processing Backends

- **GPU Functions**: `openhcs/processing/backends/`
- **Analysis**: `openhcs/processing/backends/analysis/`
- **Processors**: `openhcs/processing/backends/processors/`

---

## 💡 Tips for Success

### Reading Documentation

- **Start small**: QUICK_REFERENCE → README → Patterns → Summary
- **Focus on your use case**: Stitching vs Analysis vs Simple
- **Try examples**: Copy and run before customizing

### Using Pipelines

- **GPU first**: Try GPU variants if available (faster)
- **Start simple**: Use basic pipelines before complex ones
- **Iterate**: Test on small data before full plates

### Contributing

- **Test thoroughly**: Run on real data
- **Document well**: Add comments for parameters
- **Follow conventions**: Use naming patterns
- **Update docs**: Add to README and patterns analysis

---

## 📞 Support

### Questions?

- Check [QUICK_REFERENCE.md](QUICK_REFERENCE.md) troubleshooting section
- Review [README.md](README.md) for detailed explanations
- Consult [pipeline_preset_patterns.md](../../docs/pipeline_preset_patterns.md) for technical details

### Contributing?

- Read [README.md](README.md) contributing section
- Follow file naming conventions
- Update all relevant documentation
- Test on production data

---

## 🗺️ Roadmap

### Current Status: Phase 1-3 Complete ✅

- [x] Pipeline collection organized
- [x] GPU/CPU variants created
- [x] Pattern analysis completed
- [x] Documentation written

### Future: Preset System Implementation

- [ ] Design preset schema (JSON/YAML)
- [ ] Implement preset loader
- [ ] Create preset UI
- [ ] Build code generator
- [ ] Add preset library
- [ ] Implement parameter inheritance
- [ ] Add GPU auto-detection

See [PIPELINE_PRESETS_SUMMARY.md](../../docs/PIPELINE_PRESETS_SUMMARY.md) for detailed roadmap.

---

## 📄 Document Versions

- **Created**: 2025-10-03
- **Last Updated**: 2025-10-03
- **Status**: Complete (Phase 1-3)
- **Next Review**: When preset system implementation begins

---

## 🏁 Summary

This preset collection provides:

- **9 production-tested pipelines** covering 4 major workflow types
- **1,406 lines of documentation** for all skill levels
- **Comprehensive pattern analysis** for preset system design
- **Clear roadmap** for future implementation

**Start here**: [QUICK_REFERENCE.md](QUICK_REFERENCE.md) → Pick a pipeline → Customize → Execute

**Questions?** Read the docs in order: Quick Reference → README → Patterns → Summary

