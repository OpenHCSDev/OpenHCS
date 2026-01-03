# Unified Paper Build System

## Overview

Replaced fragmented shell scripts with a single orthogonal Python builder.

**Files:**
- `scripts/build_papers.py` - Main builder (250 lines)
- `scripts/papers.yaml` - Metadata (single source of truth)

## Usage

```bash
# Build all papers (all formats)
python3 scripts/build_papers.py all

# Build specific format
python3 scripts/build_papers.py markdown all    # All markdown
python3 scripts/build_papers.py latex all       # All LaTeX PDFs
python3 scripts/build_papers.py lean all        # All Lean proofs
python3 scripts/build_papers.py arxiv all       # All arXiv packages

# Build specific paper
python3 scripts/build_papers.py markdown paper1
python3 scripts/build_papers.py latex paper3
python3 scripts/build_papers.py lean paper2
python3 scripts/build_papers.py arxiv paper1    # Package paper1 for arXiv
```

## arXiv Packaging

The `arxiv` build type creates complete submission packages:

```bash
python3 scripts/build_papers.py arxiv all
```

Each package contains:
- **PDF**: The compiled paper
- **Markdown**: Full text for LLM consumption
- **Lean proofs**: All source files (build artifacts excluded)

Output: `docs/papers/paper{N}_{name}/paper{N}_{name}_arxiv.tar.gz`

Example contents:
```
paper1_typing_discipline/
  main.pdf                          # Compiled PDF
  paper1_typing_discipline.md        # Full markdown
  proofs/
    PrintAxioms.lean
    abstract_class_system.lean
    axis_framework.lean
    ... (11 Lean files total)
```

## Architecture

### Single Source of Truth: `papers.yaml`

```yaml
papers:
  paper1:
    name: "Typing Discipline"
    dir: "paper1_typing_discipline"
    latex_dir: "toplas"
    latex_file: "main.tex"
    lean_lines: 2666
    content_files:
      - "01_introduction.tex"
      - "02_preliminaries.tex"
      ...
```

All paper metadata in one place. No hardcoded values in code.

### Generic Builders

```python
def build_lean(paper_id):      # One function, all papers
def build_latex(paper_id):     # One function, all papers
def build_markdown(paper_id):  # One function, all papers
```

No special cases. All papers treated identically.

### Fail Loudly

- Validates prerequisites (pdflatex, pandoc, lake)
- Checks file existence before reading
- Propagates errors clearly
- No silent failures or fallbacks

## Principles

✓ **Orthogonal**: One function per build type
✓ **Declarative**: YAML metadata replaces imperative code
✓ **Generic**: Eliminates 8 nearly-identical functions
✓ **Fail Loud**: No `|| true`, errors propagate
✓ **Uniform**: All papers have identical structure

## Restructuring

Papers 3-5 were restructured to match papers 1-2:

```
paper3_leverage/
  shared/
    content/
      01_introduction.tex
      02_foundations.tex
      ...
      abstract.tex
```

This was done automatically by `scripts/restructure_papers.py`.

## Results

✓ All markdown builds pass (5/5)
✓ All LaTeX builds pass (5/5)
✓ Lean builds work (separate configuration)
✓ Reduced complexity: 642 lines → 250 lines + 100 lines YAML
✓ No edge cases, no special handling

