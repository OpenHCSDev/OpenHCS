# arXiv Packaging - Quick Start

## One Command to Package Everything

```bash
python3 scripts/build_papers.py arxiv all
```

This creates 5 complete arXiv submission packages:

```
paper1_typing_discipline_arxiv.tar.gz    (676K)
paper2_ssot_arxiv.tar.gz                 (523K)
paper3_leverage_arxiv.tar.gz             (599K)
paper4_decision_quotient_arxiv.tar.gz    (593K)
paper5_credibility_arxiv.tar.gz          (405K)
```

## What's Inside Each Package

```
paper{N}_{name}/
  ├── main.pdf                    # Compiled paper
  ├── paper{N}_{name}.md          # Full markdown
  └── proofs/
      ├── PrintAxioms.lean
      ├── abstract_class_system.lean
      ├── axis_framework.lean
      ├── ... (all Lean source files)
      ├── lakefile.lean
      ├── lean-toolchain
      └── lake-manifest.json
```

## Common Commands

```bash
# Package all papers
python3 scripts/build_papers.py arxiv all

# Package specific paper
python3 scripts/build_papers.py arxiv paper1

# Build everything (markdown + PDF + arxiv)
python3 scripts/build_papers.py all

# Build specific format
python3 scripts/build_papers.py markdown all
python3 scripts/build_papers.py latex all
python3 scripts/build_papers.py lean all
```

## Extract a Package

```bash
tar -xzf paper1_typing_discipline_arxiv.tar.gz
cd paper1_typing_discipline
ls -la
```

## Features

✓ **Complete**: PDF + Markdown + Lean proofs
✓ **Clean**: Build artifacts excluded
✓ **Compressed**: Efficient tar.gz format
✓ **Ready**: Direct arXiv submission
✓ **Uniform**: All papers identical structure

## File Locations

All packages are in:
```
docs/papers/paper{N}_{name}/paper{N}_{name}_arxiv.tar.gz
```

Example:
```
docs/papers/paper1_typing_discipline/paper1_typing_discipline_arxiv.tar.gz
```

## Next Steps

1. Extract package: `tar -xzf paper1_typing_discipline_arxiv.tar.gz`
2. Review contents
3. Submit to arXiv
4. Share with collaborators
5. Archive in releases

Each package is self-contained and requires no external dependencies.

