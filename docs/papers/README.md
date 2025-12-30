# Nominal Typing Paper

## Main Paper

**`nominal_typing_proof_v3_scp.md`** - The current submission-ready paper.

- **Title**: *Nominal Typing Strictly Dominates Structural Typing for Object-Oriented Systems with Inheritance*
- **Target**: TOPLAS (ACM Transactions on Programming Languages and Systems)
- **Status**: Ready for review

Generated outputs:
- `nominal_typing_proof_v3_scp.pdf` - PDF via pandoc/xelatex
- `nominal_typing_proof_v3_scp.html` - HTML version

### Regenerating PDF

```bash
cd docs/papers
pandoc nominal_typing_proof_v3_scp.md -o nominal_typing_proof_v3_scp.pdf \
  --pdf-engine=xelatex \
  -V geometry:margin=1in \
  -V mainfont="DejaVu Serif" \
  -V sansfont="DejaVu Sans" \
  -V monofont="DejaVu Sans Mono" \
  --toc --number-sections
```

## Machine-Checked Proofs

The Lean 4 proofs are in `/proofs/` at the repository root:

| Module | Lines | Theorems | Purpose |
|--------|-------|----------|---------|
| `abstract_class_system.lean` | 1488 | 75 | Core formalization: three-axis model, dominance, complexity |
| `nominal_resolution.lean` | 556 | 18 | Resolution, capability exhaustiveness, adapter amortization |
| `discipline_migration.lean` | 142 | 11 | Discipline vs migration separation |
| `context_formalization.lean` | 215 | 7 | Greenfield/retrofit classification |
| **Total** | **2401** | **111** | 0 `sorry` placeholders |

### Building Proofs

```bash
cd proofs
lake build
```

## Directory Structure

```
docs/papers/
├── nominal_typing_proof_v3_scp.md   # Main paper (source)
├── nominal_typing_proof_v3_scp.pdf  # Main paper (PDF)
├── nominal_typing_proof_v3_scp.html # Main paper (HTML)
├── README.md                        # This file
├── archive/                         # Previous versions
│   ├── nominal_typing_proof_v1_draft.md
│   ├── nominal_typing_complete.md
│   └── nominal_typing_complete.pdf
├── working/                         # Working documents
│   ├── nominal_proof_v3_review.md
│   ├── nominal_proof_v3_revision_drafts.md
│   ├── restructuring_plan.md
│   ├── restructuring_plan_toplas.md
│   ├── scp_submission_metadata.md
│   └── mixins_and_zen_additions.md
└── references/                      # External papers
    ├── Formal Comparisons of Nominal vs Structural Typing (2000–2025).pdf
    └── Formal Proofs of Complexity Reduction via Metaprogramming.pdf

proofs/                              # Lean 4 proofs (at repo root)
├── abstract_class_system.lean
├── nominal_resolution.lean
├── discipline_migration.lean
├── context_formalization.lean
├── lakefile.lean
├── lean-toolchain
└── lake-manifest.json
```

