# Paper 2 IT Reframing Status

## Completed Reframing ✓

### Abstract (`content/abstract.tex`)
- **OLD**: "Epistemic Foundation" → DOF = 1 → Software as Instance
- **NEW**: Information system encoding → Optimal rate theorem → Applications across domains
- **Key changes**:
  - Lead with encoding theory, not epistemology
  - Rissanen's MDL, Slepian-Wolf, zero-error capacity connections
  - Software as ONE instantiation among distributed databases, configuration systems, version control

### Introduction (`content/01_introduction.tex`)
- **OLD**: "The Epistemic Problem" → "Software as Instance"
- **NEW**: "The Encoding Problem" → "Optimal Rate Theorem" → "Applications Across Domains"
- **Key sections reframed**:
  - §1.1: Encoding problem (not epistemic)
  - §1.2: Optimal rate (DOF = 1 as IT result)
  - §1.3: Applications (databases, version control, config, software)
  - §1.4: Connection to classical IT (Shannon, Slepian-Wolf, zero-error capacity, rate-distortion)
  - §1.5: Realizability (computational requirements)
  - §1.6: Paper organization (IT first, applications second)
  - §1.7: Core theorems (IT framing)

## Remaining Content Files (Need Reframing)

### Foundation Sections
1. **`content/02_foundations.tex`** - Encoding model formalization
   - Change: "Edit space" → "Encoding space"
   - Change: "Facts in software" → "Facts in encoding systems"
   - Keep formalism, reframe motivation

2. **`content/03_ssot.tex`** - SSOT definition and optimality
   - Change: "SSOT" → "Optimal encoding rate"
   - Emphasize uniqueness (MDL parallel)
   - Keep DOF = 1 as information-theoretic optimum

3. **`content/04_requirements.tex`** - Language requirements
   - Change: "Language requirements" → "Realizability constraints for computational systems"
   - Frame hooks + introspection as information-theoretic necessities
   - Programming languages are ONE realization domain

### Evaluation and Bounds
4. **`content/05_evaluation.tex`** - Language evaluation
   - Change: Lead with formal criteria, not language names
   - Frame as "computational system evaluation against realizability criteria"
   - Python/Java/Rust as examples, not the focus

5. **`content/06_bounds.tex`** - Complexity bounds
   - Already IT-framed (O(1) vs Ω(n))
   - May need: connect to rate-distortion literature
   - Emphasize: modification complexity vs encoding rate tradeoff

### Applications
6. **`content/07_empirical.tex`** - Empirical validation
   - Keep case studies but frame as "computational realization validation"
   - OpenHCS as example of DOF reduction in practice

7. **`content/08_related.tex`** - Related work
   - Reorganize to prioritize IT literature:
     1. Encoding theory (MDL, Slepian-Wolf, zero-error)
     2. Distributed systems (consistency, replication)
     3. Software engineering (DRY, formal methods)

### Back Matter
8. **`content/09_conclusion.tex`** - Conclusion
   - Reframe contributions: IT theory first, software instantiation second
   - Future work: other encoding domains

9. **`content/10_rebuttals.tex`** - Preemptive rebuttals
   - Keep technical rebuttals
   - May remove software-specific objections

10. **`content/11_lean_proofs.tex`** - Lean appendix
    - Mostly unchanged
    - Emphasize: formalization of encoding theory, not just software

## Key Reframing Pattern (from Paper 1)

Paper 1 transformation:
```
Typing Discipline (Programming Focus)
↓
Classification Systems (Universal Focus)
```

Paper 2 should follow:
```
SSOT/DRY (Software Focus)
↓
Optimal Encoding Under Coherence (IT Focus)
```

## Concrete Terminology Changes

| Software-First | IT-First |
|----------------|----------|
| "Single Source of Truth" | "Optimal encoding rate" |
| "DRY principle" | "Minimum description length for mutable facts" |
| "Codebase" | "Encoding system" |
| "Structural facts" | "System facts" or "Configuration facts" |
| "Programming language" | "Computational realization" |
| "Language requirements" | "Realizability constraints" |
| "Definition-time hooks" | "Definition-time computation capability" |
| "Software engineering" | "Computational systems" (when general) |

## Citations to Add (IT Literature)

- Shannon (1948) - Source coding theorem
- Slepian-Wolf (1973) - Distributed source coding
- Rissanen (1978) - MDL principle
- Grünwald (2007) - MDL theory
- Körner (1973) - Zero-error capacity
- Cover & Thomas (2006) - Rate-distortion theory
- Brewer (2000) - CAP theorem (distributed systems)

## Build Status

✓ Abstract reframed
✓ Introduction reframed
✓ PDF compiles (31 pages, 390KB)
✓ Build system recognizes paper2_it

## Next Steps

1. Reframe remaining content files (02-11)
2. Update references.bib with IT citations
3. Build full paper with bibtex
4. Review for consistency
5. Compare to Paper 1 JSAIT for pattern alignment
