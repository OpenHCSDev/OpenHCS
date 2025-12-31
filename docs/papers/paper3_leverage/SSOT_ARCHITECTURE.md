# Paper 3: SSOT Architecture (Practicing What We Preach)

## Architecture Overview

Paper 3 formalizes Single Source of Truth (SSOT) and leverage maximization. We practice what we preach by using SSOT architecture for the paper itself.

### OLD Architecture (WRONG - violated SSOT):
```
leverage_paper.tex      (1378 lines) - duplicated content
leverage_toplas.tex     (1378 lines) - duplicated content
leverage_arxiv.tex      (1387 lines) - duplicated content

DOF = 3 (three independent files)
M(change content) = 3 (must edit all three files)
Leverage = 2 formats / 3 files = 0.67 (antipattern!)
```

### NEW Architecture (CORRECT - SSOT):
```
content.tex             (1325 lines) - SINGLE SOURCE OF TRUTH
leverage_toplas.tex     (37 lines)   - wrapper: \input{content.tex}
leverage_arxiv.tex      (67 lines)   - wrapper: \input{content.tex}

DOF = 1 (only content.tex is independent)
M(change content) = 1 (edit content.tex, wrappers derive automatically)
Leverage = 2 formats / 1 file = 2.0 (optimal!)
```

## File Structure

```
/home/ts/code/projects/openhcs-sequential/docs/papers/paper3_leverage/latex/
├── content.tex              # SINGLE SOURCE OF TRUTH (1325 lines)
│                            # Contains: abstract → appendices
│                            # All content lives here
│
├── leverage_toplas.tex      # TOPLAS wrapper (37 lines)
│                            # Sets up: acmtoplas class
│                            # Includes: \input{content.tex}
│
└── leverage_arxiv.tex       # arXiv wrapper (67 lines)
                             # Sets up: article class + formatting
                             # Includes: \input{content.tex}
```

## Leverage Analysis

### Capabilities
Both versions provide:
1. Complete paper content (abstract through appendices)
2. Formatted for target venue (TOPLAS or arXiv)

### Degrees of Freedom
**Before refactor**: DOF = 3 (must maintain 3 separate files)
**After refactor**: DOF = 1 (only `content.tex` is source of truth)

### Leverage Improvement
```
L_before = 2 capabilities / 3 DOF = 0.67
L_after  = 2 capabilities / 1 DOF = 2.00

Improvement: 2.00 / 0.67 = 3× leverage increase
```

### Error Probability
Assuming p = 0.01 (1% error rate per file):
```
P_error(before) = 1 - (1-0.01)³ ≈ 0.0297 (3.0%)
P_error(after)  = 1 - (1-0.01)¹ ≈ 0.0100 (1.0%)

Error reduction: 3.0% → 1.0% (3× improvement)
```

### Modification Complexity
To change content (e.g., fix typo, update theorem, add section):
```
M(change, before) = 3 (edit all three files)
M(change, after)  = 1 (edit content.tex only)

Modification cost reduction: 3×
```

## Theorem Validation

This architecture is an instance of **Theorem 5.1 (SSOT Leverage Dominance)**:

For structural fact (paper content) with n use sites (2 formats):
```
L(SSOT) / L(non-SSOT) = n = 2 (for TOPLAS + arXiv)
```

We could extend to more formats (conference version, journal version, blog post) and leverage would scale:
```
3 formats: L = 3/1 = 3
5 formats: L = 5/1 = 5
n formats: L = n/1 = n (unbounded!)
```

## Implementation Pattern

### content.tex (Source of Truth)
```latex
\begin{abstract}
...content...
\end{abstract}

\maketitle

\section{Introduction}
...content...

...all 8 sections...

\appendix
...appendices...

\bibliographystyle{ACM-Reference-Format}
\bibliography{references}

\end{document}
```

### leverage_toplas.tex (TOPLAS Wrapper)
```latex
\documentclass[acmtoplas,screen,review,anonymous]{acmart}

% TOPLAS-specific packages and settings
\usepackage{longtable}
\usepackage{booktabs}
...

% Theorem environments
\newtheorem{theorem}{Theorem}[section]
...

\begin{document}

\title{...}
\author{...}
\affiliation{...}

% DERIVE from single source
\input{content.tex}

\end{document}
```

### leverage_arxiv.tex (arXiv Wrapper)
```latex
\documentclass[11pt]{article}

% arXiv-specific packages and settings
\usepackage{geometry}
\usepackage{hyperref}
...

% Theorem environments (same as TOPLAS)
\newtheorem{theorem}{Theorem}[section]
...

\begin{document}

\title{...}
\author{...}

\maketitle

% DERIVE from single source
\input{content.tex}

\end{document}
```

## Consistency Guarantees

With SSOT architecture:

**Guaranteed consistent** (automatically synchronized):
- Abstract
- Introduction
- All theorem statements
- All proofs
- All sections
- All appendices
- Bibliography

**Format-specific** (independently maintained in wrappers):
- Document class
- Title/author formatting
- Package imports
- Margin settings
- Hyperlink colors

## Comparison to Papers 1 & 2

### Paper 1 Architecture (BEFORE refactor - should be updated)
```
toplas_version.tex      (6213 lines) - full duplicate
arxiv_version.tex       (6213 lines) - full duplicate

DOF = 2
M(change) = 2
Leverage = 1 (antipattern)
```

### Paper 2 Architecture (BEFORE refactor - should be updated)
```
ssot_paper.tex         (2432 lines) - full duplicate
ssot_arxiv.tex         (2432 lines) - full duplicate

DOF = 2
M(change) = 2
Leverage = 1 (antipattern)
```

### Paper 3 Architecture (CORRECT - exemplar)
```
content.tex            (1325 lines) - SINGLE SOURCE
leverage_toplas.tex    (37 lines)   - wrapper
leverage_arxiv.tex     (67 lines)   - wrapper

DOF = 1
M(change) = 1
Leverage = 2 (optimal)
```

**Recommendation**: Refactor Papers 1 & 2 to use same SSOT pattern.

## Metaprogramming Perspective

This is metaprogramming for LaTeX:
- **Source**: `content.tex` (definition)
- **Derivation**: `\input{content.tex}` (automatic inclusion)
- **Derived formats**: TOPLAS, arXiv (potentially: conference, journal, blog, slides...)

Analogous to:
- Python metaclass (source) auto-registering plugins (derivations)
- Single database schema (source) serving multiple APIs (derivations)
- One configuration source (source) with format-specific parsers (derivations)

## Empirical Results

**Before refactor**:
- Total lines: 3743 (1378 + 1378 + 1387)
- Maintenance burden: High (must sync 3 files)
- Error risk: P ≈ 3%

**After refactor**:
- Total lines: 1429 (1325 + 37 + 67)
- Lines saved: 3743 - 1429 = 2314 (61.8% reduction!)
- Maintenance burden: Low (edit one file)
- Error risk: P ≈ 1% (3× improvement)

## Conclusion

Paper 3 **practices the leverage principle it formalizes**:
- DOF = 1 (single source of truth)
- Leverage = 2 (two formats from one source)
- M(change) = 1 (constant modification complexity)
- Scalable to n formats with L = n

This is the **correct architecture** for maintaining multiple paper versions.

Papers 1 and 2 should be refactored to match this pattern.
