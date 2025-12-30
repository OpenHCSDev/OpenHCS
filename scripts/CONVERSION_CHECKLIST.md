# LaTeX Conversion Checklist

## Automated Steps (Run These Scripts)

### 1. Install Dependencies
```bash
# Install pandoc (if not already installed)
sudo apt install pandoc  # Ubuntu/Debian
# or
brew install pandoc      # macOS

# Install Ollama
curl -fsSL https://ollama.com/install.sh | sh

# Pull the model (32GB model, needs ~20GB RAM)
ollama pull qwen2.5-coder:32b

# Alternative: smaller model if RAM limited
ollama pull qwen2.5-coder:7b
```

### 2. Run Conversion Scripts
```bash
# Make scripts executable
chmod +x scripts/convert_to_latex.sh
chmod +x scripts/cleanup_latex_with_ollama.sh

# Step 1: Convert Markdown to LaTeX
./scripts/convert_to_latex.sh

# Step 2: Clean up with Ollama
./scripts/cleanup_latex_with_ollama.sh
```

**Time estimate:** 10-15 minutes (mostly Ollama processing)

---

## Manual Review Checklist (2-3 hours)

### Critical Sections to Review

#### 1. Theorems and Proofs (HIGH PRIORITY)
- [ ] All theorem environments properly formatted
- [ ] All proofs have \begin{proof} ... \end{proof}
- [ ] Labels are correct (e.g., \label{thm:3.13})
- [ ] Cross-references work (\ref{thm:3.13})

**Check these theorems specifically:**
- [ ] Theorem 3.13 (Provenance Impossibility)
- [ ] Theorem 3.19 (Capability Gap)
- [ ] Theorem 3.24 (Duck Typing Lower Bound)
- [ ] Theorem 2.10d (Duck Typing Incoherence)
- [ ] Theorem 2.10j (Protocol Dominance)

#### 2. Math Rendering (HIGH PRIORITY)
- [ ] All inline math renders correctly
- [ ] All display math renders correctly
- [ ] Special symbols work: $\blacksquare$, $\Omega$, $\subseteq$
- [ ] Set notation: $\mathcal{C}_B$, $\{N, B, S\}$

#### 3. Tables (MEDIUM PRIORITY)
- [ ] All tables converted to tabular environment
- [ ] Table captions added
- [ ] Tables are readable (not too wide)

**Key tables to check:**
- [ ] Table 2.1: Cross-Language Instantiation
- [ ] Table 2.2: Generic Types Across Languages
- [ ] Capability comparison tables

#### 4. Code Blocks (MEDIUM PRIORITY)
- [ ] Python code blocks use lstlisting
- [ ] Lean code blocks use lstlisting
- [ ] Code is readable (font size, line breaks)

#### 5. Citations (HIGH PRIORITY)
- [ ] Create references.bib file
- [ ] All citations converted to \cite{}
- [ ] Bibliography compiles

**Key citations to add:**
- [ ] Cardelli (1988)
- [ ] Malayeri & Aldrich (2008, 2009)
- [ ] Abdelgawad (2014, 2016)
- [ ] Liskov & Wing (1994)
- [ ] Barrett et al. (1996) - C3 linearization

#### 6. Document Metadata
- [ ] Add your name
- [ ] Add your affiliation
- [ ] Add your email
- [ ] Add keywords
- [ ] Add ACM CCS concepts (for TOPLAS)

---

## Compilation Test

### arXiv Version
```bash
cd docs/papers/latex
pdflatex arxiv_version.tex
bibtex arxiv_version
pdflatex arxiv_version.tex
pdflatex arxiv_version.tex
```

**Expected output:** arxiv_version.pdf (~60 pages)

### TOPLAS Version
```bash
cd docs/papers/latex
pdflatex toplas_version.tex
bibtex toplas_version
pdflatex toplas_version.tex
pdflatex toplas_version.tex
```

**Expected output:** toplas_version.pdf (~60 pages)

---

## Common Issues and Fixes

### Issue 1: "Undefined control sequence \blacksquare"
**Fix:** Add to preamble:
```latex
\usepackage{amssymb}
```

### Issue 2: Tables too wide
**Fix:** Use `\small` or `\footnotesize`:
```latex
\begin{table}
\small
\begin{tabular}{...}
...
\end{tabular}
\end{table}
```

### Issue 3: Code blocks overflow
**Fix:** Add to lstset:
```latex
\lstset{
  basicstyle=\ttfamily\footnotesize,
  breaklines=true
}
```

### Issue 4: Missing citations
**Fix:** Create references.bib with entries like:
```bibtex
@article{cardelli1988,
  author = {Cardelli, Luca},
  title = {A Semantics of Multiple Inheritance},
  journal = {Information and Computation},
  year = {1988}
}
```

---

## Final Checks Before Submission

### arXiv Submission
- [ ] PDF compiles without errors
- [ ] All figures/tables visible
- [ ] Math renders correctly
- [ ] File size < 50MB
- [ ] Include .tex source + .bib file

### TOPLAS Submission
- [ ] PDF compiles with ACM template
- [ ] Anonymous version (no author names)
- [ ] Line numbers enabled (review mode)
- [ ] All sections present
- [ ] Cover letter prepared

---

## Estimated Time Breakdown

| Task | Time |
|------|------|
| Install dependencies | 10 min |
| Run conversion scripts | 10 min |
| Review theorems/proofs | 1 hour |
| Review math/tables | 30 min |
| Create references.bib | 30 min |
| Fix compilation errors | 30 min |
| Final review | 30 min |
| **TOTAL** | **3-4 hours** |

**vs. manual conversion: 2-3 days**

---

## Cost Comparison

| Approach | Cost | Time |
|----------|------|------|
| Manual conversion | $0 | 2-3 days |
| Automated (pandoc + Ollama) | $0 | 3-4 hours |
| Using Claude for everything | ~$50-100 | 1 hour |

**Recommendation:** Use automated approach. Save Claude for final review of critical sections.

