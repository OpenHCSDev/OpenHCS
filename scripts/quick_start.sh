#!/bin/bash
# Quick start script - fully automated LaTeX conversion

set -e

echo "=========================================="
echo "LaTeX Conversion - Fully Automated"
echo "=========================================="
echo ""

# Check if pandoc is installed
if ! command -v pandoc &> /dev/null; then
    echo "Error: pandoc not installed."
    echo ""
    echo "Install with:"
    echo "  Ubuntu/Debian: sudo apt install pandoc"
    echo "  macOS: brew install pandoc"
    echo ""
    exit 1
fi

# Check if pdflatex is installed
if ! command -v pdflatex &> /dev/null; then
    echo "Warning: pdflatex not installed. PDF compilation will be skipped."
    echo ""
    echo "Install with:"
    echo "  Ubuntu/Debian: sudo apt install texlive-latex-base texlive-latex-extra"
    echo "  macOS: brew install --cask mactex"
    echo ""
    SKIP_COMPILE=1
else
    SKIP_COMPILE=0
fi

echo "Step 1/4: Converting Markdown to LaTeX with pandoc..."
pandoc docs/papers/nominal_typing_proof.md \
    -o docs/papers/latex/initial_conversion.tex \
    --standalone \
    --from markdown \
    --to latex \
    --number-sections

echo "✓ Pandoc conversion complete"
echo ""

echo "Step 2/4: Creating arXiv version..."
python3 scripts/convert_paper_to_latex.py \
    docs/papers/latex/initial_conversion.tex \
    docs/papers/latex/arxiv_version.tex \
    arxiv

python3 scripts/fix_latex_structure.py docs/papers/latex/arxiv_version.tex
python3 scripts/fix_latex_errors.py docs/papers/latex/arxiv_version.tex

echo "✓ arXiv version created"
echo ""

echo "Step 3/4: Creating TOPLAS version..."
python3 scripts/convert_paper_to_latex.py \
    docs/papers/latex/initial_conversion.tex \
    docs/papers/latex/toplas_version.tex \
    toplas

python3 scripts/fix_latex_structure.py docs/papers/latex/toplas_version.tex
python3 scripts/fix_latex_errors.py docs/papers/latex/toplas_version.tex

echo "✓ TOPLAS version created"
echo ""

if [ $SKIP_COMPILE -eq 0 ]; then
    echo "Step 4/4: Compiling arXiv PDF..."
    cd docs/papers/latex
    pdflatex -interaction=nonstopmode arxiv_version.tex > /dev/null 2>&1
    cd ../../..

    if [ -f docs/papers/latex/arxiv_version.pdf ]; then
        PDF_SIZE=$(ls -lh docs/papers/latex/arxiv_version.pdf | awk '{print $5}')
        PDF_PAGES=$(pdfinfo docs/papers/latex/arxiv_version.pdf 2>/dev/null | grep Pages | awk '{print $2}')
        echo "✓ PDF compiled successfully ($PDF_PAGES pages, $PDF_SIZE)"
    else
        echo "⚠ PDF compilation had errors (check arxiv_version.log)"
    fi
else
    echo "Step 4/4: Skipping PDF compilation (pdflatex not installed)"
fi

echo ""
echo "=========================================="
echo "✓ Conversion Complete!"
echo "=========================================="
echo ""
echo "Files created:"
echo "  - docs/papers/latex/arxiv_version.tex"
echo "  - docs/papers/latex/arxiv_version.pdf"
echo "  - docs/papers/latex/toplas_version.tex"
echo "  - docs/papers/latex/references.bib"
echo ""
echo "Next steps:"
echo "  1. Read: cat docs/papers/latex/DONE.md"
echo "  2. Add your name/affiliation to arxiv_version.tex"
echo "  3. Review theorems and proofs"
echo "  4. Submit to arXiv!"
echo ""
echo "Estimated review time: 2-3 hours"
echo "Cost: \$0 (all local tools)"
echo ""

