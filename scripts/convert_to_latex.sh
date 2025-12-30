#!/bin/bash
# Convert Markdown paper to LaTeX for arXiv/TOPLAS submission

set -e

PAPER_MD="docs/papers/nominal_typing_proof.md"
OUTPUT_DIR="docs/papers/latex"
ARXIV_TEX="$OUTPUT_DIR/arxiv_version.tex"
TOPLAS_TEX="$OUTPUT_DIR/toplas_version.tex"

mkdir -p "$OUTPUT_DIR"

echo "Step 1: Converting Markdown to LaTeX with pandoc..."
pandoc "$PAPER_MD" \
    -o "$ARXIV_TEX" \
    --standalone \
    --from markdown \
    --to latex \
    --number-sections \
    --bibliography=docs/papers/references.bib \
    --citeproc

echo "Step 2: Creating TOPLAS version with ACM template..."
cp "$ARXIV_TEX" "$TOPLAS_TEX"

echo "Step 3: Conversion complete!"
echo ""
echo "Next steps:"
echo "1. Install Ollama: curl -fsSL https://ollama.com/install.sh | sh"
echo "2. Pull a model: ollama pull qwen2.5-coder:32b"
echo "3. Run cleanup script: ./scripts/cleanup_latex_with_ollama.sh"
echo ""
echo "Files created:"
echo "  - $ARXIV_TEX (arXiv version)"
echo "  - $TOPLAS_TEX (TOPLAS version)"

