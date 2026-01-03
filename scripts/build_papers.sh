#!/bin/bash
# Unified build script for all three TOPLAS papers
# Usage: ./scripts/build_papers.sh [latex|markdown|lean|all] [paper1|paper2|paper3|all]
#
# Examples:
#   ./scripts/build_papers.sh all          # Build everything
#   ./scripts/build_papers.sh latex        # Build all LaTeX PDFs
#   ./scripts/build_papers.sh markdown     # Build all Markdown
#   ./scripts/build_papers.sh lean paper1  # Build Paper 1 Lean only

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
PAPERS_DIR="$REPO_ROOT/docs/papers"

GREEN='\033[0;32m'
BLUE='\033[0;34m'
RED='\033[0;31m'
NC='\033[0m'

log() { echo -e "${BLUE}[build]${NC} $1"; }
success() { echo -e "${GREEN}[build]${NC} $1"; }
error() { echo -e "${RED}[build]${NC} $1"; }

# Auto-update publication and copyright dates.
# Defaults to today's date/year but can be overridden with:
#   PAPER_PUBLICATION_DATE="January 2, 2026"
#   PAPER_COPYRIGHT_YEAR=2026
update_paper_date() {
    local paper_dir="$1"
    local publication_date="${PAPER_PUBLICATION_DATE:-$(date '+%B %-d, %Y')}"
    local derived_year
    derived_year=$(echo "$publication_date" | grep -oE '[0-9]{4}' | tail -1)
    local copyright_year="${PAPER_COPYRIGHT_YEAR:-${derived_year:-$(date '+%Y')}}"

    find "$paper_dir" -name "main.tex" -o -name "*_arxiv.tex" | while read -r tex_file; do
        sed -i "s/\\\\date{[^}]*}/\\\\date{$publication_date}/" "$tex_file"
        sed -i "s/\\(\\\\textcopyright[[:space:]]*\\)[0-9]\\{4\\}/\\1${copyright_year}/g" "$tex_file"
        sed -i "s/\\\\copyrightyear{[^}]*}/\\\\copyrightyear{${copyright_year}}/" "$tex_file"
        sed -i "s/\\\\acmYear{[^}]*}/\\\\acmYear{${copyright_year}}/" "$tex_file"
    done
    log "Updated publication date ($publication_date) and copyright year ($copyright_year) in $paper_dir"
}

build_latex_paper1() {
    log "Building Paper 1 LaTeX..."
    update_paper_date "$PAPERS_DIR/paper1_typing_discipline"
    cd "$PAPERS_DIR/paper1_typing_discipline/toplas"
    pdflatex -interaction=nonstopmode main.tex > /dev/null 2>&1 || true
    success "Paper 1 PDF → toplas/main.pdf"
}

build_latex_paper2() {
    log "Building Paper 2 LaTeX..."
    update_paper_date "$PAPERS_DIR/paper2_ssot"
    cd "$PAPERS_DIR/paper2_ssot/toplas"
    pdflatex -interaction=nonstopmode main.tex > /dev/null 2>&1 || true
    success "Paper 2 PDF → toplas/main.pdf"
}

build_latex_paper3() {
    log "Building Paper 3 LaTeX..."
    update_paper_date "$PAPERS_DIR/paper3_leverage"
    cd "$PAPERS_DIR/paper3_leverage/latex"
    pdflatex -interaction=nonstopmode leverage_arxiv.tex > /dev/null 2>&1 || true
    success "Paper 3 PDF → latex/leverage_arxiv.pdf"
}

build_latex_paper4() {
    log "Building Paper 4 LaTeX..."
    update_paper_date "$PAPERS_DIR/paper4_decision_quotient"
    cd "$PAPERS_DIR/paper4_decision_quotient/latex"
    pdflatex -interaction=nonstopmode decision_quotient_arxiv.tex > /dev/null 2>&1 || true
    success "Paper 4 PDF → latex/decision_quotient_arxiv.pdf"
}

build_latex_paper5() {
    log "Building Paper 5 LaTeX..."
    update_paper_date "$PAPERS_DIR/paper5_credibility"
    cd "$PAPERS_DIR/paper5_credibility/latex"
    pdflatex -interaction=nonstopmode credibility_arxiv.tex > /dev/null 2>&1 || true
    success "Paper 5 PDF → latex/credibility_arxiv.pdf"
}

build_lean_paper1() {
    log "Building Paper 1 Lean..."
    cd "$PAPERS_DIR/paper1_typing_discipline/proofs"
    lake build 2>&1 | tail -1
    success "Paper 1 Lean complete"
}

build_lean_paper2() {
    log "Building Paper 2 Lean..."
    cd "$PAPERS_DIR/paper2_ssot/proofs"
    lake build 2>&1 | tail -1
    success "Paper 2 Lean complete"
}

build_lean_paper3() {
    log "Building Paper 3 Lean..."
    cd "$PAPERS_DIR/paper3_leverage/proofs"
    lake build 2>&1 | tail -1
    success "Paper 3 Lean complete"
}

build_lean_paper4() {
    log "Building Paper 4 Lean..."
    cd "$PAPERS_DIR/paper4_decision_quotient/proofs"
    lake build 2>&1 | tail -1
    success "Paper 4 Lean complete"
}

build_lean_paper5() {
    log "Building Paper 5 Lean..."
    cd "$PAPERS_DIR/paper5_credibility/proofs"
    lake build 2>&1 | tail -1
    success "Paper 5 Lean complete"
}

build_markdown() {
    "$SCRIPT_DIR/build_paper_markdown.sh" "${1:-all}"
}

# Dispatch based on arguments
BUILD_TYPE="${1:-all}"
PAPER="${2:-all}"

case "$BUILD_TYPE" in
    latex)
        case "$PAPER" in
            paper1) build_latex_paper1 ;;
            paper2) build_latex_paper2 ;;
            paper3) build_latex_paper3 ;;
            all) build_latex_paper1; build_latex_paper2; build_latex_paper3 ;;
        esac
        ;;
    markdown|md)
        build_markdown "$PAPER"
        ;;
    lean)
        case "$PAPER" in
            paper1) build_lean_paper1 ;;
            paper2) build_lean_paper2 ;;
            paper3) build_lean_paper3 ;;
            all) build_lean_paper1; build_lean_paper2; build_lean_paper3 ;;
        esac
        ;;
    all)
        log "Building all papers (Lean + LaTeX + Markdown)..."
        echo ""
        build_lean_paper1; build_lean_paper2; build_lean_paper3
        echo ""
        build_latex_paper1; build_latex_paper2; build_latex_paper3
        echo ""
        build_markdown all
        echo ""
        success "All builds complete!"
        ;;
    *)
        echo "Usage: $0 [latex|markdown|lean|all] [paper1|paper2|paper3|all]"
        exit 1
        ;;
esac
