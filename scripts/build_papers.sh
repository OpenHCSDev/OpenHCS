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

build_latex_paper1() {
    log "Building Paper 1 LaTeX..."
    cd "$PAPERS_DIR/paper1_typing_discipline/toplas"
    pdflatex -interaction=nonstopmode main.tex > /dev/null 2>&1 || true
    success "Paper 1 PDF → toplas/main.pdf"
}

build_latex_paper2() {
    log "Building Paper 2 LaTeX..."
    cd "$PAPERS_DIR/paper2_ssot/toplas"
    pdflatex -interaction=nonstopmode main.tex > /dev/null 2>&1 || true
    success "Paper 2 PDF → toplas/main.pdf"
}

build_latex_paper3() {
    log "Building Paper 3 LaTeX..."
    cd "$PAPERS_DIR/paper3_leverage/latex"
    pdflatex -interaction=nonstopmode leverage_arxiv.tex > /dev/null 2>&1 || true
    success "Paper 3 PDF → latex/leverage_arxiv.pdf"
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

