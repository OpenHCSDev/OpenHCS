#!/bin/bash
# Unified build + release script for all five papers
# Builds LaTeX, Lean proofs, and packages for arXiv/Zenodo
#
# Usage: ./scripts/build_papers.sh [command] [paper]
#
# Commands:
#   release  - Full build: Lean + LaTeX + package into releases/ (default)
#   latex    - Build LaTeX PDFs only
#   lean     - Build Lean proofs only
#   package  - Package for arXiv (flatten, tarball)
#
# Paper:
#   paper1|paper2|paper3|paper4|paper5|all (default: all)
#
# Examples:
#   ./scripts/build_papers.sh                    # Full release build for all
#   ./scripts/build_papers.sh release paper3    # Full release for paper3
#   ./scripts/build_papers.sh latex             # LaTeX only, all papers
#   ./scripts/build_papers.sh lean paper1       # Lean only for paper1

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
PAPERS_DIR="$REPO_ROOT/docs/papers"
BUILD_DIR="$REPO_ROOT/build/arxiv"

# Use global Lake cache to avoid re-downloading Mathlib per paper
export LAKE_HOME="${LAKE_HOME:-$HOME/.elan/.lake}"

GREEN='\033[0;32m'
BLUE='\033[0;34m'
RED='\033[0;31m'
YELLOW='\033[0;33m'
NC='\033[0m'

log() { echo -e "${BLUE}[build]${NC} $1"; }
success() { echo -e "${GREEN}✓${NC} $1"; }
error() { echo -e "${RED}✗${NC} $1"; exit 1; }
warn() { echo -e "${YELLOW}!${NC} $1"; }

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



# Paper configurations: name|main_tex|output_pdf
declare -A PAPER_CONFIG=(
    [paper1]="paper1_typing_discipline|latex/main.tex|main.pdf"
    [paper2]="paper2_ssot|latex/main.tex|main.pdf"
    [paper3]="paper3_leverage|latex/leverage_arxiv.tex|leverage_arxiv.pdf"
    [paper4]="paper4_decision_quotient|latex/decision_quotient_arxiv.tex|decision_quotient_arxiv.pdf"
    [paper5]="paper5_credibility|latex/credibility_arxiv.tex|credibility_arxiv.pdf"
)

build_latex() {
    local paper="$1"
    local config="${PAPER_CONFIG[$paper]}"
    IFS='|' read -r dir tex_path pdf_name <<< "$config"

    local paper_dir="$PAPERS_DIR/$dir"
    local tex_dir="$(dirname "$paper_dir/$tex_path")"
    local tex_file="$(basename "$tex_path")"

    log "Building $paper LaTeX..."
    update_paper_date "$paper_dir"
    cd "$tex_dir"
    if pdflatex -interaction=batchmode "$tex_file" > /tmp/latex_$$.log 2>&1; then
        success "$paper PDF built"
    else
        warn "$paper PDF built (with warnings - check /tmp/latex_$$.log)"
    fi
}

build_lean() {
    local paper="$1"
    local config="${PAPER_CONFIG[$paper]}"
    IFS='|' read -r dir _ _ <<< "$config"

    local proofs_dir="$PAPERS_DIR/$dir/proofs"
    if [[ ! -d "$proofs_dir" ]]; then
        warn "$paper has no proofs directory, skipping"
        return
    fi

    log "Building $paper Lean proofs..."
    cd "$proofs_dir"
    lake build
    success "$paper Lean complete"
}

package_paper() {
    local paper="$1"
    local config="${PAPER_CONFIG[$paper]}"
    IFS='|' read -r dir tex_path pdf_name <<< "$config"

    local paper_dir="$PAPERS_DIR/$dir"
    local tex_dir="$(dirname "$paper_dir/$tex_path")"
    local tex_file="$(basename "$tex_path")"
    local releases_dir="$paper_dir/releases"
    local out_dir="$BUILD_DIR/$dir"

    log "Packaging $paper..."

    mkdir -p "$releases_dir" "$out_dir"

    # Build PDF with proper bibliography passes
    cd "$tex_dir"
    pdflatex -interaction=batchmode "$tex_file" > /tmp/latex_$$.log 2>&1 || true
    if [[ -f "${tex_file%.tex}.aux" ]] && grep -q "\\\\citation" "${tex_file%.tex}.aux" 2>/dev/null; then
        bibtex "${tex_file%.tex}" >> /tmp/latex_$$.log 2>&1 || true
        pdflatex -interaction=batchmode "$tex_file" >> /tmp/latex_$$.log 2>&1 || true
    fi
    pdflatex -interaction=batchmode "$tex_file" >> /tmp/latex_$$.log 2>&1 || true

    # Copy PDF to releases
    if [[ -f "$pdf_name" ]]; then
        cp "$pdf_name" "$releases_dir/$paper.pdf"
        success "$paper.pdf → releases/"
    fi

    # Copy sources for arXiv package
    cp "$tex_dir"/*.tex "$out_dir/" 2>/dev/null || true
    cp "$tex_dir"/*.bib "$out_dir/" 2>/dev/null || true
    cp "$tex_dir"/*.bbl "$out_dir/" 2>/dev/null || true
    cp "$tex_dir"/*.cls "$out_dir/" 2>/dev/null || true
    cp "$tex_dir"/*.sty "$out_dir/" 2>/dev/null || true

    # Copy Lean proofs if present
    local proofs_dir="$paper_dir/proofs"
    if [[ -d "$proofs_dir" ]]; then
        rsync -a \
            --exclude '.lake' \
            --exclude 'build' \
            --exclude 'lake-packages' \
            --exclude '*.olean' \
            "$proofs_dir"/ "$out_dir/proofs/"
    fi

    # Create arXiv tarball
    local tarball="$releases_dir/${paper}_arxiv.tar.gz"
    (cd "$out_dir" && tar -czf "$tarball" \
        --exclude='*.pdf' \
        --exclude='*.aux' \
        --exclude='*.log' \
        --exclude='*.out' \
        --exclude='*.toc' \
        --exclude='*.fls' \
        --exclude='*.fdb_latexmk' \
        .)
    success "${paper}_arxiv.tar.gz → releases/"
}

release_paper() {
    local paper="$1"
    build_lean "$paper"
    build_latex "$paper"
    package_paper "$paper"
}

run_for_papers() {
    local cmd="$1"
    local paper="$2"

    if [[ "$paper" == "all" ]]; then
        for p in paper1 paper2 paper3 paper4 paper5; do
            $cmd "$p"
        done
    else
        $cmd "$paper"
    fi
}

# Dispatch
COMMAND="${1:-release}"
PAPER="${2:-all}"

case "$COMMAND" in
    release)
        log "=== Full Release Build ==="
        rm -rf "$BUILD_DIR"
        mkdir -p "$BUILD_DIR"
        run_for_papers release_paper "$PAPER"
        echo ""
        success "Release complete! Check docs/papers/*/releases/"
        ;;
    latex)
        run_for_papers build_latex "$PAPER"
        ;;
    lean)
        run_for_papers build_lean "$PAPER"
        ;;
    package)
        rm -rf "$BUILD_DIR"
        mkdir -p "$BUILD_DIR"
        run_for_papers package_paper "$PAPER"
        ;;
    *)
        echo "Usage: $0 [release|latex|lean|package] [paper1|paper2|paper3|paper4|paper5|all]"
        echo ""
        echo "Commands:"
        echo "  release  - Full build: Lean + LaTeX + package (default)"
        echo "  latex    - Build LaTeX PDFs only"
        echo "  lean     - Build Lean proofs only"
        echo "  package  - Package for arXiv submission"
        exit 1
        ;;
esac
