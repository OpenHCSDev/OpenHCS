#!/bin/bash
# Build Markdown versions of all three TOPLAS papers
# Usage: ./scripts/build_paper_markdown.sh [paper1|paper2|paper3|all]
#
# Output goes to docs/papers/<paper>/markdown/
# Each paper gets a single combined .md file for easy sharing with LLMs

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"
PAPERS_DIR="$REPO_ROOT/docs/papers"

# Colors for output
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

log() {
    echo -e "${BLUE}[build-md]${NC} $1"
}

success() {
    echo -e "${GREEN}[build-md]${NC} $1"
}

# Check pandoc is installed
if ! command -v pandoc &> /dev/null; then
    echo "Error: pandoc is required but not installed."
    echo "Install with: sudo apt install pandoc"
    exit 1
fi

build_paper1() {
    log "Building Paper 1: Typing Discipline..."
    
    local PAPER_DIR="$PAPERS_DIR/paper1_typing_discipline"
    local CONTENT_DIR="$PAPER_DIR/shared/content"
    local OUT_DIR="$PAPER_DIR/markdown"
    local OUT_FILE="$OUT_DIR/paper1_typing_discipline.md"
    
    mkdir -p "$OUT_DIR"
    
    # Create header
    cat > "$OUT_FILE" << 'EOF'
# Paper 1: Typing Discipline Selection — When Nominal Beats Structural

**Status**: TOPLAS-ready | **Lean**: 2,666 lines, 127 theorems, 0 sorry

---

EOF
    
    # Concatenate all content files in order and convert
    local CONTENT_FILES=(
        "abstract.tex"
        "01_introduction.tex"
        "02_preliminaries.tex"
        "03_universal_dominance.tex"
        "04_core_theorems.tex"
        "05_case_studies.tex"
        "06_formalization.tex"
        "07_related_work.tex"
        "08_discussion.tex"
        "09_conclusion.tex"
    )
    
    local TEMP_TEX=$(mktemp)
    
    for file in "${CONTENT_FILES[@]}"; do
        if [[ -f "$CONTENT_DIR/$file" ]]; then
            cat "$CONTENT_DIR/$file" >> "$TEMP_TEX"
            echo -e "\n\n" >> "$TEMP_TEX"
        fi
    done
    
    # Convert with pandoc
    pandoc "$TEMP_TEX" -f latex -t markdown \
        --wrap=none \
        --columns=100 \
        -o "$OUT_DIR/content.md" 2>/dev/null || true
    
    cat "$OUT_DIR/content.md" >> "$OUT_FILE"
    rm -f "$TEMP_TEX" "$OUT_DIR/content.md"
    
    # Add footer with stats
    cat >> "$OUT_FILE" << 'EOF'

---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper1_typing_discipline/proofs/`
- Lines: 2,666
- Theorems: 127
- Sorry placeholders: 0

EOF
    
    success "Paper 1 → $OUT_FILE"
}

build_paper2() {
    log "Building Paper 2: SSOT Foundations..."
    
    local PAPER_DIR="$PAPERS_DIR/paper2_ssot"
    local CONTENT_DIR="$PAPER_DIR/shared/content"
    local OUT_DIR="$PAPER_DIR/markdown"
    local OUT_FILE="$OUT_DIR/paper2_ssot.md"
    
    mkdir -p "$OUT_DIR"
    
    # Create header
    cat > "$OUT_FILE" << 'EOF'
# Paper 2: Formal Foundations for the Single Source of Truth Principle

**Status**: TOPLAS-ready | **Lean**: 1,811 lines, 96 theorems, 0 sorry

---

EOF
    
    # Concatenate all content files in order
    local CONTENT_FILES=(
        "abstract.tex"
        "01_introduction.tex"
        "02_foundations.tex"
        "03_ssot.tex"
        "04_requirements.tex"
        "05_evaluation.tex"
        "06_bounds.tex"
        "07_case_studies.tex"
        "08_related_work.tex"
        "09_conclusion.tex"
        "10_rebuttals.tex"
    )
    
    local TEMP_TEX=$(mktemp)
    
    for file in "${CONTENT_FILES[@]}"; do
        if [[ -f "$CONTENT_DIR/$file" ]]; then
            cat "$CONTENT_DIR/$file" >> "$TEMP_TEX"
            echo -e "\n\n" >> "$TEMP_TEX"
        fi
    done
    
    # Convert with pandoc
    pandoc "$TEMP_TEX" -f latex -t markdown \
        --wrap=none \
        --columns=100 \
        -o "$OUT_DIR/content.md" 2>/dev/null || true
    
    cat "$OUT_DIR/content.md" >> "$OUT_FILE"
    rm -f "$TEMP_TEX" "$OUT_DIR/content.md"
    
    # Add footer
    cat >> "$OUT_FILE" << 'EOF'

---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper2_ssot/proofs/`
- Lines: 1,811
- Theorems: 96
- Sorry placeholders: 0

EOF
    
    success "Paper 2 → $OUT_FILE"
}

build_paper3() {
    log "Building Paper 3: Leverage Framework..."
    
    local PAPER_DIR="$PAPERS_DIR/paper3_leverage"
    local LATEX_DIR="$PAPER_DIR/latex"
    local OUT_DIR="$PAPER_DIR/markdown"
    local OUT_FILE="$OUT_DIR/paper3_leverage.md"
    
    mkdir -p "$OUT_DIR"
    
    # Create header
    cat > "$OUT_FILE" << 'EOF'
# Paper 3: Leverage-Driven Software Architecture

**Status**: TOPLAS-ready | **Lean**: 2,091 lines, ~50 theorems, 0 sorry

This is the METATHEOREM paper that unifies Papers 1 and 2 as instances.

---

EOF
    
    # Paper 3 has a single content.tex file
    if [[ -f "$LATEX_DIR/content.tex" ]]; then
        pandoc "$LATEX_DIR/content.tex" -f latex -t markdown \
            --wrap=none \
            --columns=100 \
            -o "$OUT_DIR/content.md" 2>/dev/null || true
        
        cat "$OUT_DIR/content.md" >> "$OUT_FILE"
        rm -f "$OUT_DIR/content.md"
    fi
    
    # Add footer
    cat >> "$OUT_FILE" << 'EOF'

---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper3_leverage/proofs/`
- Lines: 2,091
- Theorems: ~50
- Sorry placeholders: 0

## Cross-Paper Integration

- **Theorem 4.7**: Paper 1 (Typing) is an instance of leverage maximization
- **Theorem 4.8**: Paper 2 (SSOT) is an instance of leverage maximization

EOF
    
    success "Paper 3 → $OUT_FILE"
}

build_all() {
    log "Building all papers..."
    echo ""
    build_paper1
    echo ""
    build_paper2
    echo ""
    build_paper3
    echo ""
    
    # Create combined file for LLM consumption
    local COMBINED="$PAPERS_DIR/TRILOGY_COMBINED.md"
    
    cat > "$COMBINED" << 'EOF'
# TOPLAS Trilogy: Leverage-Driven Software Architecture

This document contains all three papers in the trilogy for easy LLM consumption.

## Overview

| Paper | Title | Role |
|-------|-------|------|
| Paper 1 | Typing Discipline Selection | Instance |
| Paper 2 | SSOT Foundations | Instance |
| Paper 3 | Leverage Framework | Metatheorem |

**Total**: 6,568 Lean lines, ~273 theorems, 0 sorry placeholders

---

EOF
    
    cat "$PAPERS_DIR/paper1_typing_discipline/markdown/paper1_typing_discipline.md" >> "$COMBINED"
    echo -e "\n\n---\n\n" >> "$COMBINED"
    cat "$PAPERS_DIR/paper2_ssot/markdown/paper2_ssot.md" >> "$COMBINED"
    echo -e "\n\n---\n\n" >> "$COMBINED"
    cat "$PAPERS_DIR/paper3_leverage/markdown/paper3_leverage.md" >> "$COMBINED"
    
    success "Combined trilogy → $COMBINED"
    echo ""
    log "Summary:"
    wc -l "$PAPERS_DIR"/paper*/markdown/*.md "$COMBINED" 2>/dev/null | tail -4
}

# Main
case "${1:-all}" in
    paper1)
        build_paper1
        ;;
    paper2)
        build_paper2
        ;;
    paper3)
        build_paper3
        ;;
    all)
        build_all
        ;;
    *)
        echo "Usage: $0 [paper1|paper2|paper3|all]"
        exit 1
        ;;
esac

