#!/usr/bin/env bash
set -euo pipefail

# arXiv requires flat directory structure - ../shared/ paths won't work
# This script flattens everything and rewrites \input paths

die() { echo "FATAL: $*" >&2; exit 1; }

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PAPERS_DIR="$ROOT/docs/papers"
BUILD_DIR="$ROOT/build/arxiv"

rm -rf "$BUILD_DIR"
mkdir -p "$BUILD_DIR"

# Paper definitions: name|main_tex|aux_files_pattern
# aux_files_pattern is glob relative to paper dir
PAPERS=(
    "paper1_typing_discipline|arxiv/main.tex|shared/preamble.tex shared/content/*.tex shared/references.bib"
    "paper2_ssot|latex/ssot_arxiv.tex|latex/references.bib latex/ssot_arxiv.bbl latex/acmart.cls"
    "paper3_leverage|latex/leverage_arxiv.tex|latex/content.tex latex/references.bib latex/leverage_arxiv.bbl"
    "paper4_decision_quotient|latex/decision_quotient_arxiv.tex|latex/content.tex latex/hardness_proofs.tex latex/references.bib latex/decision_quotient_arxiv.bbl"
    "paper5_credibility|latex/credibility_arxiv.tex|latex/content.tex latex/references.bib latex/credibility_arxiv.bbl"
)

flatten_inputs() {
    # Rewrite \input{../shared/content/foo} -> \input{foo}
    # Rewrite \input{../shared/preamble} -> \input{preamble}
    local file="$1"
    sed -i \
        -e 's|\\input{[^}]*/\([^}/]*\)}|\\input{\1}|g' \
        -e 's|\\bibliography{[^}]*/\([^}/]*\)}|\\bibliography{\1}|g' \
        "$file"
}

package_paper() {
    local spec="$1"
    local name main_tex aux_pattern
    
    IFS='|' read -r name main_tex aux_pattern <<< "$spec"
    
    local paper_dir="$PAPERS_DIR/$name"
    local out_dir="$BUILD_DIR/$name"
    local tar_file="$BUILD_DIR/${name}_arxiv.tar.gz"
    
    [[ -d "$paper_dir" ]] || die "Paper directory not found: $paper_dir"
    
    mkdir -p "$out_dir"
    
    # Copy main tex
    local main_src="$paper_dir/$main_tex"
    [[ -f "$main_src" ]] || die "Main tex not found: $main_src"
    cp "$main_src" "$out_dir/main.tex"
    
    # Copy aux files (expand globs)
    for pattern in $aux_pattern; do
        for src in $paper_dir/$pattern; do
            [[ -e "$src" ]] || die "Aux file not found: $src (from pattern: $pattern)"
            cp "$src" "$out_dir/$(basename "$src")"
        done
    done

    # Copy proofs (Lean sources) if present
    local proofs_dir="$paper_dir/proofs"
    if [[ -d "$proofs_dir" ]]; then
        rsync -a \
          --exclude '.git' \
          --exclude '.lake' \
          --exclude 'build' \
          --exclude 'lake-packages' \
          --exclude '*.olean' \
          "$proofs_dir"/ "$out_dir/proofs/"
    fi
    
    # Flatten \input paths in all tex files
    for tex in "$out_dir"/*.tex; do
        flatten_inputs "$tex"
    done
    
    # Validate compilation
    echo "Compiling $name..."
    (cd "$out_dir" && pdflatex -interaction=nonstopmode main.tex >/dev/null 2>&1) \
        || die "Compilation failed for $name - check $out_dir/main.log"

    # Bibliography pass (if aux references exist)
    if grep -q "\\\\citation" "$out_dir/main.aux" 2>/dev/null; then
        (cd "$out_dir" && bibtex main >/dev/null 2>&1) \
            || die "BibTeX failed for $name - check $out_dir/main.blg"
    fi

    # Second and third passes for references
    (cd "$out_dir" && pdflatex -interaction=nonstopmode main.tex >/dev/null 2>&1) \
        || die "Second pass failed for $name"
    (cd "$out_dir" && pdflatex -interaction=nonstopmode main.tex >/dev/null 2>&1) \
        || die "Third pass failed for $name"
    
    # Create tarball (all sources, exclude build artifacts)
    (cd "$out_dir" && tar -czf "$tar_file" \
        --exclude='*.pdf' \
        --exclude='*.aux' \
        --exclude='*.log' \
        --exclude='*.out' \
        --exclude='*.toc' \
        .)

    # Also drop a copy into each paper's releases folder for convenience
    local release_dir="$paper_dir/releases"
    mkdir -p "$release_dir"
    local release_name
    case "$name" in
        paper1_typing_discipline) release_name="paper1_arxiv.tar.gz" ;;
        paper2_ssot)              release_name="paper2_arxiv.tar.gz" ;;
        paper3_leverage)          release_name="paper3_arxiv.tar.gz" ;;
        paper4_decision_quotient) release_name="paper4_arxiv.tar.gz" ;;
        paper5_credibility)       release_name="paper5_arxiv.tar.gz" ;;
        *)                        release_name="${name}_arxiv.tar.gz" ;;
    esac
    cp "$tar_file" "$release_dir/$release_name"
    
    # Copy the compiled PDF into the release folder as well
    local pdf_name="${release_name/_arxiv.tar.gz/.pdf}"
    if [[ -f "$out_dir/main.pdf" ]]; then
        cp "$out_dir/main.pdf" "$release_dir/$pdf_name"
    fi
    
    local pages
    pages=$(pdfinfo "$out_dir/main.pdf" 2>/dev/null | grep Pages | awk '{print $2}') || pages="?"
    
    echo "  ✓ $name: packaged (with proofs if present), $pages pages -> $tar_file"
}

echo "Packaging arXiv tarballs..."
echo "Build dir: $BUILD_DIR"
echo ""

for spec in "${PAPERS[@]}"; do
    package_paper "$spec"
done

echo ""
echo "Done. Tarballs in $BUILD_DIR/"
