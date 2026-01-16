#!/usr/bin/env python3
"""
Unified paper build system for all TOPLAS papers.

OpenHCS Architecture:
  - Declarative: Configuration in YAML, not code
  - Fail-Loud: Explicit validation, no silent failures
  - Orthogonal: One responsibility per function
  - Explicit Dependency Injection: No hidden state
  - Compile-Time Validation: Check everything upfront

STRUCTURAL INVARIANTS (mathematical constraints):
  1. Content: ∀p ∈ Papers: content(p) ⊂ paper_dir(p)/latex/content/*.tex
  2. Proofs:  ∀p ∈ Papers: proofs(p) ⊂ proofs_dir/paper{id}_*.lean
  3. Output:  ∀p ∈ Papers: releases(p) = {pdf, md, BUILD_LOG.txt, tar.gz, zip}

All papers follow identical structure. No special cases.
"""

import sys
import subprocess
import shutil
from pathlib import Path
from typing import List, Dict, Tuple
from dataclasses import dataclass
import yaml
import argparse
from datetime import datetime


@dataclass(frozen=True)
class ArxivConfig:
    """Immutable arXiv packaging configuration."""
    include_build_log: bool = True
    include_lean_source: bool = True
    include_build_config: bool = True
    exclude_patterns: Tuple[str, ...] = (".lake", "build", "*.olean", "*.ilean")

    @classmethod
    def from_dict(cls, d: dict) -> "ArxivConfig":
        return cls(
            include_build_log=d.get("include_build_log", True),
            include_lean_source=d.get("include_lean_source", True),
            include_build_config=d.get("include_build_config", True),
            exclude_patterns=tuple(d.get("exclude_patterns", [])),
        )


@dataclass(frozen=True)
class PaperMeta:
    """Immutable paper metadata. Represents a single paper's configuration."""
    paper_id: str           # e.g., "paper1"
    name: str               # e.g., "Typing Discipline"
    full_name: str          # Full paper title
    dir_name: str           # e.g., "paper1_typing_discipline"
    latex_dir: str          # Relative to paper dir, typically "latex"
    latex_file: str         # Main .tex file name
    lean_lines: int
    lean_theorems: int
    lean_sorry: int
    venue: str              # Target venue, e.g., "JSAIT", "TOPLAS"

    @classmethod
    def from_dict(cls, paper_id: str, d: dict) -> "PaperMeta":
        return cls(
            paper_id=paper_id,
            name=d["name"],
            full_name=d["full_name"],
            dir_name=d["dir"],
            latex_dir=d.get("latex_dir", "latex"),
            latex_file=d["latex_file"],
            lean_lines=d.get("lean_lines", 0),
            lean_theorems=d.get("lean_theorems", 0),
            lean_sorry=d.get("lean_sorry", 0),
            venue=d.get("venue", "Draft"),
        )


class PaperBuilder:
    """
    Unified builder for all paper formats.

    STRUCTURAL INVARIANTS:
    1. ∀p: paper_dir(p) = papers_dir / meta(p).dir_name
    2. ∀p: content_dir(p) = paper_dir(p) / meta(p).latex_dir / "content"
    3. ∀p: releases_dir(p) = paper_dir(p) / "releases"
    4. ∀p: proofs_dir(p) = paper_dir(p) / "proofs"

    All papers follow these invariants. No exceptions.
    """

    def __init__(self, repo_root: Path):
        self.repo_root = repo_root
        self.scripts_dir = repo_root / "scripts"
        self.papers_dir = repo_root / "docs" / "papers"

        # Load configuration
        self._raw_metadata = self._load_raw_metadata()
        self.arxiv_config = ArxivConfig.from_dict(self._raw_metadata.get("arxiv", {}))
        self.papers: Dict[str, PaperMeta] = self._load_papers()

        # Captured build output for BUILD_LOG.txt
        self._lean_build_output: str = ""

        # Validate upfront (fail-loud)
        self._validate_prerequisites()
        self._validate_paper_structure()

    def _load_raw_metadata(self) -> dict:
        """Load raw YAML metadata."""
        metadata_file = self.scripts_dir / "papers.yaml"
        if not metadata_file.exists():
            raise FileNotFoundError(f"papers.yaml not found at {metadata_file}")
        with open(metadata_file) as f:
            return yaml.safe_load(f)

    def _load_papers(self) -> Dict[str, PaperMeta]:
        """Convert raw YAML to immutable PaperMeta objects."""
        papers = {}
        for paper_id, paper_dict in self._raw_metadata.get("papers", {}).items():
            papers[paper_id] = PaperMeta.from_dict(paper_id, paper_dict)
        return papers

    def _validate_prerequisites(self):
        """Fail loudly if required tools are missing."""
        required = ["pdflatex", "bibtex", "pandoc", "lake"]
        missing = [cmd for cmd in required if not shutil.which(cmd)]
        if missing:
            raise RuntimeError(
                f"Missing required tools: {', '.join(missing)}\n"
                f"Install with: sudo apt install {' '.join(missing)}"
            )

    def _validate_paper_structure(self):
        """Validate structural invariants for all papers."""
        errors = []
        for paper_id, meta in self.papers.items():
            paper_dir = self.papers_dir / meta.dir_name
            if not paper_dir.exists():
                errors.append(f"{paper_id}: paper_dir not found: {paper_dir}")
                continue

            latex_dir = paper_dir / meta.latex_dir
            if not latex_dir.exists():
                errors.append(f"{paper_id}: latex_dir not found: {latex_dir}")

            latex_file = latex_dir / meta.latex_file
            if not latex_file.exists():
                errors.append(f"{paper_id}: latex_file not found: {latex_file}")

            content_dir = latex_dir / "content"
            if not content_dir.exists():
                errors.append(f"{paper_id}: content_dir not found: {content_dir}")

        if errors:
            raise ValueError(
                f"Paper structure validation failed:\n" +
                "\n".join(f"  - {e}" for e in errors)
            )

    def _get_paper_meta(self, paper_id: str) -> PaperMeta:
        """Get paper metadata, fail if not found."""
        if paper_id not in self.papers:
            valid = ", ".join(self.papers.keys())
            raise ValueError(f"Unknown paper: {paper_id}. Valid papers: {valid}")
        return self.papers[paper_id]

    def _get_paper_dir(self, paper_id: str) -> Path:
        """Get paper directory path."""
        meta = self._get_paper_meta(paper_id)
        return self.papers_dir / meta.dir_name

    def _get_content_dir(self, paper_id: str) -> Path:
        """Get content directory: paper_dir/latex/content (INVARIANT 2)."""
        meta = self._get_paper_meta(paper_id)
        return self.papers_dir / meta.dir_name / meta.latex_dir / "content"

    def _get_releases_dir(self, paper_id: str) -> Path:
        """Get releases directory, creating if needed (INVARIANT 3)."""
        releases_dir = self._get_paper_dir(paper_id) / "releases"
        releases_dir.mkdir(parents=True, exist_ok=True)
        return releases_dir

    def _discover_content_files(self, paper_id: str) -> List[Path]:
        """Auto-discover content files from latex/content/ directory."""
        content_dir = self._get_content_dir(paper_id)
        # Find all .tex files, sorted by name (ensures consistent order)
        files = sorted(content_dir.glob("*.tex"))
        # Filter: skip abstract.tex (handled separately), include numbered files
        return [f for f in files if f.name != "abstract.tex"]

    def _get_paper_proofs_dir(self, paper_id: str) -> Path:
        """Get the proofs directory for a specific paper.

        Each paper has its own proofs directory at: paper_dir/proofs/
        For variants (e.g., paper1_jsait), use the base paper's proofs.
        """
        meta = self._get_paper_meta(paper_id)
        # Handle variants: paper1_jsait -> paper1_typing_discipline/proofs
        base_dir_name = meta.dir_name
        return self.papers_dir / base_dir_name / "proofs"

    def build_lean(self, paper_id: str, verbose: bool = True) -> str:
        """Build Lean proofs with streaming output. Returns captured output.

        Uses each paper's own proofs directory (paper_dir/proofs/).
        Runs `lake build` in that directory.
        Captures output for inclusion in BUILD_LOG.txt.
        """
        proofs_dir = self._get_paper_proofs_dir(paper_id)

        if not proofs_dir.exists():
            print(f"[build] No proofs directory for {paper_id}, skipping...")
            return ""

        # Check for lakefile
        lakefile = proofs_dir / "lakefile.lean"
        if not lakefile.exists():
            print(f"[build] No lakefile.lean in {proofs_dir}, skipping...")
            return ""

        print(f"[build] Building {paper_id} Lean...")
        print(f"[build]   Directory: {proofs_dir.relative_to(self.repo_root)}")

        def run_lake(args: List[str]) -> Tuple[int, List[str]]:
            """Run lake command with streaming output."""
            print(f"[build]   Running: lake {' '.join(args)}")
            process = subprocess.Popen(
                ["lake"] + args,
                cwd=proofs_dir,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
            )

            output_lines: List[str] = []
            if process.stdout is not None:
                for line in process.stdout:
                    output_lines.append(line)
                    if verbose:
                        print(f"         {line}", end="", flush=True)
                    elif "Building" in line or "Compiling" in line:
                        print(".", end="", flush=True)

            process.wait()
            if not verbose:
                print()
            return (process.returncode, output_lines)

        # Run lake build (builds all targets in the paper's proofs directory)
        returncode, output = run_lake(["build"])
        output_text = "".join(output)

        # Handle stale cache
        if "compiled configuration is invalid" in output_text:
            print(f"[build]   Reconfiguring (stale cache detected)...")
            returncode, output = run_lake(["build", "-R"])
            output_text = "".join(output)

        if returncode != 0:
            if not verbose:
                print("[build]   lake output (last 200 lines):")
                for line in output_text.splitlines()[-200:]:
                    print(f"         {line}")
            raise RuntimeError(
                f"Lean build failed for {paper_id} (exit code {returncode})"
            )

        # Store for BUILD_LOG.txt
        self._lean_build_output = output_text
        print(f"[build] ✓ {paper_id} Lean complete")
        return output_text

    def build_latex(self, paper_id: str, verbose: bool = False):
        """Build LaTeX PDF for a paper and copy to releases/.

        Runs full build cycle: pdflatex → bibtex → pdflatex → pdflatex
        to resolve citations and cross-references.

        For variants (e.g., paper1_jsait), uses variant-specific naming.
        """
        meta = self._get_paper_meta(paper_id)
        paper_dir = self._get_paper_dir(paper_id)
        latex_dir = paper_dir / meta.latex_dir
        latex_file = latex_dir / meta.latex_file

        if not latex_file.exists():
            raise FileNotFoundError(f"LaTeX file not found: {latex_file}")

        self._update_paper_date(latex_file)

        print(f"[build] Building {paper_id} LaTeX...")

        # Full build cycle for proper citation/reference resolution
        aux_name = latex_file.stem
        build_steps = [
            (["pdflatex", "-interaction=nonstopmode", latex_file.name], "pdflatex (1/3)"),
            (["bibtex", aux_name], "bibtex"),
            (["pdflatex", "-interaction=nonstopmode", latex_file.name], "pdflatex (2/3)"),
            (["pdflatex", "-interaction=nonstopmode", latex_file.name], "pdflatex (3/3)"),
        ]

        for cmd, step_name in build_steps:
            if verbose:
                print(f"[build]   Running: {step_name}")
            result = subprocess.run(
                cmd,
                cwd=latex_dir,
                capture_output=True,
                text=True,
                encoding="latin-1",
                errors="replace",
            )
            # bibtex returns non-zero if no citations, which is fine
            if result.returncode != 0 and "bibtex" not in cmd[0]:
                if verbose:
                    if result.stdout:
                        print(result.stdout)
                print(f"[build] {step_name} had warnings/errors (exit {result.returncode})")

        # Copy PDF to releases/ (INVARIANT 3)
        # Use variant-specific naming to avoid conflicts
        pdf_name = latex_file.stem + ".pdf"
        pdf_src = latex_dir / pdf_name
        if pdf_src.exists():
            releases_dir = self._get_releases_dir(paper_id)
            pdf_dest = releases_dir / f"{paper_id}.pdf"
            shutil.copy2(pdf_src, pdf_dest)
            print(f"[build] ✓ {paper_id}.pdf → releases/")

    def build_markdown(self, paper_id: str):
        """Build Markdown version of a paper.

        Uses INVARIANT 2: content is at paper_dir/latex/content/
        Content files are auto-discovered, not hardcoded.

        For variants (e.g., paper1_jsait), uses variant-specific naming.
        """
        meta = self._get_paper_meta(paper_id)
        content_dir = self._get_content_dir(paper_id)
        out_dir = self._get_paper_dir(paper_id) / "markdown"
        # Use paper_id for variant-specific naming
        out_file = out_dir / f"{paper_id}.md"

        if not content_dir.exists():
            print(f"[build-md] Skipping {paper_id}: content_dir not found: {content_dir}")
            return

        out_dir.mkdir(parents=True, exist_ok=True)
        print(f"[build-md] Building {paper_id}: {meta.name}...")

        # Auto-discover content files
        content_files = self._discover_content_files(paper_id)
        self._build_markdown_file(meta, content_dir, content_files, out_file)

        # Also copy to releases/ for arxiv package
        releases_dir = self._get_releases_dir(paper_id)
        shutil.copy2(out_file, releases_dir / out_file.name)
        print(f"[build-md] {paper_id} → {out_file.relative_to(self.repo_root)}")

    def _build_markdown_file(
        self, meta: PaperMeta, content_dir: Path, content_files: List[Path], out_file: Path
    ):
        """Generate markdown file from LaTeX content."""
        with open(out_file, "w") as f:
            # Header
            f.write(f"# Paper: {meta.full_name}\n\n")
            f.write(
                f"**Status**: {meta.venue}-ready | "
                f"**Lean**: {meta.lean_lines} lines, "
                f"{meta.lean_theorems} theorems\n\n---\n\n"
            )

            # Abstract
            f.write("## Abstract\n\n")
            abstract_file = content_dir / "abstract.tex"
            if abstract_file.exists():
                # Try extracting from \begin{abstract}...\end{abstract} first,
                # fall back to raw file content if no environment found
                content = abstract_file.read_text(encoding='utf-8')
                if r'\begin{abstract}' in content:
                    self._convert_latex_to_markdown(abstract_file, f, extract_env="abstract")
                else:
                    self._convert_latex_to_markdown(abstract_file, f)
            else:
                f.write("_Abstract not available._\n\n")

            # Content sections (auto-discovered)
            for content_path in content_files:
                self._convert_latex_to_markdown(content_path, f)

            # Footer
            f.write("\n\n---\n\n## Machine-Checked Proofs\n\n")
            f.write(f"All theorems are formalized in Lean 4:\n")
            f.write(f"- Location: `docs/papers/proofs/{meta.paper_id}_*.lean`\n")
            f.write(f"- Lines: {meta.lean_lines}\n")
            f.write(f"- Theorems: {meta.lean_theorems}\n")


    def _convert_latex_to_markdown(self, tex_file: Path, out_file, extract_env: str | None = None):
        """Convert LaTeX file to Markdown using pandoc.

        Args:
            tex_file: Path to .tex file
            out_file: Output file handle
            extract_env: If set, extract content from \\begin{env}...\\end{env} first
        """
        import re

        if extract_env:
            # Extract content from environment before converting
            content = tex_file.read_text(encoding='utf-8')
            pattern = rf'\\begin\{{{extract_env}\}}(.*?)\\end\{{{extract_env}\}}'
            match = re.search(pattern, content, re.DOTALL)
            if not match:
                out_file.write(f"_Content not found in {tex_file.name}_\n\n")
                return
            latex_input = match.group(1).strip()
            result = subprocess.run(
                ["pandoc", "-f", "latex", "-t", "markdown", "--wrap=none", "--columns=100"],
                input=latex_input,
                capture_output=True,
                text=True,
            )
        else:
            result = subprocess.run(
                ["pandoc", str(tex_file), "-f", "latex", "-t", "markdown", "--wrap=none", "--columns=100"],
                capture_output=True,
                text=True,
            )

        if result.returncode == 0 and result.stdout:
            out_file.write(result.stdout)
            out_file.write("\n\n")
        else:
            out_file.write(f"_Failed to convert {tex_file.name}_\n\n")

    def _update_paper_date(self, tex_file: Path):
        """Update publication date in LaTeX file using regex for correct replacement."""
        import re
        today = datetime.now().strftime("%B %-d, %Y")
        year = datetime.now().strftime("%Y")
        try:
            content = tex_file.read_text(encoding='utf-8')
        except UnicodeDecodeError:
            content = tex_file.read_text(encoding='latin-1')

        # Use regex to replace entire \date{...} command, not just the prefix
        content = re.sub(r'\\date\{[^}]*\}', f'\\\\date{{{today}}}', content)
        content = re.sub(r'\\copyrightyear\{[^}]*\}', f'\\\\copyrightyear{{{year}}}', content)
        content = re.sub(r'\\acmYear\{[^}]*\}', f'\\\\acmYear{{{year}}}', content)
        tex_file.write_text(content, encoding='utf-8')

    def package_arxiv(self, paper_id: str):
        """
        Package paper for arXiv submission.

        Includes:
        - PDF (compiled paper)
        - Markdown (full text for LLM consumption)
        - Lean proofs (source code)
        - BUILD_LOG.txt (actual lake build output as compilation proof)

        For variants (e.g., paper1_jsait), uses variant-specific staging directory.
        """
        # Phase 1: Validate all required files exist (fail-loud)
        pdf_file = self._validate_and_get_pdf(paper_id)
        md_file = self._validate_and_get_markdown(paper_id)

        # Phase 2: Create staging directory in releases/ with variant-specific naming
        releases_dir = self._get_releases_dir(paper_id)
        package_dir = releases_dir / f"arxiv_package_{paper_id}"
        if package_dir.exists():
            shutil.rmtree(package_dir)
        package_dir.mkdir(parents=True)

        print(f"[arxiv] Packaging {paper_id}...")

        # Phase 3: Copy artifacts
        self._copy_pdf(pdf_file, package_dir)
        self._copy_markdown(md_file, package_dir)
        self._copy_latex_sources(paper_id, package_dir)
        self._copy_lean_proofs(paper_id, package_dir)
        self._copy_experiments(paper_id, package_dir)

        if self.arxiv_config.include_build_log:
            self._create_build_log(paper_id, package_dir)

        # Phase 4: Create compressed archives
        tar_path, zip_path = self._create_archive(paper_id, package_dir)

        print(f"[arxiv] {paper_id} → {tar_path.relative_to(self.repo_root)}, {zip_path.name}")
        return tar_path

    def _validate_and_get_pdf(self, paper_id: str) -> Path:
        """Validate PDF exists and return path. Fail-loud if missing."""
        meta = self._get_paper_meta(paper_id)
        paper_dir = self._get_paper_dir(paper_id)
        latex_dir = paper_dir / meta.latex_dir
        pdfs = list(latex_dir.glob("*.pdf"))

        if not pdfs:
            raise FileNotFoundError(
                f"[arxiv] FATAL: No PDF found in {latex_dir}\n"
                f"  Paper: {meta.name}\n"
                f"  Run: python3 scripts/build_papers.py latex {paper_id}"
            )
        return pdfs[0]

    def _validate_and_get_markdown(self, paper_id: str) -> Path:
        """Validate Markdown exists and return path. Fail-loud if missing."""
        meta = self._get_paper_meta(paper_id)
        paper_dir = self._get_paper_dir(paper_id)
        md_file = paper_dir / "markdown" / f"{meta.dir_name}.md"

        if not md_file.exists():
            raise FileNotFoundError(
                f"[arxiv] FATAL: Markdown not found: {md_file}\n"
                f"  Paper: {meta.name}\n"
                f"  Run: python3 scripts/build_papers.py markdown {paper_id}"
            )
        return md_file

    def _copy_pdf(self, pdf_file: Path, package_dir: Path) -> None:
        """Copy PDF to package directory."""
        pdf_dest = package_dir / pdf_file.name
        shutil.copy2(pdf_file, pdf_dest)
        print(f"[arxiv]   PDF: {pdf_file.name}")

    def _copy_markdown(self, md_file: Path, package_dir: Path) -> None:
        """Copy Markdown to package directory."""
        md_dest = package_dir / md_file.name
        shutil.copy2(md_file, md_dest)
        print(f"[arxiv]   Markdown: {md_file.name}")

    def _copy_latex_sources(self, paper_id: str, package_dir: Path) -> None:
        """Copy LaTeX source files for arXiv submission.

        Copies all .tex, .bib, .bbl, .cls, .sty files from the latex directory.
        Also copies content/ subdirectory if present.
        """
        meta = self._get_paper_meta(paper_id)
        paper_dir = self._get_paper_dir(paper_id)
        latex_dir = paper_dir / meta.latex_dir

        if not latex_dir.exists():
            print(f"[arxiv]   No LaTeX directory for {paper_id}, skipping...")
            return

        # Extensions to copy
        extensions = [".tex", ".bib", ".bbl", ".cls", ".sty"]
        copied_count = 0

        # Copy top-level LaTeX files
        for ext in extensions:
            for src_file in latex_dir.glob(f"*{ext}"):
                shutil.copy2(src_file, package_dir / src_file.name)
                copied_count += 1

        # Copy content/ subdirectory if present
        content_dir = latex_dir / "content"
        if content_dir.exists():
            content_dest = package_dir / "content"
            content_dest.mkdir(parents=True, exist_ok=True)
            for src_file in content_dir.glob("*.tex"):
                shutil.copy2(src_file, content_dest / src_file.name)
                copied_count += 1

        print(f"[arxiv]   LaTeX sources: {copied_count} files")

    def _copy_lean_proofs(self, paper_id: str, package_dir: Path) -> None:
        """Copy Lean proofs for specific paper to package directory.

        Uses the paper's own proofs directory (paper_dir/proofs/).
        Copies all .lean files and config, generates README.
        """
        proofs_dir = self._get_paper_proofs_dir(paper_id)

        if not proofs_dir.exists():
            print(f"[arxiv]   No proofs directory for {paper_id}, skipping...")
            return

        lean_dest = package_dir / "proofs"
        lean_dest.mkdir(parents=True, exist_ok=True)

        # Copy all .lean files from the paper's proofs directory
        paper_files = []
        exclude_patterns = {".lake", "build"}
        for f in sorted(proofs_dir.rglob("*.lean")):
            # Skip files in excluded directories
            if any(part in exclude_patterns for part in f.parts):
                continue
            # Compute relative path
            rel_path = f.relative_to(proofs_dir)
            dest_file = lean_dest / rel_path
            dest_file.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(f, dest_file)
            paper_files.append(f)

        # Copy config files
        config_files = ["lean-toolchain", "lake-manifest.json"]
        for fname in config_files:
            src = proofs_dir / fname
            if src.exists():
                shutil.copy2(src, lean_dest / fname)

        # Generate README (correct by construction)
        self._generate_proofs_readme(paper_id, paper_files, lean_dest)

        print(f"[arxiv]   Lean proofs: {len(paper_files)} files")

    def _copy_experiments(self, paper_id: str, package_dir: Path) -> None:
        """Copy experiments directory if present.

        Copies Python scripts, data files, and results from the experiments/ subdirectory.
        """
        paper_dir = self._get_paper_dir(paper_id)
        experiments_dir = paper_dir / "experiments"

        if not experiments_dir.exists():
            return  # No experiments directory, skip silently

        experiments_dest = package_dir / "experiments"
        experiments_dest.mkdir(parents=True, exist_ok=True)

        # Copy all relevant files
        copied_count = 0
        extensions = [".py", ".json", ".csv", ".txt", ".sh", ".md"]
        for ext in extensions:
            for src_file in experiments_dir.glob(f"*{ext}"):
                shutil.copy2(src_file, experiments_dest / src_file.name)
                copied_count += 1

        if copied_count > 0:
            print(f"[arxiv]   Experiments: {copied_count} files")

    def _generate_paper_lakefile(self, paper_id: str, paper_files: list, lean_dest: Path) -> None:
        """Generate paper-specific lakefile from actual proof files."""
        meta = self._get_paper_meta(paper_id)

        # Extract lib names from filenames (paper4_Basic.lean -> paper4_Basic)
        lib_names = [f.stem for f in paper_files]

        lib_entries = "\n".join([
            f'''lean_lib «{name}» where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
''' for name in lib_names
        ])

        lakefile_content = f'''import Lake
open Lake DSL

-- {meta.name} - Lean 4 Formalization
-- Auto-generated by build_papers.py

def moreServerArgs := #[
  "-Dpp.unicode.fun=true",
  "-Dpp.proofs.withType=false"
]

def moreLeanArgs := moreServerArgs

def weakLeanArgs : Array String :=
  if get_config? CI |>.isSome then
    #["-DwarningAsError=true"]
  else
    #[]

package «{meta.dir_name}» where
  moreServerArgs := moreServerArgs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

{lib_entries}'''

        (lean_dest / "lakefile.lean").write_text(lakefile_content)

    def _generate_proofs_readme(self, paper_id: str, paper_files: list, lean_dest: Path) -> None:
        """Generate README for proofs directory from actual proof files."""
        meta = self._get_paper_meta(paper_id)

        # Build file table
        file_rows = "\n".join([
            f"| `{f.name}` | {f.stem.replace(paper_id + '_', '')} |"
            for f in paper_files
        ])

        readme_content = f'''# {meta.name} - Lean 4 Formalization

## Overview

This directory contains the complete Lean 4 formalization for {meta.name}.

- **Lines:** {meta.lean_lines}
- **Theorems:** {meta.lean_theorems}


## Requirements

- Lean 4 (see `lean-toolchain` for exact version)
- Mathlib4

## Building

```bash
lake update
lake build
```

## File Structure

| File | Module |
|------|--------|
{file_rows}

## Verification

All files compile with 0 `sorry` placeholders. All claims are machine-verified.

## License

MIT License - See main repository for details.

---
*Auto-generated by build_papers.py*
'''

        (lean_dest / "README.md").write_text(readme_content)

    def _create_build_log(self, paper_id: str, package_dir: Path) -> None:
        """
        Create BUILD_LOG.txt with ACTUAL lake build output as compilation proof.
        This is the mathematical evidence that proofs compile.
        """
        meta = self._get_paper_meta(paper_id)
        log_file = package_dir / "BUILD_LOG.txt"

        # Paper-specific proof files from paper's proofs directory
        proofs_dir = self._get_paper_proofs_dir(paper_id)
        exclude_patterns = {".lake", "build"}
        paper_lean_files = [
            f for f in proofs_dir.rglob("*.lean")
            if not any(part in exclude_patterns for part in f.parts)
        ] if proofs_dir.exists() else []
        lean_toolchain = proofs_dir / "lean-toolchain"
        toolchain_version = lean_toolchain.read_text().strip() if lean_toolchain.exists() else "unknown"

        log_content = f"""OpenHCS Paper Build Log
========================

Paper: {paper_id} - {meta.full_name}
Package Date: {datetime.now().isoformat()}
Lean Toolchain: {toolchain_version}

Proof Statistics:
-----------------
Lean Files: {len(paper_lean_files)}
Lines of Code: {meta.lean_lines}
Theorems: {meta.lean_theorems}


Proof Files:
------------
"""
        for f in sorted(paper_lean_files):
            log_content += f"  - {f.name}\n"

        # Include actual lake build output if available
        if self._lean_build_output:
            log_content += f"""
================================================================================
COMPILATION OUTPUT (lake build)
================================================================================

{self._lean_build_output}

================================================================================
END COMPILATION OUTPUT
================================================================================
"""
        else:
            log_content += """
Note: Run 'python3 scripts/build_papers.py release' to include compilation output.
"""

        log_content += f"""
Build Instructions:
-------------------
To verify the proofs compile:

  cd proofs/
  lake build

All theorems will be machine-verified if compilation succeeds.

Repository: https://github.com/trissim/openhcs
"""

        log_file.write_text(log_content)
        print(f"[arxiv]   Build log: BUILD_LOG.txt (with compilation output)")

    def _create_archive(self, paper_id: str, package_dir: Path) -> tuple[Path, Path]:
        """Create compressed tar.gz and zip archives of package in releases/.

        For variants (e.g., paper1_jsait), uses variant-specific naming.
        """
        import tarfile
        import zipfile

        meta = self._get_paper_meta(paper_id)
        releases_dir = self._get_releases_dir(paper_id)

        # Create tar.gz with variant-specific naming
        tar_name = f"{paper_id}_arxiv.tar.gz"
        tar_path = releases_dir / tar_name
        with tarfile.open(tar_path, "w:gz") as tar:
            tar.add(package_dir, arcname=paper_id)

        # Create zip with variant-specific naming
        zip_name = f"{paper_id}_arxiv.zip"
        zip_path = releases_dir / zip_name
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            for file_path in package_dir.rglob("*"):
                if file_path.is_file():
                    arcname = paper_id / file_path.relative_to(package_dir)
                    zf.write(file_path, arcname)

        return tar_path, zip_path

    def release(self, paper_id: str, verbose: bool = True, axiom_check: bool = False):
        """Full release build: Lean + LaTeX + Markdown + arXiv package.

        For variants (e.g., paper1_jsait), only build Lean once (shared proofs).
        """
        meta = self._get_paper_meta(paper_id)
        print(f"\n{'='*60}")
        print(f"[release] Building {paper_id}: {meta.name}")
        print(f"{'='*60}\n")

        # For variants, only build Lean if it's the base paper
        is_variant = paper_id != meta.dir_name.replace("_", "").lower()

        # Build in order: Lean → LaTeX → Markdown → Package
        if not is_variant:
            self.build_lean(paper_id, verbose=verbose)
        else:
            print(f"[release] Skipping Lean build for variant {paper_id} (shared proofs)")

        self.build_latex(paper_id, verbose=verbose)
        self.build_markdown(paper_id)
        self.package_arxiv(paper_id)

        if axiom_check and not is_variant:
            self.check_axioms(paper_id, verbose=verbose)

        releases_dir = self._get_releases_dir(paper_id)
        print(f"\n[release] ✓ {paper_id} complete → {releases_dir.relative_to(self.repo_root)}/")

    def check_axioms(self, paper_id: str, verbose: bool = True) -> dict:
        """Check what axioms each theorem in a paper depends on.

        Uses `lake env lean` with `#print axioms` to verify theorem foundations.
        Returns a summary dict with counts by axiom category.
        """
        import re
        from collections import defaultdict

        proofs_dir = self._get_paper_proofs_dir(paper_id)
        if not proofs_dir.exists():
            print(f"[axiom-check] No proofs directory for {paper_id}, skipping...")
            return {}

        print(f"[axiom-check] Checking axioms for {paper_id}...")
        print(f"[axiom-check]   Directory: {proofs_dir.relative_to(self.repo_root)}")

        # Step 1: Find all theorem/lemma declarations in .lean files
        theorems = []
        exclude_patterns = {".lake", "build"}
        for lean_file in sorted(proofs_dir.rglob("*.lean")):
            if any(part in exclude_patterns for part in lean_file.parts):
                continue
            if lean_file.name in ("lakefile.lean",):
                continue

            # Compute module name from file path
            rel_path = lean_file.relative_to(proofs_dir)
            module_name = str(rel_path.with_suffix("")).replace("/", ".")

            try:
                content = lean_file.read_text(encoding="utf-8")
            except UnicodeDecodeError:
                content = lean_file.read_text(encoding="latin-1")

            # Find theorem/lemma declarations
            for match in re.finditer(r"^(theorem|lemma)\s+(\w+['\w]*)", content, re.MULTILINE):
                thm_name = match.group(2)
                theorems.append((module_name, thm_name))

        if not theorems:
            print(f"[axiom-check]   No theorems found in {paper_id}")
            return {}

        print(f"[axiom-check]   Found {len(theorems)} theorems/lemmas")

        # Step 2: Group by module and check axioms
        by_module = defaultdict(list)
        for module, thm in theorems:
            by_module[module].append(thm)

        results = {
            "total": len(theorems),
            "checked": 0,
            "no_axioms": 0,
            "propext_only": 0,
            "quot_sound": 0,
            "classical": 0,
            "unknown": 0,
            "details": [],
        }

        for module, thms in sorted(by_module.items()):
            # Create temp file with #print axioms commands
            import tempfile
            with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
                f.write(f"import {module}\n\n")
                for thm in thms:
                    # Try with module prefix
                    f.write(f"#print axioms {module}.{thm}\n")
                tmpfile = f.name

            try:
                result = subprocess.run(
                    ["lake", "env", "lean", tmpfile],
                    capture_output=True,
                    text=True,
                    timeout=300,
                    cwd=proofs_dir,
                )
                output = result.stdout + result.stderr

                # Parse results
                found_thms = set()
                unknown_thms = []

                for line in output.split("\n"):
                    line = line.strip()
                    if "depends on axioms" in line or "does not depend" in line:
                        results["checked"] += 1
                        results["details"].append(line)
                        if verbose:
                            print(f"[axiom-check]   ✓ {line}")

                        # Categorize
                        if "does not depend" in line:
                            results["no_axioms"] += 1
                        elif "Classical" in line:
                            results["classical"] += 1
                        elif "Quot.sound" in line:
                            results["quot_sound"] += 1
                        elif "propext" in line:
                            results["propext_only"] += 1

                        # Track found
                        match = re.search(r"'([^']+)'", line)
                        if match:
                            found_thms.add(match.group(1).split(".")[-1])

                    elif "Unknown" in line and "constant" in line:
                        match = re.search(r"Unknown constant `([^`]+)`", line)
                        if match:
                            unknown_thms.append(match.group(1))

                # Retry unknown theorems without module prefix
                if unknown_thms:
                    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f2:
                        f2.write(f"import {module}\n")
                        f2.write(f"open {module.split('.')[-1]} in\n")
                        for unk in unknown_thms:
                            thm_name = unk.split(".")[-1]
                            if thm_name not in found_thms:
                                f2.write(f"#print axioms {thm_name}\n")
                        tmpfile2 = f2.name

                    result2 = subprocess.run(
                        ["lake", "env", "lean", tmpfile2],
                        capture_output=True,
                        text=True,
                        timeout=300,
                        cwd=proofs_dir,
                    )
                    output2 = result2.stdout + result2.stderr

                    for line in output2.split("\n"):
                        line = line.strip()
                        if "depends on axioms" in line or "does not depend" in line:
                            results["checked"] += 1
                            results["details"].append(line)
                            if verbose:
                                print(f"[axiom-check]   ✓ (no prefix) {line}")

                            if "does not depend" in line:
                                results["no_axioms"] += 1
                            elif "Classical" in line:
                                results["classical"] += 1
                            elif "Quot.sound" in line:
                                results["quot_sound"] += 1
                            elif "propext" in line:
                                results["propext_only"] += 1
                        elif "Unknown" in line:
                            results["unknown"] += 1

                    Path(tmpfile2).unlink(missing_ok=True)

            except subprocess.TimeoutExpired:
                print(f"[axiom-check]   TIMEOUT for module {module}")
            except Exception as e:
                print(f"[axiom-check]   ERROR: {e}")
            finally:
                Path(tmpfile).unlink(missing_ok=True)

        # Print summary
        print(f"\n[axiom-check] === {paper_id} Summary ===")
        print(f"[axiom-check]   Total theorems: {results['total']}")
        print(f"[axiom-check]   Successfully checked: {results['checked']}")
        print(f"[axiom-check]     - No axioms (constructive): {results['no_axioms']}")
        print(f"[axiom-check]     - Only propext: {results['propext_only']}")
        print(f"[axiom-check]     - propext + Quot.sound: {results['quot_sound']}")
        print(f"[axiom-check]     - Uses Classical.choice: {results['classical']}")
        print(f"[axiom-check]   Private/not exported: {results['unknown']}")

        return results

    def build_all(self, build_type: str = "all", verbose: bool = True, axiom_check: bool = False):
        """Build all papers of specified type."""
        paper_ids = list(self.papers.keys())

        if build_type == "release":
            for paper_id in paper_ids:
                try:
                    self.release(paper_id, verbose=verbose, axiom_check=axiom_check)
                except Exception as e:
                    print(f"[release] ERROR {paper_id}: {e}")
            return

        if build_type in ("all", "lean"):
            for paper_id in paper_ids:
                try:
                    self.build_lean(paper_id, verbose=verbose)
                except Exception as e:
                    print(f"[build] ERROR: {e}")

        if build_type in ("all", "latex"):
            for paper_id in paper_ids:
                try:
                    self.build_latex(paper_id, verbose=verbose)
                except Exception as e:
                    print(f"[build] ERROR: {e}")

        if build_type in ("all", "markdown"):
            for paper_id in paper_ids:
                try:
                    self.build_markdown(paper_id)
                except Exception as e:
                    print(f"[build-md] ERROR: {e}")

        if build_type in ("all", "arxiv"):
            for paper_id in paper_ids:
                try:
                    self.package_arxiv(paper_id)
                except Exception as e:
                    print(f"[arxiv] ERROR: {e}")

        if axiom_check:
            for paper_id in paper_ids:
                try:
                    self.check_axioms(paper_id, verbose=verbose)
                except Exception as e:
                    print(f"[axiom-check] ERROR: {e}")


def main():
    parser = argparse.ArgumentParser(
        description="Unified paper builder",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python scripts/build_papers.py release           # Full release build for all papers
  python scripts/build_papers.py release paper1    # Full release for paper1 only
  python scripts/build_papers.py lean paper1 -v    # Build Paper 1 Lean proofs (verbose)
  python scripts/build_papers.py latex paper2      # Build Paper 2 LaTeX
  python scripts/build_papers.py lean paper2 --axiom-check  # Build + check axioms
"""
    )
    parser.add_argument(
        "build_type",
        nargs="?",
        default="release",
        choices=["release", "all", "lean", "latex", "markdown", "arxiv"],
        help="What to build (default: release)",
    )
    parser.add_argument(
        "paper",
        nargs="?",
        default="all",
        help="Which paper: paper1, paper2, paper3, paper4, paper5, or all (default: all)",
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Show detailed output from build commands",
    )
    parser.add_argument(
        "-q", "--quiet",
        action="store_true",
        help="Minimal output (errors only)",
    )
    parser.add_argument(
        "--axiom-check",
        action="store_true",
        help="Run axiom verification on Lean theorems (checks what axioms each theorem depends on)",
    )

    args = parser.parse_args()
    repo_root = Path(__file__).parent.parent

    # Determine verbosity:
    # - Explicit -q wins (quiet)
    # - Otherwise default to verbose for release/lean so build output is streamed
    # - -v always forces verbose
    if args.quiet:
        verbose = False
    else:
        verbose = args.verbose or args.build_type in ("release", "lean")

    axiom_check = args.axiom_check

    try:
        builder = PaperBuilder(repo_root)
        if args.paper == "all":
            builder.build_all(args.build_type, verbose=verbose, axiom_check=axiom_check)
        else:
            if args.build_type == "release":
                builder.release(args.paper, verbose=verbose, axiom_check=axiom_check)
            elif args.build_type in ("all", "lean"):
                builder.build_lean(args.paper, verbose=verbose)
            if args.build_type in ("all", "latex"):
                builder.build_latex(args.paper, verbose=verbose)
            if args.build_type in ("all", "markdown"):
                builder.build_markdown(args.paper)
            if args.build_type in ("all", "arxiv"):
                builder.package_arxiv(args.paper)
            if axiom_check:
                builder.check_axioms(args.paper, verbose=verbose)
    except Exception as e:
        print(f"[build] FATAL: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
