#!/usr/bin/env python3
"""
Unified paper build system for all TOPLAS papers.

Replaces fragmented shell scripts with single orthogonal abstraction.
Principles:
  - Single source of truth (papers.yaml)
  - Fail loudly (validate all prerequisites)
  - Generic execution (one function per build type)
  - No special cases (all papers treated identically)
"""

import sys
import subprocess
import shutil
from pathlib import Path
from typing import Optional
import yaml
import argparse
from datetime import datetime


class PaperBuilder:
    """Unified builder for all paper formats."""

    def __init__(self, repo_root: Path):
        self.repo_root = repo_root
        self.scripts_dir = repo_root / "scripts"
        self.papers_dir = repo_root / "docs" / "papers"
        self.metadata = self._load_metadata()
        self._validate_prerequisites()

    def _load_metadata(self) -> dict:
        """Load papers.yaml metadata."""
        metadata_file = self.scripts_dir / "papers.yaml"
        if not metadata_file.exists():
            raise FileNotFoundError(f"papers.yaml not found at {metadata_file}")
        with open(metadata_file) as f:
            return yaml.safe_load(f)

    def _validate_prerequisites(self):
        """Fail loudly if required tools are missing."""
        required = ["pdflatex", "pandoc", "lake"]
        missing = [cmd for cmd in required if not shutil.which(cmd)]
        if missing:
            raise RuntimeError(
                f"Missing required tools: {', '.join(missing)}\n"
                f"Install with: sudo apt install {' '.join(missing)}"
            )

    def _get_paper_dir(self, paper_id: str) -> Path:
        """Get paper directory, fail if not found."""
        if paper_id not in self.metadata["papers"]:
            raise ValueError(f"Unknown paper: {paper_id}")
        paper_name = self.metadata["papers"][paper_id]["dir"]
        paper_dir = self.papers_dir / paper_name
        if not paper_dir.exists():
            raise FileNotFoundError(f"Paper directory not found: {paper_dir}")
        return paper_dir

    def build_lean(self, paper_id: str):
        """Build Lean proofs for a paper."""
        paper_dir = self._get_paper_dir(paper_id)
        proofs_dir = paper_dir / "proofs"
        if not proofs_dir.exists():
            raise FileNotFoundError(f"Proofs directory not found: {proofs_dir}")

        print(f"[build] Building {paper_id} Lean...")
        # Try with -R flag if configuration is invalid
        result = subprocess.run(
            ["lake", "build"],
            cwd=proofs_dir,
            capture_output=True,
            text=True,
        )
        if "compiled configuration is invalid" in result.stderr:
            print(f"[build] Reconfiguring {paper_id} Lean...")
            result = subprocess.run(
                ["lake", "build", "-R"],
                cwd=proofs_dir,
                capture_output=True,
                text=True,
            )
        if result.returncode != 0:
            raise RuntimeError(
                f"Lean build failed for {paper_id}:\n{result.stderr}"
            )
        print(f"[build] {paper_id} Lean complete")

    def build_latex(self, paper_id: str):
        """Build LaTeX PDF for a paper."""
        paper_dir = self._get_paper_dir(paper_id)
        paper_meta = self.metadata["papers"][paper_id]
        latex_dir = paper_dir / paper_meta["latex_dir"]
        latex_file = latex_dir / paper_meta["latex_file"]

        if not latex_file.exists():
            raise FileNotFoundError(f"LaTeX file not found: {latex_file}")

        self._update_paper_date(latex_file)

        print(f"[build] Building {paper_id} LaTeX...")
        result = subprocess.run(
            ["pdflatex", "-interaction=nonstopmode", latex_file.name],
            cwd=latex_dir,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            print(f"[build] LaTeX build had warnings/errors (continuing)")
        print(f"[build] {paper_id} PDF → {latex_dir.relative_to(self.repo_root)}")

    def build_markdown(self, paper_id: str):
        """Build Markdown version of a paper."""
        paper_dir = self._get_paper_dir(paper_id)
        paper_meta = self.metadata["papers"][paper_id]
        content_dir = paper_dir / "shared" / "content"
        out_dir = paper_dir / "markdown"
        out_file = out_dir / f"{paper_meta['dir']}.md"

        if not content_dir.exists():
            print(f"[build-md] Skipping {paper_id}: no shared/content directory")
            return

        out_dir.mkdir(parents=True, exist_ok=True)

        print(f"[build-md] Building {paper_id}: {paper_meta['name']}...")

        # Build markdown from content files
        self._build_markdown_file(
            paper_meta, content_dir, out_file
        )
        print(f"[build-md] {paper_id} → {out_file.relative_to(self.repo_root)}")

    def _build_markdown_file(
        self, meta: dict, content_dir: Path, out_file: Path
    ):
        """Generate markdown file from LaTeX content."""
        with open(out_file, "w") as f:
            # Header
            f.write(f"# Paper: {meta['full_name']}\n\n")
            f.write(
                f"**Status**: TOPLAS-ready | "
                f"**Lean**: {meta['lean_lines']} lines, "
                f"{meta['lean_theorems']} theorems, "
                f"{meta['lean_sorry']} sorry\n\n---\n\n"
            )

            # Abstract
            f.write("## Abstract\n\n")
            abstract_file = content_dir / "abstract.tex"
            if abstract_file.exists():
                self._convert_latex_to_markdown(abstract_file, f)
            else:
                f.write("_Abstract not available._\n\n")

            # Content sections
            for content_file in meta["content_files"]:
                content_path = content_dir / content_file
                if content_path.exists():
                    self._convert_latex_to_markdown(content_path, f)
                else:
                    print(f"[build-md] Warning: missing {content_file}")

            # Footer
            f.write("\n\n---\n\n## Machine-Checked Proofs\n\n")
            f.write(f"All theorems are formalized in Lean 4:\n")
            f.write(f"- Location: `docs/papers/{meta['dir']}/proofs/`\n")
            f.write(f"- Lines: {meta['lean_lines']}\n")
            f.write(f"- Theorems: {meta['lean_theorems']}\n")
            f.write(f"- Sorry placeholders: {meta['lean_sorry']}\n")

    def _convert_latex_to_markdown(self, tex_file: Path, out_file):
        """Convert LaTeX file to Markdown using pandoc."""
        result = subprocess.run(
            [
                "pandoc",
                str(tex_file),
                "-f", "latex",
                "-t", "markdown",
                "--wrap=none",
                "--columns=100",
            ],
            capture_output=True,
            text=True,
        )
        if result.returncode == 0 and result.stdout:
            out_file.write(result.stdout)
            out_file.write("\n\n")
        else:
            out_file.write(f"_Failed to convert {tex_file.name}_\n\n")

    def _update_paper_date(self, tex_file: Path):
        """Update publication date in LaTeX file."""
        today = datetime.now().strftime("%B %-d, %Y")
        year = datetime.now().strftime("%Y")
        content = tex_file.read_text()
        content = content.replace(r"\date{", f"\\date{{{today}}}")
        content = content.replace(r"\copyrightyear{", f"\\copyrightyear{{{year}}}")
        content = content.replace(r"\acmYear{", f"\\acmYear{{{year}}}")
        tex_file.write_text(content)

    def build_all(self, build_type: str = "all"):
        """Build all papers of specified type."""
        paper_ids = list(self.metadata["papers"].keys())

        if build_type in ("all", "lean"):
            for paper_id in paper_ids:
                try:
                    self.build_lean(paper_id)
                except Exception as e:
                    print(f"[build] ERROR: {e}")

        if build_type in ("all", "latex"):
            for paper_id in paper_ids:
                try:
                    self.build_latex(paper_id)
                except Exception as e:
                    print(f"[build] ERROR: {e}")

        if build_type in ("all", "markdown"):
            for paper_id in paper_ids:
                try:
                    self.build_markdown(paper_id)
                except Exception as e:
                    print(f"[build-md] ERROR: {e}")


def main():
    parser = argparse.ArgumentParser(
        description="Unified TOPLAS paper builder"
    )
    parser.add_argument(
        "build_type",
        nargs="?",
        default="all",
        choices=["all", "lean", "latex", "markdown"],
        help="What to build",
    )
    parser.add_argument(
        "paper",
        nargs="?",
        default="all",
        help="Which paper (paper1-5 or all)",
    )

    args = parser.parse_args()
    repo_root = Path(__file__).parent.parent

    try:
        builder = PaperBuilder(repo_root)
        if args.paper == "all":
            builder.build_all(args.build_type)
        else:
            if args.build_type in ("all", "lean"):
                builder.build_lean(args.paper)
            if args.build_type in ("all", "latex"):
                builder.build_latex(args.paper)
            if args.build_type in ("all", "markdown"):
                builder.build_markdown(args.paper)
    except Exception as e:
        print(f"[build] FATAL: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()

