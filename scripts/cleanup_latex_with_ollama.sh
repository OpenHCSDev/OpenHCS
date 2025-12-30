#!/bin/bash
# Use Ollama to clean up LaTeX conversion

set -e

ARXIV_TEX="docs/papers/latex/arxiv_version.tex"
TOPLAS_TEX="docs/papers/latex/toplas_version.tex"

if ! command -v ollama &> /dev/null; then
    echo "Error: Ollama not installed. Install with:"
    echo "  curl -fsSL https://ollama.com/install.sh | sh"
    exit 1
fi

echo "Checking if model is available..."
if ! ollama list | grep -q "qwen2.5-coder:32b"; then
    echo "Pulling qwen2.5-coder:32b model (this may take a while)..."
    ollama pull qwen2.5-coder:32b
fi

echo "Step 1: Fixing theorem environments in arXiv version..."
cat > /tmp/theorem_prompt.txt << 'EOF'
You are a LaTeX expert. Fix the following issues in this LaTeX document:

1. Convert theorem statements from Markdown to amsthm environments:
   - **Theorem X.Y (Name).** → \begin{theorem}[Name]\label{thm:X.Y}
   - **Lemma X.Y (Name).** → \begin{lemma}[Name]\label{lem:X.Y}
   - **Corollary X.Y (Name).** → \begin{corollary}[Name]\label{cor:X.Y}
   - **Definition X.Y (Name).** → \begin{definition}[Name]\label{def:X.Y}

2. Convert proofs:
   - *Proof.* → \begin{proof}
   - $\blacksquare$ → \end{proof}

3. Add proper preamble packages:
   - \usepackage{amsthm}
   - \usepackage{amsmath}
   - \usepackage{amssymb}
   - \usepackage{listings}
   - \usepackage{hyperref}

4. Fix code blocks:
   - Convert to \begin{lstlisting}[language=Python]

Only output the corrected LaTeX. Do not add explanations.
EOF

echo "Processing with Ollama (this may take 5-10 minutes)..."
ollama run qwen2.5-coder:32b "$(cat /tmp/theorem_prompt.txt)\n\n$(cat $ARXIV_TEX)" > /tmp/arxiv_cleaned.tex

echo "Step 2: Adding arXiv-specific header..."
cat > /tmp/arxiv_header.txt << 'EOF'
% arXiv submission version
% Submitted to ACM TOPLAS

\documentclass[11pt]{article}
\usepackage{arxiv}  % arXiv style package
\usepackage{amsmath,amssymb,amsthm}
\usepackage{listings}
\usepackage{hyperref}
\usepackage{booktabs}
\usepackage{graphicx}

\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{definition}[theorem]{Definition}

\lstset{
  basicstyle=\ttfamily\small,
  breaklines=true,
  frame=single
}

\title{Typing Discipline Selection for Object-Oriented Systems:\\
A Formal Methodology with Empirical Validation}

\author{
  Your Name \\
  Your Institution \\
  \texttt{your.email@institution.edu}
}

\begin{document}
\maketitle
EOF

# Combine header with cleaned content
cat /tmp/arxiv_header.txt > "$ARXIV_TEX.new"
tail -n +10 /tmp/arxiv_cleaned.tex >> "$ARXIV_TEX.new"  # Skip pandoc's header
mv "$ARXIV_TEX.new" "$ARXIV_TEX"

echo "Step 3: Creating TOPLAS version with ACM template..."
cat > /tmp/toplas_header.txt << 'EOF'
% TOPLAS submission version

\documentclass[acmtoplas,screen,review,anonymous]{acmart}

\usepackage{amsmath,amssymb,amsthm}
\usepackage{listings}
\usepackage{booktabs}

\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{definition}[theorem]{Definition}

\lstset{
  basicstyle=\ttfamily\small,
  breaklines=true,
  frame=single
}

\begin{document}

\title{Typing Discipline Selection for Object-Oriented Systems:\\
A Formal Methodology with Empirical Validation}

\author{Your Name}
\affiliation{Your Institution}
\email{your.email@institution.edu}

\begin{abstract}
EOF

# Create TOPLAS version
cat /tmp/toplas_header.txt > "$TOPLAS_TEX"
# Extract abstract and body from cleaned version
tail -n +10 /tmp/arxiv_cleaned.tex >> "$TOPLAS_TEX"

echo ""
echo "✓ Cleanup complete!"
echo ""
echo "Files created:"
echo "  - $ARXIV_TEX (ready for arXiv)"
echo "  - $TOPLAS_TEX (ready for TOPLAS)"
echo ""
echo "Next steps:"
echo "1. Review the LaTeX files (especially theorems and math)"
echo "2. Add your name/affiliation"
echo "3. Create references.bib file"
echo "4. Compile with: pdflatex $ARXIV_TEX"
echo "5. Upload to arXiv"

