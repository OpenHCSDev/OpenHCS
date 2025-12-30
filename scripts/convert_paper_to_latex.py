#!/usr/bin/env python3
"""
Convert the nominal typing paper from Markdown to LaTeX with proper theorem environments.
"""

import re
import sys

def convert_theorems(text):
    """Convert theorem-like environments from Markdown to LaTeX."""
    
    # Theorem
    text = re.sub(
        r'\*\*Theorem (\d+\.\d+[a-z]?) \(([^)]+)\)\.\*\*',
        r'\\begin{theorem}[\\textbf{\2}]\\label{thm:\1}',
        text
    )
    
    # Lemma
    text = re.sub(
        r'\*\*Lemma (\d+\.\d+[a-z]?) \(([^)]+)\)\.\*\*',
        r'\\begin{lemma}[\\textbf{\2}]\\label{lem:\1}',
        text
    )
    
    # Corollary
    text = re.sub(
        r'\*\*Corollary (\d+\.\d+[a-z]?) \(([^)]+)\)\.\*\*',
        r'\\begin{corollary}[\\textbf{\2}]\\label{cor:\1}',
        text
    )
    
    # Definition
    text = re.sub(
        r'\*\*Definition (\d+\.\d+[a-z]?) \(([^)]+)\)\.\*\*',
        r'\\begin{definition}[\\textbf{\2}]\\label{def:\1}',
        text
    )
    
    # Observation/Remark
    text = re.sub(
        r'\*\*Observation (\d+\.\d+[a-z]?) \(([^)]+)\)\.\*\*',
        r'\\begin{remark}[\\textbf{\2}]\\label{obs:\1}',
        text
    )
    
    text = re.sub(
        r'\*\*Remark \(([^)]+)\)\.\*\*',
        r'\\begin{remark}[\\textbf{\1}]',
        text
    )
    
    # Proofs
    text = re.sub(r'\*Proof\.\*', r'\\begin{proof}', text)
    text = re.sub(r'\$\\blacksquare\$', r'\\end{proof}', text)
    
    # Close theorem environments before next section/theorem
    # This is a heuristic - we'll need to manually verify
    
    return text

def create_arxiv_preamble():
    """Create arXiv-compatible preamble."""
    return r"""\documentclass[11pt]{article}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{graphicx}
\usepackage{xcolor}
\usepackage{booktabs}
\usepackage{longtable}
\usepackage{fancyvrb}
\usepackage{geometry}
\usepackage{hyperref}

\geometry{margin=1in}

% Fix for pandoc's \tightlist
\providecommand{\tightlist}{%
  \setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}

% Theorem environments
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{proposition}[theorem]{Proposition}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{example}[theorem]{Example}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\newtheorem{observation}[theorem]{Observation}

% Hyperref setup
\hypersetup{
  colorlinks=true,
  linkcolor=blue,
  citecolor=blue,
  urlcolor=blue
}

\title{Typing Discipline Selection for Object-Oriented Systems:\\
A Formal Methodology with Empirical Validation}

\author{
  Anonymous Author(s)\\
  \textit{Submitted to ACM TOPLAS}
}

\date{\today}

\begin{document}
\maketitle

\begin{abstract}
"""

def create_toplas_preamble():
    """Create TOPLAS ACM template preamble."""
    return r"""\documentclass[acmtoplas,screen,review,anonymous]{acmart}

\usepackage{longtable}
\usepackage{booktabs}
\usepackage{array}
\usepackage{calc}
\usepackage{amssymb}

% Fix for pandoc-generated tables
\newcolumntype{L}[1]{>{\raggedright\arraybackslash}p{#1}}
\newcolumntype{C}[1]{>{\centering\arraybackslash}p{#1}}
\newcolumntype{R}[1]{>{\raggedleft\arraybackslash}p{#1}}

% Fix for \real command (used by pandoc)
\providecommand{\real}[1]{#1}

% Fix for QED symbol
\providecommand{\blacksquare}{\ensuremath{\square}}

% Theorem environments
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{proposition}[theorem]{Proposition}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{example}[theorem]{Example}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\newtheorem{observation}[theorem]{Observation}

% Fix for pandoc's \tightlist
\providecommand{\tightlist}{%
  \setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}

\begin{document}

\title{Typing Discipline Selection for Object-Oriented Systems: A Formal Methodology with Empirical Validation}

\author{Anonymous Author}
\affiliation{Anonymous Institution}
\email{anonymous@example.com}

\begin{abstract}
"""

def process_file(input_file, output_file, preamble_func):
    """Process the pandoc output and add proper theorem environments."""
    with open(input_file, 'r') as f:
        content = f.read()

    # Convert theorem environments
    content = convert_theorems(content)

    # Extract abstract and body
    # Find where the actual content starts (after pandoc's preamble)
    doc_start = content.find(r'\begin{document}')
    if doc_start == -1:
        print("Error: Could not find \\begin{document}")
        return False

    body = content[doc_start + len(r'\begin{document}'):]

    # Create new document
    new_content = preamble_func()
    new_content += body

    # Write output
    with open(output_file, 'w') as f:
        f.write(new_content)

    return True

if __name__ == "__main__":
    if len(sys.argv) < 4:
        print("Usage: python convert_paper_to_latex.py <input.tex> <output.tex> <arxiv|toplas>")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2]
    version = sys.argv[3]

    if version == "arxiv":
        preamble = create_arxiv_preamble
    elif version == "toplas":
        preamble = create_toplas_preamble
    else:
        print(f"Unknown version: {version}")
        sys.exit(1)

    if process_file(input_file, output_file, preamble):
        print(f"✓ Created {output_file}")
    else:
        print(f"✗ Failed to create {output_file}")
        sys.exit(1)

