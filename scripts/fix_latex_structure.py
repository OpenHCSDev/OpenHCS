#!/usr/bin/env python3
"""
Fix the LaTeX structure after pandoc conversion.
"""

import re
import sys

def fix_structure(content):
    """Fix document structure issues."""
    
    # Remove duplicate title section that pandoc created
    content = re.sub(
        r'\\section\{Typing Discipline Selection for Object-Oriented\s+Systems\}.*?\\begin\{center\}\\rule.*?\\end\{center\}',
        '',
        content,
        flags=re.DOTALL
    )
    
    # Find the abstract content (after "### Abstract" heading)
    abstract_match = re.search(
        r'\\subsection\{Abstract\}\\label\{abstract\}(.*?)\\begin\{center\}\\rule',
        content,
        flags=re.DOTALL
    )
    
    if abstract_match:
        abstract_content = abstract_match.group(1).strip()
        
        # Remove the subsection version
        content = re.sub(
            r'\\subsection\{Abstract\}\\label\{abstract\}.*?\\begin\{center\}\\rule.*?\\end\{center\}',
            '',
            content,
            flags=re.DOTALL
        )
        
        # Insert proper abstract after \begin{abstract}
        content = content.replace(
            r'\begin{abstract}',
            r'\begin{abstract}' + '\n' + abstract_content + '\n' + r'\end{abstract}'
        )
    
    # Fix section numbering - remove "1." prefix from Introduction
    content = re.sub(r'\\subsection\{1\. Introduction\}', r'\\section{Introduction}', content)
    content = re.sub(r'\\subsection\{(\d+)\. ([^}]+)\}', r'\\section{\2}', content)
    content = re.sub(r'\\subsubsection\{(\d+\.\d+) ([^}]+)\}', r'\\subsection{\2}', content)
    
    return content

def close_theorem_environments(content):
    """Add \\end{theorem} etc. where needed."""
    
    # This is tricky - we need to close theorem environments before the next theorem or section
    # For now, let's add a simple heuristic
    
    # Find all theorem-like beginnings
    theorem_pattern = r'(\\begin\{(?:theorem|lemma|corollary|definition|remark|proof)\})'
    
    lines = content.split('\n')
    result = []
    in_theorem = None
    
    for line in lines:
        # Check if we're starting a new theorem-like environment
        match = re.search(r'\\begin\{(theorem|lemma|corollary|definition|remark|proof)\}', line)
        if match:
            # Close previous theorem if any
            if in_theorem and in_theorem != 'proof':
                result.append(f'\\end{{{in_theorem}}}')
            in_theorem = match.group(1)
            result.append(line)
            continue
        
        # Check if we're ending proof
        if r'\end{proof}' in line:
            in_theorem = None
            result.append(line)
            continue
        
        # Check if we hit a new section - close any open theorem
        if re.match(r'\\(sub)*section\{', line):
            if in_theorem and in_theorem != 'proof':
                result.append(f'\\end{{{in_theorem}}}')
                in_theorem = None
        
        result.append(line)
    
    # Close any remaining open theorem
    if in_theorem and in_theorem != 'proof':
        result.append(f'\\end{{{in_theorem}}}')
    
    return '\n'.join(result)

def main():
    if len(sys.argv) < 2:
        print("Usage: python fix_latex_structure.py <file.tex>")
        sys.exit(1)
    
    filename = sys.argv[1]
    
    with open(filename, 'r') as f:
        content = f.read()
    
    # Apply fixes
    content = fix_structure(content)
    content = close_theorem_environments(content)
    
    # Write back
    with open(filename, 'w') as f:
        f.write(content)
    
    print(f"✓ Fixed structure in {filename}")

if __name__ == "__main__":
    main()

