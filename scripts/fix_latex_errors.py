#!/usr/bin/env python3
"""
Fix common LaTeX compilation errors in the converted paper.
"""

import re
import sys

def fix_code_blocks(content):
    """Replace problematic Shaded/Highlighting environments with simple verbatim."""

    # Pattern to match code blocks
    # Replace Shaded environment with verbatim
    content = re.sub(
        r'\\begin\{Shaded\}.*?\\begin\{Highlighting\}\[\].*?\\end\{Highlighting\}.*?\\end\{Shaded\}',
        lambda m: convert_to_lstlisting(m.group(0)),
        content,
        flags=re.DOTALL
    )

    # Also convert any remaining lstlisting to verbatim for safety
    content = re.sub(
        r'\\begin\{lstlisting\}(?:\[.*?\])?(.*?)\\end\{lstlisting\}',
        r'\\begin{verbatim}\1\\end{verbatim}',
        content,
        flags=re.DOTALL
    )

    return content

def convert_to_lstlisting(shaded_block):
    """Convert a Shaded block to verbatim (simpler, more reliable)."""

    # Extract the code content
    # Remove all the highlighting commands
    code = shaded_block

    # Remove Shaded and Highlighting wrappers
    code = re.sub(r'\\begin\{Shaded\}', '', code)
    code = re.sub(r'\\end\{Shaded\}', '', code)
    code = re.sub(r'\\begin\{Highlighting\}\[\]', '', code)
    code = re.sub(r'\\end\{Highlighting\}', '', code)

    # Remove all highlighting commands but keep the text
    code = re.sub(r'\\[A-Z][a-zA-Z]*Tok\{([^}]*)\}', r'\1', code)
    code = re.sub(r'\\NormalTok\{([^}]*)\}', r'\1', code)

    # Clean up
    code = code.strip()

    # Use simple verbatim - more reliable than lstlisting
    return f'\\begin{{verbatim}}\n{code}\n\\end{{verbatim}}'

def fix_tables(content):
    """Fix table formatting issues."""
    
    # Add \small before longtable environments
    content = re.sub(
        r'(\\begin\{longtable\})',
        r'\\small\n\1',
        content
    )
    
    return content

def fix_math_mode_errors(content):
    """Fix common math mode errors."""

    # Fix \textbackslash in math mode
    content = re.sub(
        r'\\textbackslash',
        r'\\backslash',
        content
    )

    return content

def fix_unicode_chars(content):
    """Replace Unicode math characters with LaTeX commands."""

    replacements = {
        'Ω': r'$\\Omega$',
        'ω': r'$\\omega$',
        '≠': r'$\\neq$',
        '∅': r'$\\emptyset$',
        '∞': r'$\\infty$',
        '≤': r'$\\leq$',
        '≥': r'$\\geq$',
        '∈': r'$\\in$',
        '∉': r'$\\notin$',
        '⊆': r'$\\subseteq$',
        '⊂': r'$\\subset$',
        '∪': r'$\\cup$',
        '∩': r'$\\cap$',
        '→': r'$\\rightarrow$',
        '←': r'$\\leftarrow$',
        '⇒': r'$\\Rightarrow$',
        '⇐': r'$\\Leftarrow$',
        '∀': r'$\\forall$',
        '∃': r'$\\exists$',
        '¬': r'$\\neg$',
        '∧': r'$\\wedge$',
        '∨': r'$\\vee$',
        '×': r'$\\times$',
        '÷': r'$\\div$',
        '±': r'$\\pm$',
        '∓': r'$\\mp$',
        '√': r'$\\sqrt{}$',
        '∑': r'$\\sum$',
        '∏': r'$\\prod$',
        '∫': r'$\\int$',
        '⊕': r'$\\oplus$',
        '⊗': r'$\\otimes$',
        '⊥': r'$\\perp$',
        '∥': r'$\\parallel$',
        '≡': r'$\\equiv$',
        '≈': r'$\\approx$',
        '∼': r'$\\sim$',
        '≃': r'$\\simeq$',
        '⊢': r'$\\vdash$',
        '⊨': r'$\\models$',
    }

    for unicode_char, latex_cmd in replacements.items():
        content = content.replace(unicode_char, latex_cmd)

    return content

def fix_table_columns(content):
    """Fix table column specifications that have illegal characters."""

    # Find longtable environments and fix column specs
    def fix_column_spec(match):
        spec = match.group(1)
        # Remove any illegal characters, keep only l, r, c, p{}, |
        # Common issue: @ character or other special chars
        spec = re.sub(r'[^lrcpX\|\{\}\.\d\\]', '', spec)
        return f'\\begin{{longtable}}{{{spec}}}'

    content = re.sub(
        r'\\begin\{longtable\}\{([^}]+)\}',
        fix_column_spec,
        content
    )

    return content

def add_missing_packages(content):
    """Add missing package declarations."""
    
    # Check if fancyvrb is already there
    if r'\usepackage{fancyvrb}' not in content:
        # Add after other usepackage declarations
        content = re.sub(
            r'(\\usepackage\{xcolor\})',
            r'\1\n\\usepackage{fancyvrb}',
            content
        )
    
    return content

def main():
    if len(sys.argv) < 2:
        print("Usage: python fix_latex_errors.py <file.tex>")
        sys.exit(1)
    
    filename = sys.argv[1]
    
    print(f"Fixing LaTeX errors in {filename}...")
    
    with open(filename, 'r') as f:
        content = f.read()
    
    original_size = len(content)
    
    # Apply fixes
    print("  - Fixing Unicode characters...")
    content = fix_unicode_chars(content)

    print("  - Fixing code blocks...")
    content = fix_code_blocks(content)

    print("  - Fixing tables...")
    content = fix_tables(content)

    print("  - Fixing table columns...")
    content = fix_table_columns(content)

    print("  - Fixing math mode errors...")
    content = fix_math_mode_errors(content)

    print("  - Adding missing packages...")
    content = add_missing_packages(content)
    
    # Write back
    with open(filename, 'w') as f:
        f.write(content)
    
    new_size = len(content)
    print(f"✓ Fixed {filename}")
    print(f"  Size: {original_size} → {new_size} bytes ({new_size - original_size:+d})")

if __name__ == "__main__":
    main()

