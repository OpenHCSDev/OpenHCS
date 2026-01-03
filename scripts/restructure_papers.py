#!/usr/bin/env python3
"""
Restructure papers 3-5 to match papers 1-2 layout.
Splits content.tex into individual section files in shared/content/.
"""

import re
from pathlib import Path

def split_content_file(paper_name: str, content_file: Path, output_dir: Path):
    """Split content.tex into individual section files."""
    output_dir.mkdir(parents=True, exist_ok=True)
    
    content = content_file.read_text()
    
    # Split by \section{...}
    sections = re.split(r'(\\section\{[^}]+\})', content)
    
    file_counter = 1
    current_section = None
    
    for i, part in enumerate(sections):
        if part.startswith('\\section{'):
            current_section = part
        elif current_section and part.strip():
            # Extract section title for filename
            title_match = re.search(r'\\section\{([^}]+)\}', current_section)
            if title_match:
                title = title_match.group(1).lower()
                title = re.sub(r'[^a-z0-9]+', '_', title).strip('_')
                
                # Create filename with counter
                filename = f"{file_counter:02d}_{title}.tex"
                filepath = output_dir / filename
                
                # Write section header + content
                section_content = current_section + part
                filepath.write_text(section_content)
                print(f"  Created {filename}")
                
                file_counter += 1
                current_section = None

# Process papers 3-5
papers = {
    'paper3_leverage': '/home/ts/code/projects/openhcs-sequential/docs/papers/paper3_leverage',
    'paper4_decision_quotient': '/home/ts/code/projects/openhcs-sequential/docs/papers/paper4_decision_quotient',
    'paper5_credibility': '/home/ts/code/projects/openhcs-sequential/docs/papers/paper5_credibility',
}

for paper_name, paper_path in papers.items():
    paper_dir = Path(paper_path)
    content_file = paper_dir / 'latex' / 'content.tex'
    output_dir = paper_dir / 'shared' / 'content'
    
    if content_file.exists():
        print(f"\nProcessing {paper_name}...")
        split_content_file(paper_name, content_file, output_dir)
    else:
        print(f"Skipping {paper_name}: no content.tex found")

print("\nDone!")

