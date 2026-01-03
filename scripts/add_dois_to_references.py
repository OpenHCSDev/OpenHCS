#!/usr/bin/env python3
"""
Script to look up DOIs for BibTeX entries and add them to the references.
Uses CrossRef API to resolve citations.
"""

import re
import json
import time
import requests
from pathlib import Path
from typing import Optional, Dict, List, Tuple

# CrossRef API settings
CROSSREF_API = "https://api.crossref.org/works"
EMAIL = "research@example.com"


def lookup_doi(title: str, author: str = "", year: str = "") -> Optional[str]:
    """Look up DOI for a citation using CrossRef API."""
    # Build query - use just title for cleaner results
    query = title
    
    try:
        headers = {"User-Agent": f"DoiLookup/1.0 (mailto:{EMAIL})"}
        params = {"query": query, "rows": 5}
        
        response = requests.get(CROSSREF_API, params=params, headers=headers, timeout=15)
        
        if response.status_code == 200:
            data = response.json()
            items = data.get('message', {}).get('items', [])
            
            for item in items:
                # Check if title matches closely
                item_title = item.get('title', [''])[0].lower()
                title_lower = title.lower()
                
                # Check for significant overlap
                if item_title and (title_lower in item_title or item_title in title_lower):
                    doi = item.get('DOI')
                    if doi:
                        return doi
                
                # Also try first author matching
                if author and year:
                    authors = item.get('author', [])
                    if authors:
                        first_author = authors[0].get('family', '').lower()
                        if first_author and first_author in author.lower():
                            pub_year = str(item.get('published-print', {}).get('date-parts', [['']])[0][0])
                            if year in pub_year or pub_year in year:
                                doi = item.get('DOI')
                                if doi:
                                    return doi
        
        time.sleep(0.5)  # Rate limiting
        
    except Exception as e:
        print(f"    API error: {e}")
    
    return None


def add_dois_to_bibtex_file(filepath: Path) -> int:
    """Process a single BibTeX file and add DOIs."""
    print(f"\nProcessing: {filepath}")
    
    content = filepath.read_text()
    lines = content.split('\n')
    
    new_lines = []
    dois_added = 0
    current_entry_type = None
    current_entry_key = None
    in_entry = False
    brace_depth = 0
    entry_lines = []
    entry_has_doi = False
    
    for i, line in enumerate(lines):
        stripped = line.strip()
        
        # Check for entry start
        entry_match = re.match(r'^@(\w+)\s*\{\s*([^,]+),', stripped)
        if entry_match:
            # Save previous entry if any
            if in_entry and not entry_has_doi and current_entry_type not in ['misc', 'manual']:
                # Look up DOI for this entry
                title = None
                author = None
                year = None
                for field_line in entry_lines:
                    field_match = re.match(r'(\w+)\s*=\s*\{(.+)\}', field_line.strip())
                    if field_match:
                        key = field_match.group(1).lower()
                        value = field_match.group(2)
                        if key == 'title':
                            title = value
                        elif key == 'author':
                            author = value
                        elif key == 'year':
                            year = value
                
                if title and current_entry_type in ['article', 'inproceedings', 'incollection', 'book', 'phdthesis', 'phdthesis']:
                    print(f"  Looking up: {title[:50]}...")
                    doi = lookup_doi(title, author, year)
                    if doi:
                        print(f"    Found: {doi}")
                        # Insert DOI before closing brace
                        insert_idx = len(new_lines)
                        for j, l in enumerate(new_lines):
                            if l.strip() == '}':
                                insert_idx = j
                                break
                        new_lines.insert(insert_idx, f"  doi = {{{doi}}},")
                        dois_added += 1
                    else:
                        print(f"    Not found")
                else:
                    print(f"  Skipping: {current_entry_key or 'unknown'} (type: {current_entry_type})")
            
            # Start new entry
            current_entry_type = entry_match.group(1).lower()
            current_entry_key = entry_match.group(2).strip()
            in_entry = True
            entry_lines = []
            entry_has_doi = 'doi' in line.lower()
            new_lines.append(line)
            brace_depth = line.count('{') - line.count('}')
            continue
        
        if in_entry:
            entry_lines.append(line)
            
            # Check if this is a DOI field
            if re.match(r'^\s*doi\s*=', stripped, re.IGNORECASE):
                entry_has_doi = True
            
            # Track brace depth
            brace_depth += line.count('{') - line.count('}')
            
            # Check for entry end
            if stripped == '}' and brace_depth == 0:
                # Save this entry
                new_lines.append(line)
                
                # Process next entry
                if not entry_has_doi and current_entry_type not in ['misc', 'manual']:
                    title = None
                    author = None
                    year = None
                    for field_line in entry_lines:
                        field_match = re.match(r'(\w+)\s*=\s*\{(.+)\}', field_line.strip())
                        if field_match:
                            key = field_match.group(1).lower()
                            value = field_match.group(2)
                            if key == 'title':
                                title = value
                            elif key == 'author':
                                author = value
                            elif key == 'year':
                                year = value
                    
                    if title and current_entry_type in ['article', 'inproceedings', 'incollection', 'book', 'phdthesis']:
                        print(f"  Looking up: {title[:50]}...")
                        doi = lookup_doi(title, author, year)
                        if doi:
                            print(f"    Found: {doi}")
                            # Insert DOI after the last field
                            insert_idx = len(new_lines) - 1
                            while insert_idx > 0 and new_lines[insert_idx-1].strip().startswith('@'):
                                insert_idx -= 1
                            new_lines.insert(insert_idx, f"  doi = {{{doi}}},")
                            dois_added += 1
                        else:
                            print(f"    Not found")
                    else:
                        print(f"  Skipping: {current_entry_key or 'unknown'} (type: {current_entry_type}, title: {bool(title)})")
                
                # Reset for next entry
                in_entry = False
                current_entry_type = None
                current_entry_key = None
                entry_lines = []
                entry_has_doi = False
            else:
                new_lines.append(line)
        else:
            new_lines.append(line)
    
    # Handle last entry
    if in_entry and not entry_has_doi and current_entry_type not in ['misc', 'manual']:
        title = None
        author = None
        year = None
        for field_line in entry_lines:
            field_match = re.match(r'(\w+)\s*=\s*\{(.+)\}', field_line.strip())
            if field_match:
                key = field_match.group(1).lower()
                value = field_match.group(2)
                if key == 'title':
                    title = value
                elif key == 'author':
                    author = value
                elif key == 'year':
                    year = value
        
        if title and current_entry_type in ['article', 'inproceedings', 'incollection', 'book', 'phdthesis']:
            print(f"  Looking up: {title[:50]}...")
            doi = lookup_doi(title, author, year)
            if doi:
                print(f"    Found: {doi}")
                insert_idx = len(new_lines)
                while insert_idx > 0 and new_lines[insert_idx-1].strip() != '}':
                    insert_idx -= 1
                new_lines.insert(insert_idx, f"  doi = {{{doi}}},")
                dois_added += 1
            else:
                print(f"    Not found")
    
    # Write updated content
    if dois_added > 0:
        filepath.write_text('\n'.join(new_lines))
        print(f"  Added {dois_added} DOIs")
    
    return dois_added


def main():
    """Main function to process all BibTeX files."""
    papers_dir = Path("docs/papers")
    
    # List of reference files to process
    ref_files = [
        papers_dir / "paper1_typing_discipline" / "shared" / "references.bib",
        papers_dir / "paper2_ssot" / "shared" / "references.bib",
        papers_dir / "paper3_leverage" / "latex" / "references.bib",
        papers_dir / "paper4_decision_quotient" / "latex" / "references.bib",
        papers_dir / "paper5_credibility" / "latex" / "references.bib",
    ]
    
    total_dois = 0
    
    for filepath in ref_files:
        if filepath.exists():
            count = add_dois_to_bibtex_file(filepath)
            total_dois += count
        else:
            print(f"File not found: {filepath}")
    
    print(f"\n{'='*60}")
    print(f"Total DOIs added: {total_dois}")
    print(f"{'='*60}")


if __name__ == "__main__":
    main()
