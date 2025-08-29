#!/usr/bin/env python3
"""
Script to remove unused citations from references.bib

This script:
1. Scans all .tex files in the project directory
2. Finds all citation keys used in \cite{} commands
3. Removes unused entries from references.bib
4. Creates a backup of the original references.bib
"""

import os
import re
import glob
import shutil
from pathlib import Path

def extract_citation_keys_from_tex_files(tex_directory):
    """Extract all citation keys used in \cite{} commands from .tex files"""
    citation_keys = set()
    
    # Find all .tex files in the directory and subdirectories
    tex_files = glob.glob(os.path.join(tex_directory, "**/*.tex"), recursive=True)
    
    for tex_file in tex_files:
        try:
            with open(tex_file, 'r', encoding='utf-8') as f:
                content = f.read()
                
                # Find all \cite{...} patterns
                # This regex handles multiple citations like \cite{ref1, ref2, ref3}
                cite_pattern = r'\\cite\{([^}]+)\}'
                matches = re.findall(cite_pattern, content)
                
                for match in matches:
                    # Split on commas and clean whitespace
                    keys = [key.strip() for key in match.split(',')]
                    citation_keys.update(keys)
                    
                # Also look for \nocite{} commands
                nocite_pattern = r'\\nocite\{([^}]+)\}'
                nocite_matches = re.findall(nocite_pattern, content)
                
                for match in nocite_matches:
                    keys = [key.strip() for key in match.split(',')]
                    citation_keys.update(keys)
                    
        except Exception as e:
            print(f"Error reading {tex_file}: {e}")
    
    print(f"Found {len(citation_keys)} citation keys used in .tex files")
    return citation_keys

def parse_bib_file(bib_file):
    """Parse the .bib file and extract all entry keys and their content"""
    entries = {}
    
    try:
        with open(bib_file, 'r', encoding='utf-8') as f:
            content = f.read()
            
            # Pattern to match BibTeX entries
            # This handles @article{key, @book{key, @inproceedings{key, etc.
            entry_pattern = r'@\w+\{([^,\s]+),\s*\n((?:[^@]|@(?!\w+\{))*?)(?=@\w+\{|\Z)'
            
            matches = re.finditer(entry_pattern, content, re.MULTILINE | re.DOTALL)
            
            for match in matches:
                key = match.group(1).strip()
                full_entry = f"@{match.group(0)}"
                entries[key] = full_entry
                
    except Exception as e:
        print(f"Error reading {bib_file}: {e}")
        return {}
    
    print(f"Found {len(entries)} entries in bibliography file")
    return entries

def write_filtered_bib_file(bib_file, used_keys, all_entries):
    """Write a new .bib file containing only the used entries"""
    
    # Create backup
    backup_file = bib_file + '.backup'
    shutil.copy2(bib_file, backup_file)
    print(f"Created backup at {backup_file}")
    
    used_entries = []
    unused_keys = []
    
    for key, entry in all_entries.items():
        if key in used_keys:
            used_entries.append(entry)
        else:
            unused_keys.append(key)
    
    print(f"Removing {len(unused_keys)} unused entries:")
    for key in sorted(unused_keys):
        print(f"  - {key}")
    
    # Write the filtered bibliography
    try:
        with open(bib_file, 'w', encoding='utf-8') as f:
            # Add header comment
            f.write("% References for \"The Squiggly Line Conjecture\" paper\n")
            f.write("% Automatically cleaned to remove unused citations\n\n")
            
            # Sort entries alphabetically by key for consistency
            sorted_entries = sorted(used_entries, key=lambda x: re.search(r'@\w+\{([^,\s]+)', x).group(1).lower())
            
            for i, entry in enumerate(sorted_entries):
                f.write(entry)
                if i < len(sorted_entries) - 1:
                    f.write("\n\n")
                else:
                    f.write("\n")
                    
    except Exception as e:
        print(f"Error writing filtered bibliography: {e}")
        # Restore from backup if there was an error
        shutil.copy2(backup_file, bib_file)
        return False
    
    print(f"Successfully wrote {len(used_entries)} entries to {bib_file}")
    return True

def main():
    """Main function"""
    # Get the project directory (one level up from scripts)
    project_dir = Path(__file__).parent.parent
    bib_file = project_dir / "references.bib"
    
    print(f"Project directory: {project_dir}")
    print(f"Bibliography file: {bib_file}")
    
    # Check if bib file exists
    if not bib_file.exists():
        print(f"Error: Bibliography file {bib_file} not found!")
        return 1
    
    # Extract citation keys from all .tex files
    used_keys = extract_citation_keys_from_tex_files(str(project_dir))
    
    if not used_keys:
        print("Warning: No citation keys found in .tex files!")
        return 1
    
    print(f"Used citation keys: {sorted(used_keys)}")
    
    # Parse the bibliography file
    all_entries = parse_bib_file(str(bib_file))
    
    if not all_entries:
        print("Error: No entries found in bibliography file!")
        return 1
    
    # Find unused keys
    all_keys = set(all_entries.keys())
    unused_keys = all_keys - used_keys
    missing_keys = used_keys - all_keys
    
    if missing_keys:
        print(f"Warning: The following keys are cited but not found in bibliography:")
        for key in sorted(missing_keys):
            print(f"  - {key}")
    
    if not unused_keys:
        print("No unused citations found. Bibliography is already clean!")
        return 0
    
    # Write the filtered bibliography
    success = write_filtered_bib_file(str(bib_file), used_keys, all_entries)
    
    if success:
        print("\nCitation cleanup completed successfully!")
        print(f"Removed {len(unused_keys)} unused entries")
        print(f"Kept {len(used_keys & all_keys)} used entries")
        return 0
    else:
        print("Error occurred during cleanup!")
        return 1

if __name__ == "__main__":
    exit(main())