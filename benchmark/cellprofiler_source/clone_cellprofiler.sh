#!/bin/bash
# Clone CellProfiler source code for LLM-powered converter reference
# This script downloads all modules and library functions from CellProfiler GitHub
# Run from: benchmark/cellprofiler_source/

set -e

REPO_BASE="https://raw.githubusercontent.com/CellProfiler/CellProfiler/main"
API_BASE="https://api.github.com/repos/CellProfiler/CellProfiler/contents"

# Directories to clone
declare -A DIRS=(
    ["modules"]="src/frontend/cellprofiler/modules"
    ["library/functions"]="src/subpackages/library/cellprofiler_library/functions"
    ["library/modules"]="src/subpackages/library/cellprofiler_library/modules"
    ["library/opts"]="src/subpackages/library/cellprofiler_library/opts"
)

echo "=== CellProfiler Source Cloner ==="
echo "Cloning from: $REPO_BASE"
echo ""

for local_dir in "${!DIRS[@]}"; do
    remote_path="${DIRS[$local_dir]}"
    
    echo "=== Cloning $local_dir from $remote_path ==="
    
    # Create local directory
    mkdir -p "$local_dir"
    
    # Get file list from GitHub API
    file_list=$(curl -sL "$API_BASE/$remote_path" | \
        grep '"name":' | grep '\.py"' | \
        sed 's/.*"name": "\([^"]*\)".*/\1/')
    
    file_count=$(echo "$file_list" | wc -l)
    echo "Found $file_count Python files"
    
    # Download files in parallel
    echo "$file_list" | xargs -I{} -P 10 sh -c \
        "curl -sL -o '$local_dir/{}' '$REPO_BASE/$remote_path/{}' && echo '  Downloaded: {}'"
    
    echo ""
done

echo "=== Clone Complete ==="
echo ""
echo "Summary:"
echo "  Modules: $(ls modules/*.py 2>/dev/null | wc -l) files"
echo "  Library functions: $(ls library/functions/*.py 2>/dev/null | wc -l) files"
echo "  Library modules: $(ls library/modules/*.py 2>/dev/null | wc -l) files"
echo "  Library opts: $(ls library/opts/*.py 2>/dev/null | wc -l) files"
echo ""
echo "Total lines of code:"
find . -name "*.py" -exec cat {} \; | wc -l

