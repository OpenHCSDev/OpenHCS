#!/bin/bash
# Script to create GitHub repositories and extract code from OpenHCS

set -e  # Exit on error

echo "========================================="
echo "Package Extraction Script"
echo "========================================="
echo ""

# Step 1: Create GitHub repositories
echo "Step 1: Creating GitHub repositories..."
echo ""

echo "Creating metaclass-registry repository..."
gh repo create trissim/metaclass-registry --public \
  --description "Zero-boilerplate metaclass-driven plugin registry system with lazy discovery and caching" \
  --homepage "https://metaclass-registry.readthedocs.io" || echo "Repository may already exist"

echo "Creating arraybridge repository..."
gh repo create trissim/arraybridge --public \
  --description "Unified API for NumPy, CuPy, PyTorch, TensorFlow, JAX, and pyclesperanto with automatic memory type conversion" \
  --homepage "https://arraybridge.readthedocs.io" || echo "Repository may already exist"

echo "Creating lazy-config repository..."
gh repo create trissim/lazy-config --public \
  --description "Generic lazy dataclass configuration framework with dual-axis inheritance and contextvars-based resolution" \
  --homepage "https://lazy-config.readthedocs.io" || echo "Repository may already exist"

echo ""
echo "Step 2: Adding remotes and pushing initial code..."
echo ""

# Step 2a: Push metaclass-registry
echo "Pushing metaclass-registry..."
cd /home/ts/code/projects/metaclass-registry
git remote add origin https://github.com/trissim/metaclass-registry.git 2>/dev/null || echo "Remote already exists"
git branch -M main
git push -u origin main --force

# Step 2b: Push arraybridge
echo "Pushing arraybridge..."
cd /home/ts/code/projects/arraybridge
git remote add origin https://github.com/trissim/arraybridge.git 2>/dev/null || echo "Remote already exists"
git branch -M main
git push -u origin main --force

# Step 2c: Push lazy-config
echo "Pushing lazy-config..."
cd /home/ts/code/projects/lazy-config-framework
git remote add origin https://github.com/trissim/lazy-config.git 2>/dev/null || echo "Remote already exists"
git branch -M main
git push -u origin main --force

echo ""
echo "========================================="
echo "✅ All repositories created and pushed!"
echo "========================================="
echo ""
echo "Next steps:"
echo "1. Extract code from OpenHCS to all 3 packages"
echo "2. Write tests for all packages"
echo "3. Create documentation"
echo "4. Publish to PyPI"
echo ""
echo "Repository URLs:"
echo "- https://github.com/trissim/metaclass-registry"
echo "- https://github.com/trissim/arraybridge"
echo "- https://github.com/trissim/lazy-config"

