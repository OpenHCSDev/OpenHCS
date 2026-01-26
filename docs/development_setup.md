# Development Setup

This document explains how to set up development and production environments for openhcs.

## Overview

The openhcs project uses **pip versions of external modules** for PyPI releases. For development, you can install local external modules from git submodules separately.

## Installation

### Production Installation (PyPI Releases)

To install openhcs from PyPI:

```bash
pip install openhcs
```

Or to install with extras:

```bash
pip install "openhcs[gui,gpu]"
```

This will install pip versions of all external modules:
- zmqruntime>=0.1.0
- pycodify>=0.1.0
- objectstate>=0.1.0
- python-introspect>=0.1.0
- metaclass-registry>=0.1.0
- arraybridge>=0.1.0
- polystore>=0.1.0
- pyqt-reactive>=0.1.0

### Development Installation

To install openhcs in development mode with local external modules:

```bash
# Install openhcs with dev extras
pip install -e ".[dev,gui]"

# Install local external modules as editable installs
pip install -e external/ObjectState
pip install -e external/python-introspect
pip install -e external/metaclass-registry
pip install -e external/arraybridge
pip install -e external/PolyStore
pip install -e external/pyqt-reactive
pip install -e external/zmqruntime
pip install -e external/pycodify
```

Or use the convenience script:

```bash
python scripts/dev_install.py
```

## External Modules

The following external modules are available:

| Module | PyPI Version | Dev Path |
|--------|--------------|----------|
| zmqruntime | zmqruntime>=0.1.0 | external/zmqruntime |
| pycodify | pycodify>=0.1.0 | external/pycodify |
| objectstate | objectstate>=0.1.0 | external/ObjectState |
| python-introspect | python-introspect>=0.1.0 | external/python-introspect |
| metaclass-registry | metaclass-registry>=0.1.0 | external/metaclass-registry |
| arraybridge | arraybridge>=0.1.0 | external/arraybridge |
| polystore | polystore>=0.1.0 | external/PolyStore |
| pyqt-reactive | pyqt-reactive>=0.1.0 | external/pyqt-reactive |

## Git Submodules

The external modules are git submodules. To initialize them:

```bash
git submodule update --init --recursive
```

To update them to the latest versions:

```bash
git submodule update --remote
```

## Building for PyPI

To build openhcs for PyPI:

```bash
python -m build
```

The build will create a wheel that uses pip versions of external modules.

## Troubleshooting

### External modules not found in development

If you see errors about missing external modules during development:

1. Ensure git submodules are initialized:
   ```bash
   git submodule update --init --recursive
   ```

2. Verify that `external/` directory exists and contains submodules:
   ```bash
   ls -la external/
   ```

### Why not use dynamic dependency selection?

You might wonder why we don't use dynamic dependency selection (e.g., custom build backend or setup.py). The reasons are:

1. **Reliability**: Dynamic approaches can have import issues and conflicts with setuptools
2. **Simplicity**: Using standard pip versions is more predictable and easier to debug
3. **CI/CD friendly**: Works out-of-the-box with standard PyPI installation
4. **No build artifacts**: Avoids issues with multiple `.egg-info` directories

## Architecture

The installation flow:

**Production (PyPI):**
```
pip install openhcs
    ↓
pip reads pyproject.toml
    ↓
pip installs pip versions of external modules
    ↓
Installation complete
```

**Development:**
```
pip install -e ".[dev,gui]"
    ↓
pip reads pyproject.toml
    ↓
pip installs openhcs (without external modules)
    ↓
Developer installs local external modules separately
    ↓
Installation complete
```
