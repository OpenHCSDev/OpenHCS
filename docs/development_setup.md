# Development Setup

This document explains how to set up development and production environments for openhcs.

## Overview

The openhcs project uses a **custom build backend** ([`openhcs_build/`](../openhcs_build/__init__.py)) that automatically detects whether you're installing for development or production, and selects appropriate dependency sources:

- **Development mode**: Uses local external modules from [`external/`](../external/) directory (git submodules)
- **Production/PyPI mode**: Uses pip versions of external modules from PyPI

This approach avoids the need for a separate `requirements-dev.txt` file and keeps all configuration in [`pyproject.toml`](../pyproject.toml).

## How It Works

The custom build backend ([`openhcs_build/__init__.py`](../openhcs_build/__init__.py)) extends `setuptools.build_meta` and:

1. **Detects development mode** by checking:
   - Whether `PIP_EDITABLE_INSTALL=1` environment variable is set (set by `pip install -e`)
   - Whether the `external/` directory exists
   - Whether `OPENHCS_DEV_MODE` environment variable is set to `1`, `true`, or `yes`

2. **Modifies dependencies dynamically** in the `get_requires_for_build_*` functions:
   - In development mode: Adds local paths like `file:///${PROJECT_ROOT}/external/ObjectState`
   - In production mode: Adds pip versions like `objectstate>=0.1.0`

## Installation

### Development Installation

To install openhcs in development mode with local external modules:

```bash
# Simple development install
pip install -e ".[dev,gui]"

# Or use the convenience script
python scripts/dev_install.py
```

The custom build backend will automatically detect development mode and use the local external modules from the `external/` directory.

### Production Installation

To install openhcs from PyPI:

```bash
pip install openhcs
```

Or to install with extras:

```bash
pip install "openhcs[gui,gpu]"
```

### Force Production Mode in Development

If you want to test production mode while still doing an editable install:

```bash
OPENHCS_DEV_MODE=0 pip install -e ".[dev,gui]"
```

## External Modules

The following external modules are managed by the custom build backend:

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

To build openhcs for PyPI (which will use pip versions of external modules):

```bash
python -m build
```

The build process will automatically use production mode dependencies.

## Troubleshooting

### External modules not found in development

If you see errors about missing external modules during development:

1. Ensure git submodules are initialized:
   ```bash
   git submodule update --init --recursive
   ```

2. Verify the `external/` directory exists and contains submodules:
   ```bash
   ls -la external/
   ```

### Wrong dependency source being used

If the wrong dependency source is being used:

1. Check if you're using the `-e` flag for editable install
2. Verify the `external/` directory exists
3. Set `OPENHCS_DEV_MODE=1` to force development mode or `OPENHCS_DEV_MODE=0` to force production mode

### Build fails with "Module not found: openhcs_build"

This can happen if the `openhcs_build/` directory is not in the Python path. Ensure:

1. You're running commands from the project root
2. The `openhcs_build/` directory exists in the project root
3. The build system requirements are installed:
   ```bash
   pip install setuptools>=61.0 wheel tomli>=1.2.0
   ```

### Why not use requirements-dev.txt?

You might wonder why we don't use a `requirements-dev.txt` file. The reasons are:

1. **Single source of truth**: All configuration is in `pyproject.toml`
2. **Automatic detection**: Developers don't need to remember to install external modules separately
3. **PyPI compatible**: Production builds work out-of-the-box with pip versions
4. **Modern packaging**: Uses PEP621 with pyproject.toml for most configuration
5. **Flexible**: Can force either mode using environment variables

### Why use a custom build backend?

A custom build backend provides several advantages:

1. **Clean separation**: Build logic is separate from project configuration
2. **PEP621 compliant**: Uses modern Python packaging standards
3. **Dynamic dependencies**: Can modify dependencies at build time
4. **Maintainable**: Clear, well-structured code that's easy to understand
5. **Extensible**: Easy to add more complex logic in the future

## Architecture

The custom build backend follows this flow:

```
pip install -e .
    ↓
pip reads pyproject.toml
    ↓
pip loads openhcs_build build backend
    ↓
openhcs_build.get_requires_for_build_editable() is called
    ↓
openhcs_build detects development mode
    ↓
openhcs_build returns modified dependencies
    ↓
pip installs the dependencies
    ↓
setuptools builds the package
```

## Benefits

This approach provides several benefits:

1. **Single source of truth**: All configuration is in `pyproject.toml`
2. **No requirements.txt**: Avoids the "smell" of having a separate requirements file
3. **Automatic detection**: Developers don't need to remember to install external modules separately
4. **PyPI compatible**: Production builds work out-of-the-box with pip versions
5. **Flexible**: Can force either mode using environment variables
6. **Modern packaging**: Uses PEP621 and custom build backends
7. **Maintainable**: Clear, well-structured code that's easy to understand
