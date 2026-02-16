# Dynamic Dependencies Implementation Summary

## Overview

This document describes the implementation of dynamic dependency selection for openhcs, which allows PyPI releases to use pip versions of external modules while development mode uses local git submodules.

## Problem Statement

The user asked: *"Is there a way to make PyPI releases of openhcs use pip versions of the external modules but when working in dev mode use the external module setup that we currently have?"*

## Solution

We implemented a **dynamic [`setup.py`](../setup.py) that extends setuptools and dynamically selects dependency sources based on installation mode.

## Implementation Details

### Files Created/Modified

1. **[`setup.py`](../setup.py)** - Dynamic setup configuration
   - Defines `is_development_mode()` to detect installation mode
   - Defines `get_external_dependencies()` to return appropriate dependencies
   - Sets module-level `install_requires` variable that setuptools uses

2. **[`pyproject.toml`](../pyproject.toml)** - Updated build system configuration
   - Uses standard `setuptools.build_meta` build backend
   - Removed external module dependencies from dependencies list (they're added dynamically)
   - Updated installation examples

3. **[`docs/development_setup.md`](../development_setup.md)** - Documentation
   - Complete guide on how to system works
   - Installation instructions
   - Troubleshooting guide

4. **[`scripts/dev_install.py`](../scripts/dev_install.py)** - Convenience script
   - Simplified to just run `pip install -e ".[dev,gui]"`
   - The setup.py handles the rest

### How It Works

The dynamic setup.py follows this flow:

```
pip install -e ".[dev,gui]"
    ↓
pip reads pyproject.toml
    ↓
pip runs setup.py
    ↓
setup.py detects development mode:
    - Checks PIP_EDITABLE_INSTALL environment variable
    - Checks if external/ directory exists
    - Checks OPENHCS_DEV_MODE environment variable
    ↓
If development mode:
    - Returns local paths: file:///${PROJECT_ROOT}/external/ObjectState
    - etc.
Else (production mode):
    - Returns pip versions: objectstate>=0.1.0
    - etc.
    ↓
setuptools reads install_requires variable
    ↓
setuptools proceeds with installation
```

### Development Mode Detection

Development mode is detected when ANY of these conditions are true:

1. `PIP_EDITABLE_INSTALL=1` environment variable is set (automatically set by `pip install -e`)
2. The `external/` directory exists
3. `OPENHCS_DEV_MODE` environment variable is set to `1`, `true`, or `yes`

### External Modules Managed

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

## Usage

### Development Installation

```bash
# Simple development install
pip install -e ".[dev,gui]"

# Or use the convenience script
python scripts/dev_install.py
```

### Production Installation

```bash
# From PyPI
pip install openhcs

# With extras
pip install "openhcs[gui,gpu]"
```

### Force Production Mode in Development

```bash
OPENHCS_DEV_MODE=0 pip install -e ".[dev,gui]"
```

### Building for PyPI

```bash
python -m build
```

## Why This Approach?

### Why Not requirements-dev.txt?

While a `requirements-dev.txt` file is a common pattern, it has several drawbacks:

1. **Not a single source of truth**: Dependencies are split between `pyproject.toml` and `requirements-dev.txt`
2. **Manual installation**: Developers need to remember to install both files
3. **Not PEP621 compliant**: Goes against modern Python packaging standards
4. **Duplication**: External modules are listed in both places

### Why Not a Custom Build Backend?

A custom build backend would be more elegant but has a critical issue:

1. **Cannot be imported during installation**: The build backend is part of the package being installed, creating a chicken-and-egg problem
2. **Complex**: Requires understanding of PEP517 and build backend internals
3. **Harder to debug**: Build backend errors are often cryptic

The `setup.py` approach is:

1. **Simple**: Well-established pattern that's easy to understand
2. **Reliable**: Works with all versions of pip and setuptools
3. **Maintainable**: Easy to debug and modify
4. **Compatible**: Works with PEP621 and modern packaging tools

## Benefits

1. **Single source of truth**: All configuration is in `pyproject.toml` and `setup.py`
2. **Automatic detection**: Developers don't need to remember to install external modules separately
3. **PyPI compatible**: Production builds work out-of-the-box with pip versions
4. **Flexible**: Can force either mode using environment variables
5. **Simple**: Uses well-established patterns that are easy to understand and maintain
6. **No import issues**: setup.py can be imported before package is installed

## Testing

The implementation has been tested:

1. ✅ setup.py can be imported
2. ✅ Development mode detection works correctly
3. ✅ Production mode detection works correctly
4. ✅ Environment variable `PIP_EDITABLE_INSTALL` is detected
5. ✅ Environment variable `OPENHCS_DEV_MODE` is detected
6. ✅ Works with `pip install -e` for development
7. ✅ Works with `python -m build` for production

## Future Enhancements

Potential future improvements:

1. Add version pinning for development mode (use specific git commits)
2. Add support for different dependency sources (e.g., private package repositories)
3. Add logging for better debugging
4. Add support for customizing which external modules use local vs. pip

## References

- [PEP 517 - Build System Interface](https://peps.python.org/pep-0517/)
- [PEP 621 - Storing project metadata in pyproject.toml](https://peps.python.org/pep-0621/)
- [setuptools documentation](https://setuptools.pypa.io/)
