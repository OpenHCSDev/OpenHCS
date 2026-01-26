# Dynamic Dependencies Implementation Summary

## Overview

This document describes the implementation of dynamic dependency selection for openhcs, which allows PyPI releases to use pip versions of external modules while development mode uses local git submodules.

## Problem Statement

The user asked: *"Is there a way to make PyPI releases of openhcs use the pip versions of the external modules but when working in dev mode use the external module setup that we currently have?"*

## Solution

We implemented a **custom build backend** ([`openhcs_build/__init__.py`](../openhcs_build/__init__.py)) that extends `setuptools.build_meta` and dynamically selects dependency sources based on the installation mode.

## Implementation Details

### Files Created/Modified

1. **[`openhcs_build/__init__.py`](../openhcs_build/__init__.py)** - Custom build backend
   - Extends `setuptools.build_meta`
   - Overrides `get_requires_for_build_wheel()` and `get_requires_for_build_editable()`
   - Detects development mode and returns appropriate dependencies

2. **[`pyproject.toml`](../pyproject.toml)** - Updated build system configuration
   - Changed `build-backend` from `setuptools.build_meta` to `openhcs_build`
   - Added `tomli>=1.2.0` to build-system requirements
   - Removed external module dependencies from dependencies list (they're added dynamically)
   - Updated installation examples

3. **[`docs/development_setup.md`](../development_setup.md)** - Documentation
   - Complete guide on how the system works
   - Installation instructions
   - Troubleshooting guide

4. **[`scripts/dev_install.py`](../scripts/dev_install.py)** - Convenience script
   - Simplified to just run `pip install -e ".[dev,gui]"`
   - The custom build backend handles the rest

### How It Works

The custom build backend follows this flow:

```
pip install -e ".[dev,gui]"
    ↓
pip reads pyproject.toml
    ↓
pip loads openhcs_build build backend
    ↓
openhcs_build.get_requires_for_build_editable() is called
    ↓
openhcs_build detects development mode:
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
pip installs the dependencies
    ↓
setuptools builds the package
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

### Why Not setup.py?

A `setup.py` file with dynamic dependencies is a common pattern, but:

1. **Not PEP621 compliant**: When using `pyproject.toml` with PEP621, `setup.py` dependencies are ignored
2. **Conflicts**: Can cause warnings about dependencies being overwritten
3. **Deprecated pattern**: Modern Python packaging prefers PEP621

### Why Custom Build Backend?

A custom build backend provides the best of both worlds:

1. **PEP621 compliant**: Uses modern Python packaging standards
2. **Dynamic dependencies**: Can modify dependencies at build time
3. **Clean separation**: Build logic is separate from project configuration
4. **Maintainable**: Clear, well-structured code
5. **Extensible**: Easy to add more complex logic in the future
6. **No requirements.txt**: Avoids the "smell" of having a separate requirements file

## Benefits

1. **Single source of truth**: All configuration is in `pyproject.toml`
2. **Automatic detection**: Developers don't need to remember to install external modules separately
3. **PyPI compatible**: Production builds work out-of-the-box with pip versions
4. **Flexible**: Can force either mode using environment variables
5. **Modern packaging**: Uses PEP621 and custom build backends
6. **Maintainable**: Clear, well-structured code that's easy to understand

## Testing

The implementation has been tested:

1. ✅ Custom build backend can be imported
2. ✅ Development mode detection works correctly
3. ✅ Production mode detection works correctly
4. ✅ Environment variable `PIP_EDITABLE_INSTALL` is detected
5. ✅ Environment variable `OPENHCS_DEV_MODE` is detected

## Future Enhancements

Potential future improvements:

1. Add version pinning for development mode (use specific git commits)
2. Add support for different dependency sources (e.g., private package repositories)
3. Add logging for better debugging
4. Add support for customizing which external modules use local vs. pip

## References

- [PEP 517 - Build System Interface](https://peps.python.org/pep-0517/)
- [PEP 621 - Storing project metadata in pyproject.toml](https://peps.python.org/pep-0621/)
- [setuptools.build_meta documentation](https://setuptools.pypa.io/en/latest/build_meta.html)
