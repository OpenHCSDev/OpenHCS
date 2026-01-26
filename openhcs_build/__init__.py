"""
Custom build backend for openhcs.

This build backend allows for different dependency sources:
- PyPI releases: Use pip versions from PyPI
- Development mode: Use local external modules from external/ directory

Usage:
    # Production/PyPI build (uses pip versions)
    pip install .
    python -m build

    # Development install (uses local external modules)
    pip install -e .
"""

import os
from pathlib import Path
from setuptools.build_meta import (
    build_editable,
    build_wheel,
    get_requires_for_build_editable,
    get_requires_for_build_wheel,
    prepare_metadata_for_build_editable,
    prepare_metadata_for_build_wheel,
)

# External module versions for PyPI releases
PYPI_DEPENDENCIES = [
    "zmqruntime>=0.1.0",
    "pycodify>=0.1.0",
    "objectstate>=0.1.0",
    "python-introspect>=0.1.0",
    "metaclass-registry>=0.1.0",
    "arraybridge>=0.1.0",
    "polystore>=0.1.0",
    "pyqt-reactive>=0.1.0",
]

# Local external modules for development
LOCAL_EXTERNAL_DEPENDENCIES = [
    "ObjectState @ file:///${PROJECT_ROOT}/external/ObjectState",
    "python-introspect @ file:///${PROJECT_ROOT}/external/python-introspect",
    "metaclass-registry @ file:///${PROJECT_ROOT}/external/metaclass-registry",
    "arraybridge @ file:///${PROJECT_ROOT}/external/arraybridge",
    "polystore @ file:///${PROJECT_ROOT}/external/PolyStore",
    "pyqt-reactive @ file:///${PROJECT_ROOT}/external/pyqt-reactive",
    "zmqruntime @ file:///${PROJECT_ROOT}/external/zmqruntime",
    "pycodify @ file:///${PROJECT_ROOT}/external/pycodify",
]


def is_development_mode():
    """
    Determine if we're in development mode.

    Development mode is detected when:
    1. We're doing an editable install
    2. The external/ directory exists with git submodules
    3. OPENHCS_DEV_MODE environment variable is set
    """
    # Check for editable install (pip passes this via environment)
    is_editable = os.environ.get("PIP_EDITABLE_INSTALL") == "1"

    # Check for external directory
    project_root = Path(__file__).parent.parent
    external_dir = project_root / "external"
    has_external = external_dir.exists()

    # Check for explicit dev mode flag
    dev_mode_env = os.environ.get("OPENHCS_DEV_MODE", "").lower() in ("1", "true", "yes")

    return is_editable and has_external or dev_mode_env


def get_requires_for_build_wheel(config_settings=None):
    """Get requirements for building wheel."""
    # Get the original requirements
    requires = []

    # Read pyproject.toml to get base dependencies
    pyproject_path = Path(__file__).parent.parent / "pyproject.toml"
    try:
        import tomli
        with open(pyproject_path, "rb") as f:
            pyproject = tomli.load(f)
        base_deps = pyproject.get("project", {}).get("dependencies", [])

        # Filter out external dependencies (they start with the package names we're replacing)
        external_names = {
            "zmqruntime", "pycodify", "objectstate", "python-introspect",
            "metaclass-registry", "arraybridge", "polystore", "pyqt-reactive"
        }

        filtered_deps = [
            dep for dep in base_deps
            if not any(
                dep.startswith(f"{name} ") or dep.startswith(f"{name}=") or dep.startswith(f"{name}@")
                for name in external_names
            )
        ]

        requires.extend(filtered_deps)
    except Exception:
        pass

    # Add external dependencies based on mode
    if is_development_mode():
        print("openhcs: Building in DEVELOPMENT mode (using local external modules)")
        requires.extend(LOCAL_EXTERNAL_DEPENDENCIES)
    else:
        print("openhcs: Building in PRODUCTION mode (using PyPI versions)")
        requires.extend(PYPI_DEPENDENCIES)

    return requires


def get_requires_for_build_editable(config_settings=None):
    """Get requirements for building editable wheel."""
    # Same logic as regular wheel
    return get_requires_for_build_wheel(config_settings)


# Export all required build backend functions
__all__ = [
    "build_editable",
    "build_wheel",
    "get_requires_for_build_editable",
    "get_requires_for_build_wheel",
    "prepare_metadata_for_build_editable",
    "prepare_metadata_for_build_wheel",
]
