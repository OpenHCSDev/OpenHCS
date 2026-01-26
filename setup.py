"""
Dynamic setup.py for openhcs.

This setup.py allows for different dependency sources:
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
from setuptools import setup

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
    project_root = Path(__file__).parent
    external_dir = project_root / "external"
    has_external = external_dir.exists()

    # Check for explicit dev mode flag
    dev_mode_env = os.environ.get("OPENHCS_DEV_MODE", "").lower() in ("1", "true", "yes")

    result = is_editable and has_external or dev_mode_env
    if result:
        print("openhcs: Installing in DEVELOPMENT mode (using local external modules)")
    else:
        print("openhcs: Installing in PRODUCTION mode (using PyPI versions)")
    return result


def get_external_dependencies():
    """
    Get external dependencies based on install mode.

    Returns:
        list: List of dependency specifications
    """
    if is_development_mode():
        return LOCAL_EXTERNAL_DEPENDENCIES
    else:
        return PYPI_DEPENDENCIES


# Call setup with dynamic dependencies
# This will merge with dependencies from pyproject.toml
setup(
    install_requires=get_external_dependencies(),
)
