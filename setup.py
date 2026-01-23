"""
Custom setup.py for openhcs with automatic ZeroC-Ice installation.

This setup.py extends the default setuptools install command to automatically
download and install zeroc-ice (required for OMERO integration) from
Glencoe Software's repository.

The automatic installation only runs when installing with OMERO extras
(e.g., `pip install openhcs[omero]` or `pip install openhcs[remote]`).

For more information, see:
https://www.glencoesoftware.com/blog/2023/12/08/ice-binaries-for-omero.html
"""

import sys

from setuptools import setup
from setuptools.command.install import install as _install
from setuptools.command.develop import develop as _develop

# Import the shared zeroc_ice installer module
# This module is in openhcs/build_utils/zeroc_ice_installer.py
try:
    from openhcs.build_utils.zeroc_ice_installer import install_zeroc_ice
except ImportError:
    # If openhcs is not installed yet, try importing from build_utils
    import os
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'openhcs'))
    from build_utils.zeroc_ice_installer import install_zeroc_ice


class InstallCommand(_install):
    """Custom install command that installs zeroc-ice for OMERO extras."""

    def run(self):
        # Check if OMERO extras are being installed
        # This is detected by checking command line arguments
        install_with_omero = any(
            'omero' in arg or 'remote' in arg
            for arg in sys.argv
        )

        if install_with_omero:
            print("[openhcs setup] OMERO extras detected. Installing zeroc-ice dependency...")
            install_zeroc_ice(verbose=True)
        else:
            print("[openhcs setup] OMERO extras not requested. Skipping zeroc-ice installation.")

        # Run the standard install
        _install.run(self)


class DevelopCommand(_develop):
    """Custom develop command that installs zeroc-ice for OMERO extras."""

    def run(self):
        # Check if OMERO extras are being installed
        install_with_omero = any(
            'omero' in arg or 'remote' in arg
            for arg in sys.argv
        )

        if install_with_omero:
            print("[openhcs setup] OMERO extras detected. Installing zeroc-ice dependency...")
            install_zeroc_ice(verbose=True)
        else:
            print("[openhcs setup] OMERO extras not requested. Skipping zeroc-ice installation.")

        # Run the standard develop
        _develop.run(self)


if __name__ == "__main__":
    # Read configuration from pyproject.toml
    # This setup.py is mainly for to custom install commands
    setup(
        cmdclass={
            'install': InstallCommand,
            'develop': DevelopCommand,
        },
    )
