"""
Build hook for automatic ZeroC-Ice installation during openhcs[omero] installation.

This hook is automatically executed during the build process when installing
openhcs with OMERO dependencies. It uses the shared zeroc-ice installer
module from openhcs.build_utils.zeroc_ice_installer to download and
install the appropriate zeroc-ice wheel from Glencoe Software's repository.

For more information, see:
https://www.glencoesoftware.com/blog/2023/12/08/ice-binaries-for-omero.html
"""

import sys
import os

# Import the shared zeroc-ice installer module
# This module is in openhcs/build_utils/zeroc_ice_installer.py
try:
    from openhcs.build_utils.zeroc_ice_installer import install_zeroc_ice
except ImportError:
    # If openhcs is not installed yet, try importing from build_utils
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
    from openhcs.build_utils.zeroc_ice_installer import install_zeroc_ice


def build_editable(config_settings=None):
    """
    Build hook called during editable install.

    This function is automatically called by pip when installing
    openhcs in editable mode. It attempts to install zeroc-ice
    if not already present.
    """
    # Call the shared installation function
    install_zeroc_ice(verbose=True)


# This is the entry point that setuptools will call
__all__ = ["build_editable"]
