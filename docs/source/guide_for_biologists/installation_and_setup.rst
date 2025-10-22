Installation & Setup
====================

This guide will walk you through installing OpenHCS on your computer and launching the application for the first time.

.. contents::
   :local:
   :depth: 2

----------------------------

System Requirements
-------------------

**Operating Systems:**
- Linux 
- Windows 10/11 (via WSL2 - Windows Subsystem for Linux)
- macOS 

**Minimum Requirements:**
- Python 3.11 or newer


----------------------------
Installation Instructions
------------------------

Install OpenHCS with required GUI dependencies:

.. code-block:: bash

   pip install openhcs[gui]

This will install openhcs along with all optional dependencies for full functionality. 

If you want a minimal installation, you can choose to do a CPU-only install: (for CI/testing environments)
.. code-block:: bash

   # Install with minimal dependencies
    pip install openhcs --no-deps
    pip install numpy scipy scikit-image pandas

    # Enable CPU-only mode
    export OPENHCS_CPU_ONLY=1

The installation may take several minutes as it downloads and installs all dependencies.

----------------------------

Launching OpenHCS
-----------------

Once installed, you can launch the OpenHCS graphical interface with a command:

.. code-block:: bash

   openhcs
   #or
   python -m openhcs.pyqt_gui

----------------------------

First Launch
------------

When you first launch OpenHCS, you'll see:

1. **Main Window:** The central control panel
2. **Plate Manager:** For organizing your microscopy experiments
3. **Pipeline Editor:** For creating and editing image processing pipelines

You're now ready to start using OpenHCS! Proceed to the next section to learn about the basic interface.

----------------------------

Updating OpenHCS
---------------

To update to the latest version of OpenHCS:

.. code-block:: bash

   pip install --upgrade openhcs[all]

It's recommended to check for updates periodically to get the latest features and bug fixes.