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

### Step 1: Install Python

OpenHCS requires Python 3.11 or newer.

**Linux:**

Most modern Linux distributions come with Python 3. Check your version:

.. code-block:: bash

   python3 --version

If you need to install or update Python:

.. code-block:: bash

   # Ubuntu/Debian
   sudo apt update
   sudo apt install python3.11 python3.11-venv python3-pip

   # Fedora
   sudo dnf install python3.11

**Windows (WSL2):**

1. Install WSL2 following Microsoft's official guide: https://docs.microsoft.com/en-us/windows/wsl/install
2. Install Ubuntu from the Microsoft Store
3. Open Ubuntu and run:

.. code-block:: bash

   sudo apt update
   sudo apt install python3.11 python3.11-venv python3-pip

**macOS:**

Install Python using Homebrew:

.. code-block:: bash

   # Install Homebrew if you don't have it
   /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"

   # Install Python
   brew install python@3.11

### Step 2: Create a Virtual Environment (Recommended)

It's best practice to install OpenHCS in a virtual environment to avoid conflicts with other Python packages.

.. code-block:: bash

   # Create a new directory for your OpenHCS work
   mkdir openhcs_workspace
   cd openhcs_workspace

   # Create a virtual environment
   python3.11 -m venv openhcs_env

   # Activate the virtual environment
   # On Linux/macOS/WSL:
   source openhcs_env/bin/activate

   # On Windows (if not using WSL):
   openhcs_env\Scripts\activate

Your terminal prompt should now show ``(openhcs_env)`` indicating the environment is active.

### Step 3: Install OpenHCS

Install OpenHCS with all required dependencies:

.. code-block:: bash

   pip install openhcs[all]

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