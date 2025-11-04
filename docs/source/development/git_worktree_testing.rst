Git Worktree Testing
====================

This guide explains how to run tests from a different Git worktree than the main branch, which is useful for testing feature branches while keeping your main branch clean.

What are Git Worktrees?
-----------------------

Git worktrees allow you to have multiple working directories for the same repository. This is particularly useful when:

- You want to test a feature branch without switching away from your current work
- You need to compare behavior between branches
- You want to run tests on a feature branch while continuing development on main

Setting Up a Worktree
---------------------

**1. Create a worktree for your feature branch:**

.. code-block:: bash

   # From your main repository directory
   git worktree add ../openhcs-feature feature/my-feature-branch

This creates a new directory ``../openhcs-feature`` with the ``feature/my-feature-branch`` checked out.

**2. Verify the worktree:**

.. code-block:: bash

   git worktree list

You should see both your main directory and the new worktree listed.

Running Tests from a Worktree
------------------------------

**Option 1: Run tests directly in the worktree**

.. code-block:: bash

   # Navigate to the worktree
   cd ../openhcs-feature
   
   # Activate the virtual environment (if using one)
   source .venv/bin/activate
   
   # Run tests
   OPENHCS_CPU_ONLY=true python -m pytest tests/

**Option 2: Run tests from main directory pointing to worktree**

You can run tests from your main directory but execute them against the worktree code:

.. code-block:: bash

   # From your main repository directory
   cd ../openhcs-feature && source .venv/bin/activate && \
   OPENHCS_CPU_ONLY=true python -m pytest tests/ && cd -

**Option 3: Use a shared virtual environment**

If you want to share the virtual environment between worktrees:

.. code-block:: bash

   # Create a shared venv outside both worktrees
   python -m venv ../openhcs-shared-venv
   
   # In each worktree, activate the shared venv
   source ../openhcs-shared-venv/bin/activate
   
   # Install the package in editable mode
   pip install -e .
   
   # Run tests
   OPENHCS_CPU_ONLY=true python -m pytest tests/

.. warning::
   When using a shared virtual environment, be aware that installing the package in editable mode (``pip install -e .``) will point to whichever worktree you last installed from. This can cause confusion if you're switching between worktrees.

Running Integration Tests
--------------------------

For integration tests with specific configurations:

.. code-block:: bash

   # Navigate to the worktree
   cd ../openhcs-feature
   
   # Activate virtual environment
   source .venv/bin/activate
   
   # Run integration tests with specific parameters
   OPENHCS_CPU_ONLY=true python -m pytest tests/integration/test_main.py \
       --it-backends disk \
       --it-microscopes ImageXpress \
       --it-dims 3d \
       --it-exec-mode multiprocessing \
       --it-zmq-mode direct \
       --it-visualizers none \
       -xvs

Comparing Test Results Between Branches
----------------------------------------

To compare test results between main and a feature branch:

**1. Run tests on main branch:**

.. code-block:: bash

   # In main repository
   cd /path/to/openhcs-main
   source .venv/bin/activate
   OPENHCS_CPU_ONLY=true python -m pytest tests/ -v > test_results_main.txt 2>&1

**2. Run tests on feature branch:**

.. code-block:: bash

   # In worktree
   cd /path/to/openhcs-feature
   source .venv/bin/activate
   OPENHCS_CPU_ONLY=true python -m pytest tests/ -v > test_results_feature.txt 2>&1

**3. Compare results:**

.. code-block:: bash

   diff test_results_main.txt test_results_feature.txt

Measuring Performance Differences
----------------------------------

To compare memory usage or execution time between branches:

.. code-block:: bash

   # Run with time measurement on main
   cd /path/to/openhcs-main
   /usr/bin/time -v bash -c "source .venv/bin/activate && \
       OPENHCS_CPU_ONLY=true python -m pytest tests/integration/test_main.py \
       --it-backends disk --it-microscopes ImageXpress -xvs" \
       2>&1 | grep -E "(Maximum resident set size|Elapsed)"
   
   # Run with time measurement on feature branch
   cd /path/to/openhcs-feature
   /usr/bin/time -v bash -c "source .venv/bin/activate && \
       OPENHCS_CPU_ONLY=true python -m pytest tests/integration/test_main.py \
       --it-backends disk --it-microscopes ImageXpress -xvs" \
       2>&1 | grep -E "(Maximum resident set size|Elapsed)"

This will show:
- ``Maximum resident set size``: Peak memory usage in kilobytes
- ``Elapsed (wall clock) time``: Total execution time

Cleaning Up Worktrees
----------------------

When you're done with a worktree:

**1. Remove the worktree:**

.. code-block:: bash

   # From main repository
   git worktree remove ../openhcs-feature

**2. If the worktree directory was deleted manually:**

.. code-block:: bash

   # Prune stale worktree references
   git worktree prune

**3. List all worktrees to verify:**

.. code-block:: bash

   git worktree list

Best Practices
--------------

1. **Separate Virtual Environments**: Create a separate virtual environment for each worktree to avoid dependency conflicts.

2. **Naming Convention**: Use descriptive names for worktrees that match the branch name:
   
   .. code-block:: bash
   
      git worktree add ../openhcs-sequential feature/sequential-component-processing

3. **Test Data**: Test data is typically shared between worktrees since it's in the same repository. Be aware that changes to test data in one worktree affect all worktrees.

4. **Clean State**: Always ensure your worktree is in a clean state before running tests:
   
   .. code-block:: bash
   
      cd ../openhcs-feature
      git status  # Check for uncommitted changes
      git pull    # Update to latest commits

5. **Resource Cleanup**: After running tests, especially integration tests, ensure all resources are cleaned up:
   
   .. code-block:: bash
   
      # Kill any lingering processes
      pkill -f "openhcs"
      
      # Clean up temporary files
      rm -rf /tmp/openhcs_*

Common Issues
-------------

**Issue: Import errors when running tests**

This usually means the package isn't installed in the virtual environment:

.. code-block:: bash

   cd ../openhcs-feature
   source .venv/bin/activate
   pip install -e .

**Issue: Tests using old code**

If you're using a shared virtual environment, reinstall the package:

.. code-block:: bash

   pip install -e . --force-reinstall --no-deps

**Issue: Worktree shows as locked**

If a worktree operation was interrupted:

.. code-block:: bash

   # Remove the lock file
   rm .git/worktrees/<worktree-name>/locked
   
   # Or use git worktree unlock
   git worktree unlock <path-to-worktree>

Example Workflow
----------------

Here's a complete example workflow for testing a feature branch:

.. code-block:: bash

   # 1. Create worktree for feature branch
   cd /path/to/openhcs-main
   git worktree add ../openhcs-sequential feature/sequential-component-processing
   
   # 2. Set up virtual environment in worktree
   cd ../openhcs-sequential
   python -m venv .venv
   source .venv/bin/activate
   
   # 3. Install dependencies
   pip install -e .
   pip install pytest
   
   # 4. Run tests
   OPENHCS_CPU_ONLY=true python -m pytest tests/integration/test_main.py \
       --it-backends disk \
       --it-microscopes ImageXpress \
       --it-dims 3d \
       --it-exec-mode multiprocessing \
       --it-zmq-mode direct \
       --it-visualizers none \
       --it-sequential valid_1_component \
       -xvs
   
   # 5. Compare with main branch
   cd /path/to/openhcs-main
   source .venv/bin/activate
   OPENHCS_CPU_ONLY=true python -m pytest tests/integration/test_main.py \
       --it-backends disk \
       --it-microscopes ImageXpress \
       --it-dims 3d \
       --it-exec-mode multiprocessing \
       --it-zmq-mode direct \
       --it-visualizers none \
       --it-sequential none \
       -xvs
   
   # 6. When done, clean up
   cd /path/to/openhcs-main
   git worktree remove ../openhcs-sequential

See Also
--------

- :doc:`pipeline_debugging_guide` - Debugging pipeline execution
- :doc:`omero_testing` - Testing with OMERO integration
- :doc:`../user_guide/cpu_only_mode` - CPU-only testing mode

