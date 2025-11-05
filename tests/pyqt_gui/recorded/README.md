# Recorded GUI Tests

This directory contains auto-generated tests from GUI interaction recordings.

## Recording a Test

```bash
python -m openhcs.pyqt_gui.launch --record-test my_workflow_name
```

Interact with the GUI normally, then close the application. A test file will be generated here.

## Running Tests

```bash
# Run all recorded tests
pytest tests/pyqt_gui/recorded/ -v

# Run specific test
pytest tests/pyqt_gui/recorded/test_my_workflow_name.py -v
```

## Timing Configuration for Slower Machines

If tests fail due to timing issues on slower machines, increase the delays:

```bash
# For slow CI runners or VMs
export OPENHCS_TEST_ACTION_DELAY=3.0
export OPENHCS_TEST_WINDOW_DELAY=3.0
export OPENHCS_TEST_SAVE_DELAY=3.0

pytest tests/pyqt_gui/recorded/ -v
```

For faster machines:

```bash
# For fast local testing
export OPENHCS_TEST_ACTION_DELAY=0.5
export OPENHCS_TEST_WINDOW_DELAY=0.5
export OPENHCS_TEST_SAVE_DELAY=0.5

pytest tests/pyqt_gui/recorded/ -v
```

## How It Works

Generated tests use `_wait_for_gui(TIMING.ACTION_DELAY)` instead of fixed delays. The `TimingConfig.from_environment()` reads environment variables, so the same test code works on all machines by adjusting timing through env vars.

## Documentation

See the full documentation at: `docs/source/development/gui_test_recording.rst`

