"""
Unit tests for Windows path escaping in detached process spawning.

Tests that Windows paths with backslashes are properly escaped when generating
Python code strings for subprocess execution.
"""

import pytest
from unittest.mock import patch, MagicMock


def test_napari_windows_path_escaping():
    """Test that napari detached process handles Windows paths correctly."""
    # Import the module
    from openhcs.runtime import napari_stream_visualizer
    from openhcs.core.config import TransportMode

    # Mock os.getcwd to return a Windows-style path
    windows_path = r"C:\Users\labuser\Documents\openhcs"

    with patch("os.getcwd", return_value=windows_path):
        with patch("os.makedirs"):
            with patch(
                "os.path.expanduser",
                return_value="C:\\Users\\labuser\\.local\\share\\openhcs\\logs",
            ):
                with patch("subprocess.Popen") as mock_popen:
                    with patch("builtins.open", MagicMock()):
                        # Call the function
                        napari_stream_visualizer._spawn_detached_napari_process(
                            port=7777,
                            viewer_title="Test Viewer",
                            replace_layers=False,
                            transport_mode=TransportMode.TCP,
                        )

                        # Get the python code that was passed to subprocess
                        call_args = mock_popen.call_args
                        python_code = call_args[0][0][
                            2
                        ]  # [sys.executable, "-c", python_code]

                        # Verify the path is properly escaped using repr()
                        # repr() produces a string like 'C:\\Users\\labuser\\Documents\\openhcs'
                        # with properly escaped backslashes
                        expected_repr = repr(windows_path)
                        assert (
                            expected_repr in python_code
                        ), f"Windows path not properly escaped. Expected {expected_repr} in generated code:\n{python_code}"

                        # Verify the code is syntactically valid Python
                        try:
                            compile(python_code, "<string>", "exec")
                        except SyntaxError as e:
                            pytest.fail(
                                f"Generated Python code has syntax error: {e}\n\nCode:\n{python_code}"
                            )


def test_fiji_windows_path_escaping():
    """Test that fiji detached process handles Windows paths correctly."""
    # Import the module
    from openhcs.runtime import fiji_stream_visualizer
    from openhcs.core.config import TransportMode

    # Mock os.getcwd to return a Windows-style path
    windows_path = r"C:\Users\labuser\Documents\openhcs"

    with patch("os.getcwd", return_value=windows_path):
        with patch("os.makedirs"):
            with patch(
                "os.path.expanduser",
                return_value="C:\\Users\\labuser\\.local\\share\\openhcs\\logs",
            ):
                with patch("subprocess.Popen") as mock_popen:
                    with patch("builtins.open", MagicMock()):
                        # Call the function
                        fiji_stream_visualizer._spawn_detached_fiji_process(
                            port=7778,
                            viewer_title="Test Fiji Viewer",
                            display_config=None,
                            transport_mode=TransportMode.TCP,
                        )

                        # Get the python code that was passed to subprocess
                        call_args = mock_popen.call_args
                        python_code = call_args[0][0][
                            2
                        ]  # [sys.executable, "-c", python_code]

                        # Verify the path is properly escaped using repr()
                        # repr() produces a string like 'C:\\Users\\labuser\\Documents\\openhcs'
                        # with properly escaped backslashes
                        expected_repr = repr(windows_path)
                        assert (
                            expected_repr in python_code
                        ), f"Windows path not properly escaped. Expected {expected_repr} in generated code:\n{python_code}"

                        # Verify the code is syntactically valid Python
                        try:
                            compile(python_code, "<string>", "exec")
                        except SyntaxError as e:
                            pytest.fail(
                                f"Generated Python code has syntax error: {e}\n\nCode:\n{python_code}"
                            )


def test_napari_unix_path_still_works():
    """Test that napari detached process still handles Unix paths correctly."""
    from openhcs.runtime import napari_stream_visualizer
    from openhcs.core.config import TransportMode

    # Mock os.getcwd to return a Unix-style path
    unix_path = "/home/user/openhcs"

    with patch("os.getcwd", return_value=unix_path):
        with patch("os.makedirs"):
            with patch(
                "os.path.expanduser",
                return_value="/home/user/.local/share/openhcs/logs",
            ):
                with patch("subprocess.Popen") as mock_popen:
                    with patch("builtins.open", MagicMock()):
                        # Call the function
                        napari_stream_visualizer._spawn_detached_napari_process(
                            port=7777,
                            viewer_title="Test Viewer",
                            replace_layers=False,
                            transport_mode=TransportMode.IPC,
                        )

                        # Get the python code that was passed to subprocess
                        call_args = mock_popen.call_args
                        python_code = call_args[0][0][2]

                        # Verify the code is syntactically valid Python
                        try:
                            compile(python_code, "<string>", "exec")
                        except SyntaxError as e:
                            pytest.fail(
                                f"Generated Python code has syntax error: {e}\n\nCode:\n{python_code}"
                            )


def test_fiji_unix_path_still_works():
    """Test that fiji detached process still handles Unix paths correctly."""
    from openhcs.runtime import fiji_stream_visualizer
    from openhcs.core.config import TransportMode

    # Mock os.getcwd to return a Unix-style path
    unix_path = "/home/user/openhcs"

    with patch("os.getcwd", return_value=unix_path):
        with patch("os.makedirs"):
            with patch(
                "os.path.expanduser",
                return_value="/home/user/.local/share/openhcs/logs",
            ):
                with patch("subprocess.Popen") as mock_popen:
                    with patch("builtins.open", MagicMock()):
                        # Call the function
                        fiji_stream_visualizer._spawn_detached_fiji_process(
                            port=7778,
                            viewer_title="Test Fiji Viewer",
                            display_config=None,
                            transport_mode=TransportMode.IPC,
                        )

                        # Get the python code that was passed to subprocess
                        call_args = mock_popen.call_args
                        python_code = call_args[0][0][2]

                        # Verify the code is syntactically valid Python
                        try:
                            compile(python_code, "<string>", "exec")
                        except SyntaxError as e:
                            pytest.fail(
                                f"Generated Python code has syntax error: {e}\n\nCode:\n{python_code}"
                            )
