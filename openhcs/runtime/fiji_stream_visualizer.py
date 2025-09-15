"""
Fiji stream visualizer for OpenHCS.

Manages Fiji/ImageJ instances for real-time visualization of pipeline data.
Provides automatic Fiji process management and macro execution.
"""

import logging
import multiprocessing
import threading
import time
from typing import Optional
from pathlib import Path

from openhcs.io.filemanager import FileManager

logger = logging.getLogger(__name__)

# Global process management for Fiji viewer
_global_fiji_process: Optional[multiprocessing.Process] = None
_global_fiji_lock = threading.Lock()


def _cleanup_global_fiji_viewer() -> None:
    """
    Clean up global Fiji viewer process for test mode.
    
    This forcibly terminates the Fiji viewer process to allow pytest to exit.
    Should only be called in test mode.
    """
    global _global_fiji_process
    
    with _global_fiji_lock:
        if _global_fiji_process and _global_fiji_process.is_alive():
            logger.info("🔬 FIJI VISUALIZER: Terminating Fiji viewer for test cleanup")
            _global_fiji_process.terminate()
            _global_fiji_process.join(timeout=3)
            
            if _global_fiji_process.is_alive():
                logger.warning("🔬 FIJI VISUALIZER: Force killing Fiji viewer process")
                _global_fiji_process.kill()
                _global_fiji_process.join(timeout=1)
            
            _global_fiji_process = None


def _fiji_viewer_process(temp_dir: str, viewer_title: str = "OpenHCS Fiji Visualization", fiji_executable_path: Optional[Path] = None) -> None:
    """
    Fiji viewer process function.
    
    This runs in a separate process to manage Fiji instance and handle
    incoming image data for visualization.
    
    Args:
        temp_dir: Temporary directory for image files
        viewer_title: Title for the Fiji window
    """
    try:
        import subprocess
        import time
        from pathlib import Path
        
        print(f"🔬 FIJI PROCESS: Starting Fiji viewer with title '{viewer_title}'")
        print(f"🔬 FIJI PROCESS: Monitoring directory: {temp_dir}")
        
        # Try to find and start Fiji
        fiji_path = _find_fiji_executable(fiji_executable_path)
        if not fiji_path:
            print("🔬 FIJI PROCESS: Fiji executable not found - monitoring directory only")
            _monitor_directory_only(temp_dir)
            return
        
        # Start Fiji GUI for interactive exploration (no macro needed)
        print(f"🔬 FIJI PROCESS: Starting Fiji GUI for interactive image exploration")
        print(f"🔬 FIJI PROCESS: Images will be streamed directly to Fiji for viewing and editing")

        # Start Fiji GUI without any macro - just open for interactive use
        fiji_process = subprocess.Popen([
            str(fiji_path)
        ], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        
        print(f"🔬 FIJI PROCESS: Started Fiji GUI process (PID: {fiji_process.pid})")
        print(f"🔬 FIJI PROCESS: Fiji is ready for interactive image exploration")

        # Wait for Fiji process to complete (user closes Fiji)
        fiji_process.wait()
        
    except Exception as e:
        print(f"🔬 FIJI PROCESS: Error: {e}")
    finally:
        print("🔬 FIJI PROCESS: Fiji GUI closed")


def _find_fiji_executable(config_path: Optional[Path] = None) -> Optional[Path]:
    """Find Fiji executable on the system."""
    # If explicit path provided in config, use it
    if config_path is not None:
        if config_path.exists():
            return config_path
        else:
            print(f"🔬 FIJI PROCESS: Configured path {config_path} does not exist")
            return None

    # Try to find fiji in PATH first
    import shutil
    fiji_in_path = shutil.which("fiji")
    if fiji_in_path:
        return Path(fiji_in_path)

    # Fall back to common installation paths
    common_paths = [
        Path("/Applications/Fiji.app/Contents/MacOS/ImageJ-macosx"),  # macOS
        Path("C:/Fiji.app/ImageJ-win64.exe"),  # Windows
        Path("/opt/fiji/ImageJ-linux64"),  # Linux
        Path.home() / "Fiji.app" / "ImageJ-linux64",  # User installation
    ]

    for path in common_paths:
        if path.exists():
            return path

    return None


def _monitor_directory_only(temp_dir: str) -> None:
    """Monitor directory for new files when Fiji is not available."""
    print("🔬 FIJI PROCESS: Fiji not available - monitoring directory for files")
    
    temp_dir_path = Path(temp_dir)
    temp_dir_path.mkdir(exist_ok=True)
    
    seen_files = set()
    
    while True:
        try:
            current_files = set(temp_dir_path.glob("*.tif*"))
            new_files = current_files - seen_files
            
            for file_path in new_files:
                print(f"🔬 FIJI PROCESS: New image detected: {file_path.name}")
                seen_files.add(file_path)
            
            time.sleep(1)  # Check every second
            
        except KeyboardInterrupt:
            break
        except Exception as e:
            print(f"🔬 FIJI PROCESS: Monitor error: {e}")
            time.sleep(5)


class FijiStreamVisualizer:
    """
    Manages a Fiji viewer instance for real-time visualization of images
    streamed from the OpenHCS pipeline. Runs Fiji in a separate process
    for independence and persistence across pipeline runs.
    """

    def __init__(self, filemanager: FileManager, viewer_title: str = "OpenHCS Fiji Visualization", persistent: bool = True, visualizer_config):
        self.filemanager = filemanager
        self.viewer_title = viewer_title
        self.persistent = persistent
        self.visualizer_config = visualizer_config
        self.temp_dir: Optional[str] = None
        self.process: Optional[multiprocessing.Process] = None
        self.is_running = False
        self._lock = threading.Lock()

    def start_viewer(self) -> None:
        """Start the Fiji viewer process."""
        global _global_fiji_process
        
        with self._lock:
            # Check if we can reuse existing global viewer process
            with _global_fiji_lock:
                if (_global_fiji_process is not None and
                    _global_fiji_process.is_alive()):
                    logger.info("🔬 FIJI VISUALIZER: Reusing existing Fiji viewer process")
                    self.process = _global_fiji_process
                    self.is_running = True
                    return

            if self.is_running:
                logger.warning("Fiji viewer is already running.")
                return

            # Create temporary directory for image files
            import tempfile
            if self.visualizer_config.temp_directory:
                self.temp_dir = str(self.visualizer_config.temp_directory / "openhcs_fiji")
                Path(self.temp_dir).mkdir(parents=True, exist_ok=True)
            else:
                self.temp_dir = tempfile.mkdtemp(prefix="openhcs_fiji_")

            logger.info(f"🔬 FIJI VISUALIZER: Starting Fiji viewer process")
            logger.info(f"🔬 FIJI VISUALIZER: Temp directory: {self.temp_dir}")

            # Get Fiji executable path from config
            fiji_executable_path = self.visualizer_config.fiji_executable_path

            self.process = multiprocessing.Process(
                target=_fiji_viewer_process,
                args=(self.temp_dir, self.viewer_title, fiji_executable_path),
                daemon=False  # Don't make it daemon so it can outlive parent
            )
            self.process.start()

            # Update global references
            with _global_fiji_lock:
                _global_fiji_process = self.process

            self.is_running = True
            logger.info(f"🔬 FIJI VISUALIZER: Fiji viewer started (PID: {self.process.pid})")

    def stop_viewer(self) -> None:
        """Stop the Fiji viewer process."""
        global _global_fiji_process
        
        with self._lock:
            if not self.is_running or self.process is None:
                logger.warning("Fiji viewer is not running.")
                return

            if not self.persistent:
                logger.info("🔬 FIJI VISUALIZER: Stopping Fiji viewer process")
                self.process.terminate()
                self.process.join(timeout=5)
                
                if self.process.is_alive():
                    logger.warning("🔬 FIJI VISUALIZER: Force killing Fiji viewer")
                    self.process.kill()
                    self.process.join(timeout=2)

                # Clear global reference if we stopped it
                with _global_fiji_lock:
                    if _global_fiji_process == self.process:
                        _global_fiji_process = None

            # Clean up temp directory
            if self.temp_dir:
                try:
                    import shutil
                    shutil.rmtree(self.temp_dir)
                    logger.debug(f"🔬 FIJI VISUALIZER: Cleaned up temp directory: {self.temp_dir}")
                except Exception as e:
                    logger.warning(f"🔬 FIJI VISUALIZER: Failed to cleanup temp directory: {e}")

            self.process = None
            self.temp_dir = None
            self.is_running = False

    def get_temp_directory(self) -> Optional[str]:
        """Get the temporary directory path for Fiji image files."""
        return self.temp_dir

    def is_viewer_running(self) -> bool:
        """Check if the Fiji viewer process is running."""
        if not self.is_running or self.process is None:
            return False
        return self.process.is_alive()
