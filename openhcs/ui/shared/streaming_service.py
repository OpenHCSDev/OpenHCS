"""Unified streaming service for viewer communication (Napari/Fiji).

Eliminates duplication between Napari and Fiji streaming code by parametrizing
on viewer_type. All heavy operations run in background threads.
"""

from __future__ import annotations

import logging
import time
from pathlib import Path
from typing import TYPE_CHECKING, Callable, Literal

from objectstate import spawn_thread_with_context

if TYPE_CHECKING:
    from polystore.filemanager import FileManager

logger = logging.getLogger(__name__)

# Chunk size to prevent file descriptor exhaustion
# Each image creates a shared memory segment (file descriptor on Linux)
CHUNK_SIZE = 50

ViewerType = Literal["napari", "fiji"]


class StreamingService:
    """Unified service for streaming images/ROIs to viewers.

    Handles all viewer communication in background threads.
    Uses callbacks for UI thread communication (status updates, errors).
    """

    def __init__(
        self,
        filemanager: FileManager,
        microscope_handler,
        plate_path: Path,
    ):
        self.filemanager = filemanager
        self.microscope_handler = microscope_handler
        self.plate_path = plate_path

    @classmethod
    def supported_viewer_types(cls):
        """Return a list of supported viewer short names (e.g. 'napari', 'fiji').

        Centralized so UI can discover which viewer buttons to create instead
        of hardcoding Napari/Fiji in multiple places.
        """
        # Use the metaclass-driven ZMQ server registry (no fallback).
        # ZMQ_SERVERS is populated by zmqruntime.server via AutoRegisterMeta.
        from zmqruntime.server import ZMQ_SERVERS

        # Trigger discovery (LazyDiscoveryDict) and return stable ordering
        return sorted(list(ZMQ_SERVERS.keys()))

    def _get_backend_enum(self, viewer_type: ViewerType):
        """Get the backend enum for the viewer type."""
        from openhcs.constants.constants import Backend as BackendEnum

        return (
            BackendEnum.NAPARI_STREAM
            if viewer_type == "napari"
            else BackendEnum.FIJI_STREAM
        )

    def _wait_for_viewer_ready(
        self,
        viewer,
        viewer_type: ViewerType,
        num_items: int,
    ) -> None:
        """Wait for viewer to be ready, registering as launching if needed."""
        # Use centralized ViewerStateManager for launching/queued state
        from zmqruntime.viewer_state import ViewerStateManager

        manager = ViewerStateManager.get_instance()

        is_already_running = viewer.wait_for_ready(timeout=0.1)

        # Update queued images for UI display via the manager. The QueueTracker
        # will later update counts precisely as images are sent/acked.
        try:
            manager.update_queued_images(viewer_type, viewer.port, num_items)
        except Exception:
            # If manager doesn't have an entry for this viewer yet, that's fine -
            # get_or_create_viewer should have registered it earlier. We intentionally
            # surface errors elsewhere instead of hiding them here.
            logger.debug(
                "ViewerStateManager: could not update queued images (no viewer registered yet)"
            )

        if not is_already_running:
            logger.info(
                f"Waiting for {viewer_type} viewer on port {viewer.port} to become ready"
            )

            if not viewer.wait_for_ready(timeout=15.0):
                # Clear queued count for UI if startup failed
                try:
                    manager.update_queued_images(viewer_type, viewer.port, 0)
                except Exception:
                    pass
                raise RuntimeError(
                    f"{viewer_type.capitalize()} viewer on port {viewer.port} failed to become ready"
                )

            logger.info(
                f"{viewer_type.capitalize()} viewer on port {viewer.port} is ready"
            )

    def _build_metadata(self, viewer, config, source: str) -> dict:
        """Build metadata dict for streaming."""
        return {
            "port": viewer.port,
            "host": config.host,
            "transport_mode": config.transport_mode,
            "display_config": config,
            "microscope_handler": self.microscope_handler,
            "plate_path": self.plate_path,
            "source": source,
        }

    def stream_images_async(
        self,
        viewer,
        filenames: list[str],
        plate_path: Path,
        read_backend: str,
        config,
        viewer_type: ViewerType,
        status_callback: Callable[[str], None],
        error_callback: Callable[[str], None],
    ) -> None:
        """Load and stream images to viewer in background thread.

        Uses chunked streaming to prevent file descriptor exhaustion.
        """
        backend_enum = self._get_backend_enum(viewer_type)

        def _worker():
            try:
                self._wait_for_viewer_ready(viewer, viewer_type, len(filenames))

                total_images = len(filenames)
                num_chunks = (total_images + CHUNK_SIZE - 1) // CHUNK_SIZE
                logger.info(f"Streaming {total_images} images in {num_chunks} chunks")

                for chunk_idx in range(num_chunks):
                    start_idx = chunk_idx * CHUNK_SIZE
                    end_idx = min(start_idx + CHUNK_SIZE, total_images)
                    chunk_filenames = filenames[start_idx:end_idx]

                    status_callback(
                        f"Loading chunk {chunk_idx + 1}/{num_chunks} ({len(chunk_filenames)} images)..."
                    )

                    # Load chunk
                    image_data_list = []
                    file_paths = []
                    for filename in chunk_filenames:
                        image_path = plate_path / filename
                        image_data = self.filemanager.load(
                            str(image_path), read_backend
                        )
                        image_data_list.append(image_data)
                        file_paths.append(filename)

                    logger.info(
                        f"Loaded chunk {chunk_idx + 1}/{num_chunks}: {len(image_data_list)} images"
                    )

                    source = (
                        Path(file_paths[0]).parent.name
                        if file_paths
                        else "unknown_source"
                    )
                    metadata = self._build_metadata(viewer, config, source)

                    self.filemanager.save_batch(
                        image_data_list, file_paths, backend_enum.value, **metadata
                    )
                    logger.info(
                        f"Streamed chunk {chunk_idx + 1}/{num_chunks} to {viewer_type}"
                    )

                    if chunk_idx < num_chunks - 1:
                        time.sleep(0.1)

                logger.info(
                    f"Successfully streamed {total_images} images to {viewer_type}"
                )
                status_callback(
                    f"Streamed {total_images} images to {viewer_type.capitalize()}"
                )

            except Exception as e:
                logger.error(f"Failed to stream images to {viewer_type}: {e}")
                status_callback(f"Error: {e}")
                error_callback(str(e))

        spawn_thread_with_context(_worker, name=f"stream_images_{viewer_type}")
        logger.info(f"Started streaming {len(filenames)} images to {viewer_type}")

    def stream_rois_async(
        self,
        viewer,
        roi_filenames: list[str],
        plate_path: Path,
        config,
        viewer_type: ViewerType,
        status_callback: Callable[[str], None],
        error_callback: Callable[[str], None],
    ) -> None:
        """Load and stream ROI files to viewer in background thread."""
        backend_enum = self._get_backend_enum(viewer_type)

        def _worker():
            try:
                from polystore.roi import load_rois_from_zip

                total = len(roi_filenames)
                if total == 0:
                    return

                status_callback(f"Loading {total} ROI file(s) from disk...")

                data_list: list = []
                paths: list[str] = []

                for i, filename in enumerate(roi_filenames, 1):
                    file_path = plate_path / filename
                    rois = load_rois_from_zip(file_path)
                    if not rois:
                        logger.warning(f"No ROIs found in {file_path.name}")
                        continue

                    data_list.append(rois)
                    paths.append(filename)

                    if i % 5 == 0 or i == total:
                        status_callback(f"Loading ROIs: {i}/{total} file(s)...")

                if not data_list:
                    msg = "No ROIs loaded from any selected files."
                    logger.warning(msg)
                    status_callback(msg)
                    return

                self._wait_for_viewer_ready(viewer, viewer_type, len(paths))

                source = Path(paths[0]).parent.name if paths else "unknown_source"
                metadata = self._build_metadata(viewer, config, source)

                status_callback(
                    f"Streaming {len(paths)} ROI file(s) to {viewer_type.capitalize()}..."
                )

                self.filemanager.save_batch(
                    data_list, paths, backend_enum.value, **metadata
                )

                msg = f"Streamed {len(paths)} ROI file(s) to {viewer_type.capitalize()} on port {viewer.port}"
                logger.info(msg)
                status_callback(msg)

            except Exception as e:
                logger.error(f"Failed to stream ROIs to {viewer_type}: {e}")
                status_callback(f"Error: {e}")
                error_callback(str(e))

        spawn_thread_with_context(_worker, name=f"stream_rois_{viewer_type}")
