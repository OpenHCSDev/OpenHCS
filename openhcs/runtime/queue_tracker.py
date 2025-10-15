"""Queue tracker for monitoring image processing progress in viewers.

Tracks sent images by ID and decrements count when acknowledgments are received.
Used to show real-time progress like '3/10 images processed' in the UI.
"""

import logging
import threading
import time
from typing import Dict, Tuple, Optional, Set

logger = logging.getLogger(__name__)


class QueueTracker:
    """Tracks pending images for a single viewer.
    
    Thread-safe tracker that maintains:
    - Set of sent image IDs (pending processing)
    - Set of processed image IDs (received acks)
    - Timestamps for timeout detection
    """
    
    def __init__(self, viewer_port: int, viewer_type: str, timeout_seconds: float = 30.0):
        """Initialize queue tracker.
        
        Args:
            viewer_port: Port of the viewer being tracked
            viewer_type: 'napari' or 'fiji'
            timeout_seconds: How long to wait for ack before marking as stuck
        """
        self.viewer_port = viewer_port
        self.viewer_type = viewer_type
        self.timeout_seconds = timeout_seconds
        
        self._lock = threading.Lock()
        self._pending: Dict[str, float] = {}  # {image_id: timestamp_sent}
        self._processed: Set[str] = set()     # {image_id}
        self._total_sent = 0
        self._total_processed = 0
    
    def register_sent(self, image_id: str):
        """Register that an image was sent to the viewer.
        
        Args:
            image_id: UUID of the sent image
        """
        with self._lock:
            self._pending[image_id] = time.time()
            self._total_sent += 1
            logger.debug(f"[{self.viewer_type}:{self.viewer_port}] Registered sent image {image_id} (pending: {len(self._pending)})")
    
    def mark_processed(self, image_id: str):
        """Mark an image as processed (ack received).

        Args:
            image_id: UUID of the processed image
        """
        with self._lock:
            if image_id in self._pending:
                elapsed = time.time() - self._pending[image_id]
                del self._pending[image_id]
                self._processed.add(image_id)
                self._total_processed += 1
                logger.debug(f"[{self.viewer_type}:{self.viewer_port}] Marked processed {image_id} (took {elapsed:.2f}s, pending: {len(self._pending)})")

                # Auto-clear when all images are processed
                if len(self._pending) == 0 and self._total_sent > 0:
                    logger.info(f"[{self.viewer_type}:{self.viewer_port}] All {self._total_sent} images processed - auto-clearing tracker")
                    self._processed.clear()
                    self._total_sent = 0
                    self._total_processed = 0
            else:
                logger.warning(f"[{self.viewer_type}:{self.viewer_port}] Received ack for unknown image {image_id}")
    
    def get_progress(self) -> Tuple[int, int]:
        """Get current progress.
        
        Returns:
            (processed_count, total_sent_count)
        """
        with self._lock:
            return (self._total_processed, self._total_sent)
    
    def get_pending_count(self) -> int:
        """Get number of pending images (sent but not acked).
        
        Returns:
            Number of pending images
        """
        with self._lock:
            return len(self._pending)
    
    def has_stuck_images(self) -> bool:
        """Check if any images have been pending longer than timeout.
        
        Returns:
            True if any images are stuck (no ack within timeout)
        """
        with self._lock:
            now = time.time()
            for image_id, sent_time in self._pending.items():
                if now - sent_time > self.timeout_seconds:
                    return True
            return False
    
    def get_stuck_images(self) -> list:
        """Get list of stuck image IDs (pending longer than timeout).
        
        Returns:
            List of (image_id, elapsed_seconds) tuples
        """
        with self._lock:
            now = time.time()
            stuck = []
            for image_id, sent_time in self._pending.items():
                elapsed = now - sent_time
                if elapsed > self.timeout_seconds:
                    stuck.append((image_id, elapsed))
            return stuck
    
    def clear(self):
        """Clear all tracking data (e.g., when viewer is closed)."""
        with self._lock:
            self._pending.clear()
            self._processed.clear()
            self._total_sent = 0
            self._total_processed = 0
            logger.debug(f"[{self.viewer_type}:{self.viewer_port}] Cleared queue tracker")
    
    def __repr__(self):
        with self._lock:
            return f"QueueTracker({self.viewer_type}:{self.viewer_port}, processed={self._total_processed}/{self._total_sent}, pending={len(self._pending)})"


class GlobalQueueTrackerRegistry:
    """Global registry of queue trackers for all viewers.
    
    Singleton that maintains queue trackers for each active viewer.
    Used by the ack listener to route acks to the correct tracker.
    """
    
    _instance = None
    _lock = threading.Lock()
    
    def __new__(cls):
        if cls._instance is None:
            with cls._lock:
                if cls._instance is None:
                    cls._instance = super().__new__(cls)
                    cls._instance._initialized = False
        return cls._instance
    
    def __init__(self):
        if self._initialized:
            return
        self._initialized = True
        self._trackers: Dict[int, QueueTracker] = {}  # {viewer_port: QueueTracker}
        self._registry_lock = threading.Lock()
        logger.info("Initialized GlobalQueueTrackerRegistry")
    
    def get_or_create_tracker(self, viewer_port: int, viewer_type: str) -> QueueTracker:
        """Get existing tracker or create new one for a viewer.
        
        Args:
            viewer_port: Port of the viewer
            viewer_type: 'napari' or 'fiji'
            
        Returns:
            QueueTracker for this viewer
        """
        with self._registry_lock:
            if viewer_port not in self._trackers:
                self._trackers[viewer_port] = QueueTracker(viewer_port, viewer_type)
                logger.info(f"Created queue tracker for {viewer_type} viewer on port {viewer_port}")
            return self._trackers[viewer_port]
    
    def get_tracker(self, viewer_port: int) -> Optional[QueueTracker]:
        """Get tracker for a viewer port.
        
        Args:
            viewer_port: Port of the viewer
            
        Returns:
            QueueTracker if exists, None otherwise
        """
        with self._registry_lock:
            return self._trackers.get(viewer_port)
    
    def remove_tracker(self, viewer_port: int):
        """Remove tracker for a viewer (e.g., when viewer is closed).
        
        Args:
            viewer_port: Port of the viewer
        """
        with self._registry_lock:
            if viewer_port in self._trackers:
                del self._trackers[viewer_port]
                logger.info(f"Removed queue tracker for viewer on port {viewer_port}")
    
    def get_all_trackers(self) -> Dict[int, QueueTracker]:
        """Get all active trackers.
        
        Returns:
            Dict of {viewer_port: QueueTracker}
        """
        with self._registry_lock:
            return dict(self._trackers)
    
    def clear_all(self):
        """Clear all trackers (e.g., on shutdown)."""
        with self._registry_lock:
            self._trackers.clear()
            logger.info("Cleared all queue trackers")

