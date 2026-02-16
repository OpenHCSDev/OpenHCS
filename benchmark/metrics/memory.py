"""Peak memory usage metric."""

import threading
import time

import psutil

from benchmark.contracts.metric import MetricCollector


class MemoryMetric(MetricCollector):
    """Samples RSS memory in a background thread and reports peak MB."""

    name = "peak_memory_mb"

    def __init__(self, interval_seconds: float = 0.1):
        self.interval = interval_seconds
        self._running = False
        self._peak_rss = 0
        self._thread: threading.Thread | None = None
        self._process = psutil.Process()
        self._started = False

    def __enter__(self) -> "MemoryMetric":
        self._peak_rss = 0
        self._running = True
        self._started = True
        self._thread = threading.Thread(target=self._sample_loop, daemon=True)
        self._thread.start()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb) -> None:
        self._running = False
        if self._thread is not None:
            self._thread.join(timeout=1.0)

    def _sample_loop(self) -> None:
        while self._running:
            try:
                rss = self._process.memory_info().rss
                if rss > self._peak_rss:
                    self._peak_rss = rss
            except Exception:
                # If the process disappears or psutil errors, just stop sampling.
                break
            time.sleep(self.interval)

    def get_result(self) -> float:
        if not self._started:
            raise RuntimeError("MemoryMetric not used as context manager")
        if self._peak_rss == 0:
            raise RuntimeError("MemoryMetric recorded no samples")
        return self._peak_rss / (1024 * 1024)
