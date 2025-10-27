"""
Async initialization for I/O backends.

This module provides background loading of GPU-heavy dependencies
to avoid blocking during import while ensuring they're ready when needed.
"""
import logging
import threading

logger = logging.getLogger(__name__)

_init_complete = threading.Event()
_init_thread = None


def _background_init():
    """
    Background thread target for async initialization.

    NOTE: Due to Python's GIL, importing heavy modules in a background thread
    still blocks the main thread during imports. Therefore, we use lazy initialization
    for GPU libraries and storage backends - they'll be loaded on first use.

    Currently this is a no-op placeholder. GPU registry initialization happens
    lazily on first use, not during startup.
    """
    try:
        logger.info("Background I/O initialization complete (lazy mode - no-op)")
    except Exception as e:
        logger.error(f"Background I/O initialization failed: {e}")
    finally:
        _init_complete.set()


def start_async_initialization():
    """
    Start background initialization of GPU-heavy dependencies.
    
    Call this during application startup (GUI/CLI) to pre-load
    GPU libraries without blocking. Safe to call multiple times.
    """
    global _init_thread
    
    if _init_thread is None:
        _init_thread = threading.Thread(
            target=_background_init,
            daemon=True,
            name="io-async-init"
        )
        _init_thread.start()
        logger.info("Started background I/O initialization")


def wait_for_initialization(timeout: float = 60.0) -> bool:
    """
    Wait for background initialization to complete.
    
    Args:
        timeout: Maximum seconds to wait
        
    Returns:
        True if completed, False if timeout
    """
    return _init_complete.wait(timeout)

