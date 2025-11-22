"""
Centralized cache toggles used across the UI/live-context pipeline.

ENABLE_TIME_BASED_CACHES controls whether token/time-based caches
are respected. Disable for debugging correctness (forces fresh
placeholder resolution, live-context collection, and unsaved checks).
"""

ENABLE_TIME_BASED_CACHES: bool = True


def set_time_based_caches_enabled(enabled: bool) -> None:
    """Set global flag for token/time-based caches."""
    global ENABLE_TIME_BASED_CACHES
    ENABLE_TIME_BASED_CACHES = bool(enabled)


def time_based_caches_enabled() -> bool:
    """Return whether token/time-based caches are enabled."""
    return ENABLE_TIME_BASED_CACHES
