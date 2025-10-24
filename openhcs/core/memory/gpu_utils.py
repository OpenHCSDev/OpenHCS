"""
GPU utility functions for OpenHCS.

This module provides utility functions for checking GPU availability
across different frameworks (cupy, torch, tensorflow, jax).

Doctrinal Clauses:
- Clause 88 — No Inferred Capabilities
- Clause 293 — GPU Pre-Declaration Enforcement
"""

import logging
import os
from typing import Optional

from openhcs.core.lazy_gpu_imports import check_gpu_capability

logger = logging.getLogger(__name__)


def check_library_gpu_available(library_name: str) -> Optional[int]:
    """
    Check GPU availability for a specific library (lazy import).

    Args:
        library_name: Library name ('cupy', 'torch', 'tf'/'tensorflow', 'jax')

    Returns:
        Device ID if GPU available, None otherwise
    """
    if os.getenv('OPENHCS_SUBPROCESS_NO_GPU') == '1':
        return None
    return check_gpu_capability(library_name)


# Backwards compatibility aliases
check_cupy_gpu_available = lambda: check_library_gpu_available('cupy')
check_torch_gpu_available = lambda: check_library_gpu_available('torch')
check_tf_gpu_available = lambda: check_library_gpu_available('tf')
check_jax_gpu_available = lambda: check_library_gpu_available('jax')
