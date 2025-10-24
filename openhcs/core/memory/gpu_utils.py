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


def check_cupy_gpu_available() -> Optional[int]:
    """Check cupy GPU availability (lazy import)."""
    if os.getenv('OPENHCS_SUBPROCESS_NO_GPU') == '1':
        return None
    return check_gpu_capability('cupy')


def check_torch_gpu_available() -> Optional[int]:
    """Check torch GPU availability (lazy import)."""
    if os.getenv('OPENHCS_SUBPROCESS_NO_GPU') == '1':
        return None
    return check_gpu_capability('torch')


def check_tf_gpu_available() -> Optional[int]:
    """Check tensorflow GPU availability (lazy import)."""
    if os.getenv('OPENHCS_SUBPROCESS_NO_GPU') == '1':
        return None
    return check_gpu_capability('tf')


def check_jax_gpu_available() -> Optional[int]:
    """Check JAX GPU availability (lazy import)."""
    if os.getenv('OPENHCS_SUBPROCESS_NO_GPU') == '1':
        return None
    return check_gpu_capability('jax')
