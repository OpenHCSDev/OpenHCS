"""
Lazy GPU import system.

Defers GPU library imports until first use to eliminate startup delay.
Supports fast installation checking without imports.
"""

import importlib
import importlib.util
import logging
import threading
from typing import Any, Dict, Optional, Tuple, Callable

logger = logging.getLogger(__name__)


# GPU check functions - explicit, fail-loud implementations
def _check_cuda_available(lib) -> bool:
    """Check CUDA availability (torch/cupy pattern)."""
    return lib.cuda.is_available()


def _check_jax_gpu(lib) -> bool:
    """Check JAX GPU availability.

    Uses lazy detection: only checks if JAX is installed, defers actual
    jax.devices() call to avoid thread explosion during startup.
    Returns True if JAX is installed (actual GPU check happens at runtime).
    """
    # JAX is installed - assume GPU availability will be checked at runtime
    # This avoids calling jax.devices() which creates 54+ threads
    return True


def _check_tf_gpu(lib) -> bool:
    """Check TensorFlow GPU availability."""
    gpus = lib.config.list_physical_devices('GPU')
    return len(gpus) > 0


# GPU library registry
# Format: (module_name, submodule, gpu_check_func, get_device_id_func)
GPU_LIBRARY_REGISTRY: Dict[str, Tuple[str, Optional[str], Optional[Callable], Optional[Callable]]] = {
    'torch': ('torch', None, _check_cuda_available, lambda lib: lib.cuda.current_device()),
    'cupy': ('cupy', None, _check_cuda_available, lambda lib: lib.cuda.get_device_id()),
    'jax': ('jax', None, _check_jax_gpu, lambda lib: 0),
    'tensorflow': ('tensorflow', None, _check_tf_gpu, lambda lib: 0),
    'jnp': ('jax', 'numpy', None, None),
    'pyclesperanto': ('pyclesperanto', None, None, None),
}


class _LazyGPUModule:
    """Lazy proxy for GPU libraries - imports on first attribute access."""
    
    def __init__(self, name: str):
        self._name = name
        module_name, submodule, _, _ = GPU_LIBRARY_REGISTRY[name]
        self._module_name = module_name
        self._submodule = submodule
        self._module = None
        self._lock = threading.Lock()
        self._imported = False
        
        # Fast installation check (no import)
        self._installed = importlib.util.find_spec(module_name) is not None
    
    def is_installed(self) -> bool:
        """Check if installed without importing."""
        return self._installed
    
    def _ensure_imported(self) -> Any:
        """
        Import module if needed (thread-safe).
        
        FAIL LOUD: No try-except. Let import errors propagate.
        """
        if not self._imported:
            with self._lock:
                if not self._imported:
                    if not self._installed:
                        # Not installed - return None (expected case)
                        self._imported = True
                        return None
                    
                    # Import the module - FAIL LOUD if import fails
                    self._module = importlib.import_module(self._module_name)
                    logger.debug(f"Lazy-imported {self._module_name}")
                    
                    # Navigate to submodule if specified
                    if self._submodule:
                        for attr in self._submodule.split('.'):
                            self._module = getattr(self._module, attr)
                            # FAIL LOUD: getattr raises AttributeError if missing
                    
                    self._imported = True
        
        return self._module
    
    def __getattr__(self, name: str) -> Any:
        """
        Lazy import on attribute access.
        
        FAIL LOUD: Raises ImportError if not installed, AttributeError if attribute missing.
        """
        module = self._ensure_imported()
        if module is None:
            raise ImportError(
                f"Module '{self._module_name}' is not installed. "
                f"Install it to use {self._name}.{name}"
            )
        # FAIL LOUD: getattr raises AttributeError if name doesn't exist
        return getattr(module, name)
    
    def __bool__(self) -> bool:
        """
        Allow truthiness checks.
        
        Returns False if not installed, True if installed and imports successfully.
        FAIL LOUD: Propagates import errors.
        """
        module = self._ensure_imported()
        return module is not None


# Auto-generate lazy proxies from registry
for _name in GPU_LIBRARY_REGISTRY.keys():
    globals()[_name] = _LazyGPUModule(_name)

# Alias tf -> tensorflow for compatibility
tf = globals()['tensorflow']


def check_installed_gpu_libraries() -> Dict[str, bool]:
    """
    Check which GPU libraries are installed without importing them.
    
    Fast (~0.001s per library). No imports, just filesystem checks.
    """
    return {
        name: importlib.util.find_spec(module_name) is not None
        for name, (module_name, _, _, _) in GPU_LIBRARY_REGISTRY.items()
    }


def check_gpu_capability(library_name: str) -> Optional[int]:
    """
    Check GPU capability for a library (lazy import).
    
    FAIL LOUD: Propagates import errors and attribute errors.
    Only returns None if library not installed or has no GPU.
    
    Args:
        library_name: Name from GPU_LIBRARY_REGISTRY
    
    Returns:
        Device ID if GPU available, None otherwise
    """
    if library_name not in GPU_LIBRARY_REGISTRY:
        raise ValueError(f"Unknown GPU library: {library_name}")
    
    _, _, gpu_check, get_device_id = GPU_LIBRARY_REGISTRY[library_name]
    
    # No GPU check defined for this library
    if gpu_check is None:
        return None
    
    # Get lazy module (imports if needed) - FAIL LOUD
    lib = globals()[library_name]
    
    # Not installed (expected case)
    if not lib:
        return None
    
    # Check GPU availability - FAIL LOUD if check function fails
    if gpu_check(lib):
        return get_device_id(lib)
    
    return None

