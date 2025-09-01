"""
OpenHCS native function registry.

This registry processes OpenHCS functions that have been decorated with
explicit contract declarations, allowing them to skip runtime testing
while producing the same FunctionMetadata format as external libraries.
"""

import logging
import numpy as np
from typing import Dict, List, Tuple, Any
import importlib

from openhcs.processing.backends.lib_registry.unified_registry import LibraryRegistryBase, FunctionMetadata, ProcessingContract

logger = logging.getLogger(__name__)


class OpenHCSRegistry(LibraryRegistryBase):
    """
    Registry for OpenHCS native functions with explicit contract support.

    This registry processes OpenHCS functions that have been decorated with
    explicit contract declarations, allowing them to skip runtime testing
    while producing the same FunctionMetadata format as external libraries.
    """

    # Required abstract class attributes
    MODULES_TO_SCAN = []  # Will be set dynamically
    MEMORY_TYPE = "openhcs"  # Placeholder, actual memory types come from function attributes
    FLOAT_DTYPE = np.float32

    def __init__(self):
        super().__init__("openhcs")
        # Set modules to scan to OpenHCS processing modules
        self.MODULES_TO_SCAN = self._get_openhcs_modules()

    def _get_openhcs_modules(self) -> List[str]:
        """Get list of OpenHCS processing modules to scan."""
        # Import here to avoid circular imports
        import openhcs.processing
        import os
        import pkgutil

        modules = []
        processing_path = os.path.dirname(openhcs.processing.__file__)
        processing_package = "openhcs.processing"

        # Scan all modules in openhcs.processing recursively (eliminate magic string per RST)
        EXCLUDED_MODULE_PATTERN = "lib_registry"  # Extract magic string to constant
        for importer, modname, ispkg in pkgutil.walk_packages([processing_path], processing_package + "."):
            # Skip lib_registry modules to avoid circular imports
            if EXCLUDED_MODULE_PATTERN not in modname:
                modules.append(modname)

        return modules

    def get_modules_to_scan(self) -> List[Tuple[str, Any]]:
        """Get modules to scan for OpenHCS functions."""
        modules = []
        for module_name in self.MODULES_TO_SCAN:
            try:
                module = importlib.import_module(module_name)
                modules.append((module_name, module))
            except ImportError as e:
                logger.warning(f"Could not import OpenHCS module {module_name}: {e}")
        return modules



    # ===== ESSENTIAL ABC METHODS =====
    def get_library_version(self) -> str:
        """Get OpenHCS version."""
        try:
            import openhcs
            return getattr(openhcs, '__version__', 'unknown')
        except:
            return 'unknown'

    def is_library_available(self) -> bool:
        """OpenHCS is always available."""
        return True

    def get_library_object(self):
        """Return OpenHCS processing module."""
        import openhcs.processing
        return openhcs.processing

    def get_memory_type(self) -> str:
        """Return placeholder memory type."""
        return self.MEMORY_TYPE

    def get_display_name(self) -> str:
        """Get display name for OpenHCS."""
        return "OpenHCS"

    def get_module_patterns(self) -> List[str]:
        """Get module patterns for OpenHCS."""
        return ["openhcs"]



    def discover_functions(self) -> Dict[str, FunctionMetadata]:
        """Discover OpenHCS functions with explicit contracts."""
        functions = {}
        modules = self.get_modules_to_scan()

        for module_name, module in modules:
            import inspect
            for name, func in inspect.getmembers(module, inspect.isfunction):
                # Simple: if it has a processing contract, include it
                if hasattr(func, '__processing_contract__'):
                    contract = getattr(func, '__processing_contract__')

                    metadata = FunctionMetadata(
                        name=name,
                        func=func,
                        contract=contract,
                        module=func.__module__ or "",
                        doc=(func.__doc__ or "").splitlines()[0] if func.__doc__ else "",
                        tags=["openhcs"],
                        original_name=name
                    )

                    functions[name] = metadata

        return functions

    def _generate_function_name(self, original_name: str, module_name: str) -> str:
        """Generate unique function name for OpenHCS functions."""
        # Extract meaningful part from module name
        if isinstance(module_name, str):
            module_parts = module_name.split('.')
            # Find meaningful part after 'backends'
            try:
                backends_idx = module_parts.index('backends')
                meaningful_parts = module_parts[backends_idx+1:]
                if meaningful_parts:
                    prefix = '_'.join(meaningful_parts)
                    return f"{prefix}_{original_name}"
            except ValueError:
                pass
        
        return original_name

    def _generate_tags(self, module_name: str) -> List[str]:
        """Generate tags for OpenHCS functions."""
        tags = ['openhcs']
        
        # Add module-specific tags
        if isinstance(module_name, str):
            module_parts = module_name.split('.')
            if 'analysis' in module_parts:
                tags.append('analysis')
            if 'preprocessing' in module_parts:
                tags.append('preprocessing')
            if 'segmentation' in module_parts:
                tags.append('segmentation')
        
        return tags
