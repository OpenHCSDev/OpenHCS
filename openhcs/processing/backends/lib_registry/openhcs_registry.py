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

from openhcs.processing.backends.lib_registry.unified_registry import LibraryRegistryBase, FunctionMetadata

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
    MEMORY_TYPE = None  # OpenHCS functions have their own memory type attributes
    FLOAT_DTYPE = np.float32

    def __init__(self):
        super().__init__("openhcs")
        # Set modules to scan to OpenHCS processing modules
        self.MODULES_TO_SCAN = self._get_openhcs_modules()

    def _get_openhcs_modules(self) -> List[str]:
        """Get list of OpenHCS processing modules to scan using automatic discovery."""
        import pkgutil
        import os

        modules = []

        # Get the backends directory path
        backends_path = os.path.dirname(__file__)  # lib_registry directory
        backends_path = os.path.dirname(backends_path)  # backends directory

        # Walk through all modules in openhcs.processing.backends recursively
        for importer, module_name, ispkg in pkgutil.walk_packages(
            [backends_path],
            "openhcs.processing.backends."
        ):
            # Skip lib_registry modules to avoid circular imports
            if "lib_registry" in module_name:
                continue

            # Skip __pycache__ and other non-module files
            if "__pycache__" in module_name:
                continue

            try:
                # Try to import the module to ensure it's valid
                importlib.import_module(module_name)
                modules.append(module_name)
            except ImportError as e:
                # Module has import issues, skip it but log for debugging
                logger.debug(f"Skipping module {module_name}: {e}")
                continue

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
        """Discover OpenHCS functions with explicit contracts and filter by backend availability."""
        functions = {}
        modules = self.get_modules_to_scan()

        for module_name, module in modules:
            import inspect
            for name, func in inspect.getmembers(module, inspect.isfunction):
                # Simple: if it has a processing contract, include it
                if hasattr(func, '__processing_contract__'):
                    contract = getattr(func, '__processing_contract__')

                    # Check if function's backend is available before including it
                    if not self._is_function_backend_available(func):
                        logger.debug(f"Skipping {name} - backend not available")
                        continue

                    # Apply contract wrapper (adds slice_by_slice for FLEXIBLE)
                    wrapped_func = self.apply_contract_wrapper(func, contract)

                    # Generate unique function name using module information
                    unique_name = self._generate_function_name(name, module_name)

                    # Extract full docstring, not just first line
                    doc = self._extract_function_docstring(func)

                    metadata = FunctionMetadata(
                        name=unique_name,
                        func=wrapped_func,
                        contract=contract,
                        registry=self,
                        module=func.__module__ or "",
                        doc=doc,
                        tags=["openhcs"],
                        original_name=name
                    )

                    functions[unique_name] = metadata

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

    def _is_function_backend_available(self, func) -> bool:
        """
        Check if the function's backend is available.

        For OpenHCS functions with mixed backends, we need to check each function
        individually based on its memory type attributes.

        Args:
            func: Function to check

        Returns:
            True if the function's backend is available, False otherwise
        """
        # Get the function's memory type
        memory_type = None
        if hasattr(func, 'input_memory_type'):
            memory_type = func.input_memory_type
        elif hasattr(func, 'output_memory_type'):
            memory_type = func.output_memory_type
        elif hasattr(func, 'backend'):
            memory_type = func.backend

        if not memory_type:
            # If no memory type specified, assume numpy (always available)
            return True

        # Check backend availability based on memory type
        return self._check_backend_availability(memory_type)

    def _check_backend_availability(self, memory_type: str) -> bool:
        """
        Check if a specific backend/memory type is available using the registry system.

        This uses the existing registry system as the source of truth for backend availability,
        avoiding hardcoded checks and ensuring consistency across the system.

        Args:
            memory_type: Memory type to check (e.g., "cupy", "torch", "numpy", "pyclesperanto")

        Returns:
            True if backend is available, False otherwise
        """
        # Import registry service to get registry instances
        from openhcs.processing.backends.lib_registry.registry_service import RegistryService

        # Special case: numpy is always available (no dedicated registry)
        if memory_type == "numpy":
            return True

        # Get all available registries
        try:
            registry_classes = RegistryService._discover_registries()

            # Find the registry that matches this memory type
            for registry_class in registry_classes:
                try:
                    registry_instance = registry_class()

                    # Check if this registry handles the memory type
                    if hasattr(registry_instance, 'MEMORY_TYPE') and registry_instance.MEMORY_TYPE == memory_type:
                        # Use the registry's own availability check as source of truth
                        return registry_instance.is_library_available()

                except Exception as e:
                    logger.debug(f"Failed to check registry {registry_class.__name__}: {e}")
                    continue

            # If no registry found for this memory type, it's not available
            logger.debug(f"No registry found for memory type: {memory_type}")
            return False

        except Exception as e:
            logger.warning(f"Failed to check backend availability for {memory_type}: {e}")
            return False

    def _extract_function_docstring(self, func) -> str:
        """
        Extract the full docstring from a function, with proper formatting.

        Args:
            func: Function to extract docstring from

        Returns:
            Formatted docstring or empty string if none
        """
        if not func.__doc__:
            return ""

        # Get the full docstring
        docstring = func.__doc__.strip()

        # For UI display, we want a concise but informative description
        # Take the first paragraph (up to first double newline) or first 200 chars
        lines = docstring.split('\n')

        # Find the first non-empty line (summary)
        summary_lines = []
        for line in lines:
            line = line.strip()
            if not line and summary_lines:
                # Empty line after content - end of summary
                break
            if line:
                summary_lines.append(line)

        if summary_lines:
            summary = ' '.join(summary_lines)
            # Limit length for UI display
            if len(summary) > 200:
                summary = summary[:197] + "..."
            return summary

        return ""
