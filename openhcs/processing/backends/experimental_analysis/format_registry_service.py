"""
Format registry service for automatic discovery and management.

This module provides automatic discovery of microscope format registries
following OpenHCS generic solution principles.
"""

import pkgutil
import importlib
from typing import Dict, List, Optional, Type
from pathlib import Path

from .format_registry import MicroscopeFormatRegistryBase, FormatDetectionError


class FormatRegistryService:
    """
    Service for automatic discovery and access to microscope format registries.
    
    Following OpenHCS generic solution principles, this service automatically
    discovers all format registry implementations without hardcoded imports.
    """
    
    _registry_cache: Optional[Dict[str, Type[MicroscopeFormatRegistryBase]]] = None
    _instance_cache: Optional[Dict[str, MicroscopeFormatRegistryBase]] = None
    
    @classmethod
    def _discover_registries(cls) -> Dict[str, Type[MicroscopeFormatRegistryBase]]:
        """
        Automatically discover all format registry classes.
        
        Returns:
            Dictionary mapping format names to registry classes
        """
        if cls._registry_cache is not None:
            return cls._registry_cache
        
        registries = {}
        
        # Get the package path for experimental_analysis
        import openhcs.processing.backends.experimental_analysis
        package_path = openhcs.processing.backends.experimental_analysis.__path__
        
        # Walk through all modules in the package
        for importer, modname, ispkg in pkgutil.walk_packages(
            package_path, 
            prefix="openhcs.processing.backends.experimental_analysis."
        ):
            if ispkg:
                continue
                
            try:
                module = importlib.import_module(modname)
                
                # Find all classes that inherit from MicroscopeFormatRegistryBase
                for attr_name in dir(module):
                    attr = getattr(module, attr_name)
                    
                    if (isinstance(attr, type) and 
                        issubclass(attr, MicroscopeFormatRegistryBase) and 
                        attr is not MicroscopeFormatRegistryBase):
                        
                        # Validate that the registry has required class attributes
                        if hasattr(attr, 'FORMAT_NAME') and attr.FORMAT_NAME:
                            registries[attr.FORMAT_NAME] = attr
                            
            except ImportError:
                # Skip modules that can't be imported
                continue
        
        cls._registry_cache = registries
        return registries
    
    @classmethod
    def get_all_format_registries(cls) -> Dict[str, Type[MicroscopeFormatRegistryBase]]:
        """
        Get all discovered format registry classes.
        
        Returns:
            Dictionary mapping format names to registry classes
        """
        return cls._discover_registries()
    
    @classmethod
    def get_registry_class_for_format(cls, format_name: str) -> Type[MicroscopeFormatRegistryBase]:
        """
        Get registry class for specific format.
        
        Args:
            format_name: Name of the microscope format
            
        Returns:
            Registry class for the format
            
        Raises:
            FormatDetectionError: If format is not supported
        """
        registries = cls.get_all_format_registries()
        
        if format_name not in registries:
            available_formats = list(registries.keys())
            raise FormatDetectionError(
                f"Unsupported format '{format_name}'. Available formats: {available_formats}"
            )
        
        return registries[format_name]
    
    @classmethod
    def get_registry_instance_for_format(cls, format_name: str) -> MicroscopeFormatRegistryBase:
        """
        Get registry instance for specific format.
        
        Args:
            format_name: Name of the microscope format
            
        Returns:
            Registry instance for the format
            
        Raises:
            FormatDetectionError: If format is not supported
        """
        if cls._instance_cache is None:
            cls._instance_cache = {}
        
        if format_name not in cls._instance_cache:
            registry_class = cls.get_registry_class_for_format(format_name)
            cls._instance_cache[format_name] = registry_class()
        
        return cls._instance_cache[format_name]
    
    @classmethod
    def detect_format_from_file(cls, file_path: str) -> str:
        """
        Automatically detect microscope format from file.
        
        Args:
            file_path: Path to the results file
            
        Returns:
            Detected format name
            
        Raises:
            FormatDetectionError: If format cannot be detected
        """
        file_path_obj = Path(file_path)
        
        if not file_path_obj.exists():
            raise FormatDetectionError(f"File not found: {file_path}")
        
        registries = cls.get_all_format_registries()
        
        # Try each registry to see which one can handle the file
        for format_name, registry_class in registries.items():
            try:
                registry_instance = cls.get_registry_instance_for_format(format_name)
                
                # Check if file extension is supported
                if file_path_obj.suffix in registry_instance.SUPPORTED_EXTENSIONS:
                    # Try to read and process a small sample
                    try:
                        raw_df = registry_instance.read_results(file_path)
                        features = registry_instance.extract_features(raw_df)
                        
                        # If we can extract features, this format works
                        if features:
                            return format_name
                            
                    except Exception:
                        # This format doesn't work, try next one
                        continue
                        
            except Exception:
                # Skip this registry if it fails
                continue
        
        # If no format worked, raise error
        available_formats = list(registries.keys())
        raise FormatDetectionError(
            f"Could not detect format for file {file_path}. "
            f"Available formats: {available_formats}"
        )
    
    @classmethod
    def get_supported_formats(cls) -> List[str]:
        """
        Get list of all supported format names.
        
        Returns:
            List of supported format names
        """
        registries = cls.get_all_format_registries()
        return list(registries.keys())
    
    @classmethod
    def get_supported_extensions(cls) -> Dict[str, List[str]]:
        """
        Get mapping of formats to their supported file extensions.
        
        Returns:
            Dictionary mapping format names to supported extensions
        """
        registries = cls.get_all_format_registries()
        extensions_map = {}
        
        for format_name, registry_class in registries.items():
            registry_instance = cls.get_registry_instance_for_format(format_name)
            extensions_map[format_name] = list(registry_instance.SUPPORTED_EXTENSIONS)
        
        return extensions_map
    
    @classmethod
    def clear_cache(cls):
        """Clear registry and instance caches (useful for testing)."""
        cls._registry_cache = None
        cls._instance_cache = None
