"""
Base classes for microscope format registry system.

This module provides the abstract base class and common functionality for
microscope format registries, following OpenHCS registry architecture patterns.
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Dict, List, Any, Optional, Tuple
import pandas as pd
from pathlib import Path


@dataclass(frozen=True)
class MicroscopeFormatConfig:
    """Configuration for microscope format processing."""
    format_name: str
    sheet_name: Optional[str]
    supported_extensions: Tuple[str, ...]
    feature_extraction_method: str
    plate_detection_method: str


class MicroscopeFormatRegistryBase(ABC):
    """
    Abstract base class for microscope format registries.
    
    Following OpenHCS registry patterns, this provides a unified interface
    for processing different microscope data formats while eliminating
    code duplication and hardcoded format-specific logic.
    """
    
    # Abstract class attributes - each implementation must define these
    FORMAT_NAME: str
    SHEET_NAME: Optional[str]  # None means use first sheet
    SUPPORTED_EXTENSIONS: Tuple[str, ...]
    
    def __init__(self):
        """Initialize registry with format configuration."""
        self.config = MicroscopeFormatConfig(
            format_name=self.FORMAT_NAME,
            sheet_name=self.SHEET_NAME,
            supported_extensions=self.SUPPORTED_EXTENSIONS,
            feature_extraction_method=f"extract_features_{self.FORMAT_NAME.lower()}",
            plate_detection_method=f"extract_plates_{self.FORMAT_NAME.lower()}"
        )
    
    @property
    def format_name(self) -> str:
        """Get format name for this registry."""
        return self.FORMAT_NAME
    
    @abstractmethod
    def extract_features(self, raw_df: pd.DataFrame) -> List[str]:
        """
        Extract feature column names from raw microscope data.
        
        Args:
            raw_df: Raw data DataFrame from microscope
            
        Returns:
            List of feature column names
            
        Raises:
            ValueError: If feature extraction fails
        """
        pass
    
    @abstractmethod
    def extract_plate_names(self, raw_df: pd.DataFrame) -> List[str]:
        """
        Extract plate identifiers from raw microscope data.
        
        Args:
            raw_df: Raw data DataFrame from microscope
            
        Returns:
            List of plate identifiers
            
        Raises:
            ValueError: If plate extraction fails
        """
        pass
    
    @abstractmethod
    def create_plates_dict(self, raw_df: pd.DataFrame) -> Dict[str, Dict[str, Dict[str, Any]]]:
        """
        Create nested dictionary structure for plate data.
        
        Args:
            raw_df: Raw data DataFrame from microscope
            
        Returns:
            Dictionary structure: {plate_id: {well_id: {feature: value}}}
            
        Raises:
            ValueError: If data structure creation fails
        """
        pass
    
    @abstractmethod
    def fill_plates_dict(self, raw_df: pd.DataFrame, plates_dict: Dict[str, Dict[str, Dict[str, Any]]]) -> Dict[str, Dict[str, Dict[str, Any]]]:
        """
        Fill plates dictionary with actual measurement values.
        
        Args:
            raw_df: Raw data DataFrame from microscope
            plates_dict: Empty plates dictionary structure
            
        Returns:
            Filled plates dictionary with measurement values
            
        Raises:
            ValueError: If data filling fails
        """
        pass
    
    def read_results(self, results_path: str) -> pd.DataFrame:
        """
        Read results file using format-specific logic.
        
        Args:
            results_path: Path to results file
            
        Returns:
            Raw data DataFrame
            
        Raises:
            FileNotFoundError: If results file doesn't exist
            ValueError: If file format is not supported
        """
        results_file = Path(results_path)
        
        if not results_file.exists():
            raise FileNotFoundError(f"Results file not found: {results_path}")
        
        if results_file.suffix not in self.SUPPORTED_EXTENSIONS:
            raise ValueError(f"Unsupported file extension {results_file.suffix} for format {self.FORMAT_NAME}")
        
        if results_path.endswith('.csv'):
            return pd.read_csv(results_path)
        else:
            # Excel file
            xls = pd.ExcelFile(results_path)
            sheet_name = self.SHEET_NAME if self.SHEET_NAME else xls.sheet_names[0]
            return pd.read_excel(xls, sheet_name)
    
    def process_data(self, results_path: str) -> Dict[str, Any]:
        """
        Complete data processing pipeline for this format.
        
        Args:
            results_path: Path to results file
            
        Returns:
            Processed data structure ready for analysis
            
        Raises:
            ValueError: If data processing fails
        """
        # Read raw data
        raw_df = self.read_results(results_path)
        
        # Extract features and plates
        features = self.extract_features(raw_df)
        plate_names = self.extract_plate_names(raw_df)
        
        # Create and fill data structures
        plates_dict = self.create_plates_dict(raw_df)
        filled_plates_dict = self.fill_plates_dict(raw_df, plates_dict)
        
        return {
            'raw_df': raw_df,
            'features': features,
            'plate_names': plate_names,
            'plates_dict': filled_plates_dict,
            'format_name': self.FORMAT_NAME
        }
    
    def validate_data_structure(self, data: Dict[str, Any]) -> bool:
        """
        Validate processed data structure.
        
        Args:
            data: Processed data dictionary
            
        Returns:
            True if data structure is valid
            
        Raises:
            ValueError: If validation fails
        """
        required_keys = ['raw_df', 'features', 'plate_names', 'plates_dict', 'format_name']
        
        for key in required_keys:
            if key not in data:
                raise ValueError(f"Missing required key in data structure: {key}")
        
        if not data['features']:
            raise ValueError("No features extracted from data")
        
        if not data['plate_names']:
            raise ValueError("No plates detected in data")
        
        return True


class FormatDetectionError(Exception):
    """Raised when microscope format cannot be detected."""
    pass


class DataProcessingError(Exception):
    """Raised when data processing fails."""
    pass
