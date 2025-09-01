"""
ThermoFisher CX5 format registry implementation.

This module provides format-specific processing for ThermoFisher CX5 microscope
data following OpenHCS registry architecture patterns.
"""

import string
from typing import Dict, List, Any
import pandas as pd

from .format_registry import MicroscopeFormatRegistryBase


class CX5FormatRegistry(MicroscopeFormatRegistryBase):
    """
    Registry for ThermoFisher CX5 microscope format.
    
    Handles CX5-specific data structure parsing, feature extraction,
    and plate organization following OpenHCS registry patterns.
    """
    
    FORMAT_NAME = "EDDU_CX5"
    SHEET_NAME = "Rawdata"
    SUPPORTED_EXTENSIONS = (".xlsx", ".xls")
    
    def extract_features(self, raw_df: pd.DataFrame) -> List[str]:
        """
        Extract feature column names from CX5 raw data.
        
        CX5 format stores features after the 'Replicate' column.
        
        Args:
            raw_df: Raw CX5 data DataFrame
            
        Returns:
            List of feature column names
            
        Raises:
            ValueError: If feature extraction fails
        """
        try:
            # Find the 'Replicate' column and extract features after it
            replicate_col_idx = raw_df.columns.str.find("Replicate").argmax()
            feature_columns = raw_df.iloc[:, replicate_col_idx + 1:-1].columns.tolist()
            
            if not feature_columns:
                raise ValueError("No features found in CX5 data")
            
            return feature_columns
            
        except Exception as e:
            raise ValueError(f"Failed to extract features from CX5 data: {e}")
    
    def extract_plate_names(self, raw_df: pd.DataFrame) -> List[str]:
        """
        Extract plate identifiers from CX5 raw data.
        
        CX5 format stores plate names in the second column.
        
        Args:
            raw_df: Raw CX5 data DataFrame
            
        Returns:
            List of unique plate identifiers
            
        Raises:
            ValueError: If plate extraction fails
        """
        try:
            if len(raw_df.columns) < 2:
                raise ValueError("CX5 data must have at least 2 columns")
            
            # Plate names are in the second column (index 1)
            plate_names = raw_df.iloc[:, 1].unique().tolist()
            
            # Remove any NaN values
            plate_names = [name for name in plate_names if pd.notna(name)]
            
            if not plate_names:
                raise ValueError("No plate names found in CX5 data")
            
            return plate_names
            
        except Exception as e:
            raise ValueError(f"Failed to extract plate names from CX5 data: {e}")
    
    def create_plates_dict(self, raw_df: pd.DataFrame) -> Dict[str, Dict[str, Dict[str, Any]]]:
        """
        Create nested dictionary structure for CX5 plate data.
        
        Args:
            raw_df: Raw CX5 data DataFrame
            
        Returns:
            Dictionary structure: {plate_id: {well_id: {feature: None}}}
            
        Raises:
            ValueError: If data structure creation fails
        """
        try:
            features = self.extract_features(raw_df)
            plate_names = self.extract_plate_names(raw_df)
            
            # Generate standard 96-well plate layout
            wells = self._generate_well_ids()
            
            # Create nested structure
            plates_dict = {}
            for plate_id in plate_names:
                plates_dict[plate_id] = {}
                for well_id in wells:
                    plates_dict[plate_id][well_id] = {feature: None for feature in features}
            
            return plates_dict
            
        except Exception as e:
            raise ValueError(f"Failed to create CX5 plates dictionary: {e}")
    
    def fill_plates_dict(self, raw_df: pd.DataFrame, plates_dict: Dict[str, Dict[str, Dict[str, Any]]]) -> Dict[str, Dict[str, Dict[str, Any]]]:
        """
        Fill plates dictionary with actual measurement values from CX5 data.
        
        CX5 format stores row/column indices in columns 2 and 3.
        
        Args:
            raw_df: Raw CX5 data DataFrame
            plates_dict: Empty plates dictionary structure
            
        Returns:
            Filled plates dictionary with measurement values
            
        Raises:
            ValueError: If data filling fails
        """
        try:
            features = self.extract_features(raw_df)
            
            for index, row in raw_df.iterrows():
                # Extract plate, row, and column information
                plate_id = row.iloc[1]  # Plate name in second column
                row_idx = row.iloc[2]   # Row index in third column
                col_idx = row.iloc[3]   # Column index in fourth column
                
                # Convert row/column indices to well ID
                well_id = self._row_col_to_well(row_idx, col_idx)
                
                # Fill feature values
                if plate_id in plates_dict and well_id in plates_dict[plate_id]:
                    for feature in features:
                        if feature in row.index:
                            plates_dict[plate_id][well_id][feature] = row[feature]
            
            return plates_dict
            
        except Exception as e:
            raise ValueError(f"Failed to fill CX5 plates dictionary: {e}")
    
    def _generate_well_ids(self) -> List[str]:
        """
        Generate standard 96-well plate well IDs.
        
        Returns:
            List of well IDs (A01, A02, ..., H12)
        """
        rows = [string.ascii_uppercase[i] for i in range(8)]  # A-H
        cols = [i + 1 for i in range(12)]  # 1-12
        
        wells = []
        for row in rows:
            for col in cols:
                wells.append(f"{row}{col:02d}")
        
        return wells
    
    def _row_col_to_well(self, row_idx: int, col_idx: int) -> str:
        """
        Convert row/column indices to well ID.
        
        Args:
            row_idx: Row index (1-based)
            col_idx: Column index (1-based)
            
        Returns:
            Well ID (e.g., "A01")
            
        Raises:
            ValueError: If indices are out of range
        """
        try:
            # Convert to 0-based indices
            row_zero_based = int(row_idx) - 1
            col_zero_based = int(col_idx) - 1
            
            # Validate ranges
            if row_zero_based < 0 or row_zero_based >= 8:
                raise ValueError(f"Row index {row_idx} out of range (1-8)")
            
            if col_zero_based < 0 or col_zero_based >= 12:
                raise ValueError(f"Column index {col_idx} out of range (1-12)")
            
            # Convert to well ID
            row_letter = string.ascii_uppercase[row_zero_based]
            well_id = f"{row_letter}{col_idx:02d}"
            
            return well_id
            
        except (ValueError, TypeError) as e:
            raise ValueError(f"Invalid row/column indices: {row_idx}, {col_idx}: {e}")
