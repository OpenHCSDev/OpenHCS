"""
MetaXpress format registry implementation.

This module provides format-specific processing for MetaXpress microscope
data following OpenHCS registry architecture patterns.
"""

import string
from typing import Dict, List, Any
import pandas as pd

from .format_registry import MicroscopeFormatRegistryBase


class MetaXpressFormatRegistry(MicroscopeFormatRegistryBase):
    """
    Registry for MetaXpress microscope format.
    
    Handles MetaXpress-specific data structure parsing, feature extraction,
    and plate organization following OpenHCS registry patterns.
    """
    
    FORMAT_NAME = "EDDU_metaxpress"
    SHEET_NAME = None  # Use first sheet
    SUPPORTED_EXTENSIONS = (".xlsx", ".xls", ".csv")
    
    def extract_features(self, raw_df: pd.DataFrame) -> List[str]:
        """
        Extract feature column names from MetaXpress raw data.
        
        MetaXpress format stores features in rows where the first column is null.
        
        Args:
            raw_df: Raw MetaXpress data DataFrame
            
        Returns:
            List of feature column names
            
        Raises:
            ValueError: If feature extraction fails
        """
        try:
            # Find rows where first column is null - these contain feature names
            feature_rows = raw_df[pd.isnull(raw_df.iloc[:, 0])]
            
            if feature_rows.empty:
                raise ValueError("No feature rows found in MetaXpress data")
            
            # Get feature names from the first feature row, starting from column 2
            feature_names = feature_rows.iloc[0].tolist()[2:]
            
            # Remove any NaN values
            feature_names = [name for name in feature_names if pd.notna(name)]
            
            if not feature_names:
                raise ValueError("No features found in MetaXpress data")
            
            return feature_names
            
        except Exception as e:
            raise ValueError(f"Failed to extract features from MetaXpress data: {e}")
    
    def extract_plate_names(self, raw_df: pd.DataFrame) -> List[str]:
        """
        Extract plate identifiers from MetaXpress raw data.
        
        MetaXpress format stores plate names in rows where first column is 'Plate Name'.
        
        Args:
            raw_df: Raw MetaXpress data DataFrame
            
        Returns:
            List of unique plate identifiers
            
        Raises:
            ValueError: If plate extraction fails
        """
        try:
            # Find rows where first column is 'Plate Name'
            plate_name_rows = raw_df[raw_df.iloc[:, 0] == 'Plate Name']
            
            if plate_name_rows.empty:
                raise ValueError("No 'Plate Name' rows found in MetaXpress data")
            
            # Extract plate names from second column
            plate_names = plate_name_rows.iloc[:, 1].unique().tolist()
            
            # Remove any NaN values
            plate_names = [name for name in plate_names if pd.notna(name)]
            
            if not plate_names:
                raise ValueError("No plate names found in MetaXpress data")
            
            return plate_names
            
        except Exception as e:
            raise ValueError(f"Failed to extract plate names from MetaXpress data: {e}")
    
    def create_plates_dict(self, raw_df: pd.DataFrame) -> Dict[str, Dict[str, Dict[str, Any]]]:
        """
        Create nested dictionary structure for MetaXpress plate data.
        
        Args:
            raw_df: Raw MetaXpress data DataFrame
            
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
            raise ValueError(f"Failed to create MetaXpress plates dictionary: {e}")
    
    def fill_plates_dict(self, raw_df: pd.DataFrame, plates_dict: Dict[str, Dict[str, Dict[str, Any]]]) -> Dict[str, Dict[str, Dict[str, Any]]]:
        """
        Fill plates dictionary with actual measurement values from MetaXpress data.
        
        MetaXpress format has a complex structure where data collection starts
        after plate name declaration and ends at 'Barcode' rows.
        
        Args:
            raw_df: Raw MetaXpress data DataFrame
            plates_dict: Empty plates dictionary structure
            
        Returns:
            Filled plates dictionary with measurement values
            
        Raises:
            ValueError: If data filling fails
        """
        try:
            features = self.extract_features(raw_df)
            
            # Create column mapping for easier access
            column_names = ["Well", "Laser_Focus"] + features
            df_with_names = raw_df.set_axis(column_names, axis=1, copy=False)
            
            current_plate = None
            collecting_data = False
            
            for index, row in df_with_names.iterrows():
                first_col = row.iloc[0]
                
                # Stop collecting when we hit 'Barcode'
                if first_col == "Barcode":
                    collecting_data = False
                    continue
                
                # Start collecting data when we hit a null first column (after plate name)
                if pd.isnull(first_col) and current_plate is not None:
                    collecting_data = True
                    continue
                
                # Set current plate when we hit 'Plate Name'
                if first_col == "Plate Name":
                    current_plate = row.iloc[1]
                    collecting_data = False
                    continue
                
                # Collect data if we're in collection mode
                if collecting_data and current_plate and not pd.isnull(first_col):
                    well_id = first_col
                    
                    if (current_plate in plates_dict and 
                        well_id in plates_dict[current_plate]):
                        
                        # Fill feature values
                        for feature in features:
                            if feature in row.index:
                                plates_dict[current_plate][well_id][feature] = row[feature]
            
            return plates_dict
            
        except Exception as e:
            raise ValueError(f"Failed to fill MetaXpress plates dictionary: {e}")
    
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
