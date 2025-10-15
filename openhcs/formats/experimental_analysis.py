"""
Experimental analysis for CX5 and MetaXpress microscopy data.

This module provides comprehensive analysis capabilities for high-content screening data
from ThermoFisher CX5 and MetaXpress systems. It handles experimental design configuration,
data parsing, replicate averaging, normalization, and result export.

Supports:
- CX5 format (ThermoFisher)
- MetaXpress format (Molecular Devices)
- Complex experimental designs with multiple conditions, doses, and replicates
- Control-based normalization
- Excel-based configuration and output
"""

import copy
import xlsxwriter
import string
import numpy as np
import pandas as pd
import sys
from typing import Optional




def read_results(results_path: str, scope: Optional[str] = None) -> pd.DataFrame:
    """
    Read results data from Excel or CSV file based on microscope format.

    Args:
        results_path: Path to Excel or CSV results file
        scope: Microscope format ('EDDU_CX5' or 'EDDU_metaxpress')

    Returns:
        DataFrame containing the raw results data

    Raises:
        SystemExit: If scope is not recognized
    """
    if results_path.endswith('.csv'):
        # Handle CSV files (like MetaXpress consolidated output)
        raw_df = pd.read_csv(results_path)
    else:
        # Handle Excel files
        xls = pd.ExcelFile(results_path)
        if scope == "EDDU_CX5":
            raw_df = pd.read_excel(xls, 'Rawdata')
        elif scope == "EDDU_metaxpress":
            raw_df = pd.read_excel(xls, xls.sheet_names[0])
        else:
            print("microscope "+str(scope)+" not known. Exiting")
            sys.exit()
    return raw_df

def get_features(raw_df,scope=None):
    if scope == "EDDU_CX5":
        return get_features_EDDU_CX5(raw_df)
    if scope == "EDDU_metaxpress":
        return get_features_EDDU_metaxpress(raw_df)
    else:
        print("microscope "+str(scope)+" not known. Exiting")
        sys.exit()

def is_N_row(row_name):
    row_name = str(row_name).lower()
    is_N = False
    if row_name == "n" or row_name=="ns":
        is_N = True
    if row_name == "replicate" or row_name=="replicates":
        is_N = True
    return is_N


def is_well_all_replicates_row(row_name):
    row_name = str(row_name).lower()
    return row_name == "well" or row_name == "wells"

def is_well_specific_replicate_row(row_name):
    row_name = str(row_name).lower()
    if 'well' in row_name:
        return row_name[-1].isdigit()
    else: return False

def read_plate_layout(config_path):
    xls = pd.ExcelFile(config_path)
    df = pd.read_excel(xls, 'drug_curve_map',index_col=0,header=None)
    df = df.dropna(how='all')
    layout={}
    condition=None
    doses=None
    wells=None
    plate_groups=None
    N = None
    specific_N = None
    scope = None
    per_well_datapoints = False
    conditions=[]
    ctrl_wells=None
    ctrl_wells_aligned=None
    ctrl_groups=None
    ctrl_positions_replicates=None
    ctrl_positions=None
    excluded_wells=None
    excluded_wells_aligned=None
    excluded_groups=None
    excluded_positions_replicates=None
    excluded_positions=None

    def sanitize_compare(string1,string2):
        string1 = str(string1).lower()
        string2 = str(string2).lower()
        string1 = string1.replace('_','')
        string1 = string1.replace(' ','')
        string2 = string2.replace('_','')
        string2 = string2.replace(' ','')
        if len(string1) > 0 and not string1[-1] == 's': string1 +='s'
        if len(string2) > 0 and not string2[-1] == 's': string2 +='s'
        return string1 == string2

    for i,row in df.iterrows():
        #check max number of replicates
        row_content = str(row.iloc[0]) if pd.notna(row.iloc[0]) else ''
        row_name = str(i) if pd.notna(i) else ''

        # Check both row_content and row_name for N parameter (for compatibility)
        if is_N_row(row_content) or is_N_row(row_name):
            if is_N_row(row_name):
                N = int(row.iloc[0])  # Value is in first column when N is in index
            else:
                N = int(row.iloc[1])  # Value is in second column when N is in content
            for j in range(N):
                layout["N"+str(j+1)]={}
        #load microscope
        if sanitize_compare(row_content,'scope') or sanitize_compare(row_content,'microscope') or sanitize_compare(row_name,'scope') or sanitize_compare(row_name,'microscope'):
            if sanitize_compare(row_name,'scope') or sanitize_compare(row_name,'microscope'):
                scope = row.iloc[0]  # Value is in first column when scope is in index
            else:
                scope = row.iloc[1]  # Value is in second column when scope is in content

        #load per-well datapoints flag
        if (sanitize_compare(row_content,'per well datapoints') or
            sanitize_compare(row_content,'per well datapoint') or
            sanitize_compare(row_content,'individual wells') or
            sanitize_compare(row_content,'individual well') or
            sanitize_compare(row_name,'per well datapoints') or
            sanitize_compare(row_name,'per well datapoint') or
            sanitize_compare(row_name,'individual wells') or
            sanitize_compare(row_name,'individual well')):
            if (sanitize_compare(row_name,'per well datapoints') or
                sanitize_compare(row_name,'per well datapoint') or
                sanitize_compare(row_name,'individual wells') or
                sanitize_compare(row_name,'individual well')):
                value = str(row.iloc[0]).lower().strip()  # Value in first column when parameter is in index
            else:
                value = str(row.iloc[1]).lower().strip()  # Value in second column when parameter is in content
            per_well_datapoints = value in ['true', '1', 'yes', 'on', 'enabled']

        #finished reading controls
        if sanitize_compare(row.name,'plate group') and ctrl_wells is not None:
            if ctrl_groups is None:
                ctrl_groups = []
            ctrl_groups += row.dropna().tolist()
            continue
#        if sanitize_compare(row.name,'plate group') and not ctrl_wells is None and not ctrl_groups is None:
#            ctrl_positions = []
#            for i in range(len(ctrl_wells_aligned)):
#                if not ctrl_well_replicates is None:
#                    ctrl_positions.append((ctrl_wells_aligned[i],ctrl_groups[i],ctrl_well_replicates[i]))
#                else:
#                    ctrl_positions = None
#            continue

        #get control wells
        if sanitize_compare(row.name,'control') or sanitize_compare(row.name,'control well'):
            if ctrl_wells is None:
                ctrl_wells = []
            ctrl_wells+=row.dropna().tolist()
            continue

        #get excluded wells (following same pattern as Controls)
        row_content = str(row.iloc[0]) if pd.notna(row.iloc[0]) else ''
        row_name = str(row.name) if pd.notna(row.name) else ''

        # Check both row_content and row_name for compatibility with existing inconsistent logic
        if (sanitize_compare(row_content,'exclude wells') or sanitize_compare(row_content,'excluded wells') or sanitize_compare(row_content,'exclude') or
            sanitize_compare(row_name,'exclude wells') or sanitize_compare(row_name,'excluded wells') or sanitize_compare(row_name,'exclude')):
            if excluded_wells is None:
                excluded_wells = []
            excluded_wells+=row.dropna().tolist()
            continue

        #get plate group for excluded wells
        if ((sanitize_compare(row_content,'plate group') or sanitize_compare(row_name,'plate group')) and
            excluded_wells is not None):
            if excluded_groups is None:
                excluded_groups = []
            excluded_groups += row.dropna().tolist()
            continue

        #get replicate for excluded well position
        if ((sanitize_compare(row_content,'group n') or sanitize_compare(row_name,'group n')) and
            excluded_wells is not None):
            if excluded_positions_replicates is None:
                excluded_positions_replicates = []
            if excluded_wells_aligned is None:
                excluded_wells_aligned = []
            excluded_positions_replicates+=row.dropna().tolist()
            excluded_wells_aligned += excluded_wells
            excluded_wells = None  # Reset to stop processing more plate groups
            continue

        #get replicate for ctrl position
        if sanitize_compare(row.name,'group n'):
            if ctrl_positions_replicates is None:
                ctrl_positions_replicates = []
            if ctrl_wells_aligned is None:
                ctrl_wells_aligned = []
            ctrl_positions_replicates+=row.dropna().tolist()
            ctrl_wells_aligned += ctrl_wells
            continue

        #get new condition name
        #finished reading controls and excluded wells
        if sanitize_compare(row_content,'condition') or sanitize_compare(row_name,'condition'):
            # make control well dict
            if ctrl_wells_aligned is not None:
                ctrl_positions = {"N"+str(i+1):[] for i in range(N)}
                for i in range(len(ctrl_wells_aligned)):
                    if ctrl_positions_replicates is not None:
                        ctrl_positions["N"+str(ctrl_positions_replicates[i])].append((ctrl_wells_aligned[i],ctrl_groups[i]))
                        ctrl_wells = None
                    else:
                        ctrl_positions = None
            else:
                # No controls defined in config
                ctrl_positions = None

            # make excluded wells dict (following same pattern as controls)
            if excluded_wells_aligned is not None:
                excluded_positions = {"N"+str(i+1):[] for i in range(N)}

                # Filter out non-well entries from excluded_wells_aligned (like "Exclude Wells")
                filtered_excluded_wells = [w for w in excluded_wells_aligned if w != "Exclude Wells"]
                # Filter out non-plate entries from excluded_groups (like "Plate Group")
                filtered_excluded_groups = [g for g in excluded_groups if g != "Plate Group"]
                # Filter out non-numeric entries from excluded_positions_replicates (like "Group N")
                filtered_excluded_replicates = [r for r in excluded_positions_replicates if r != "Group N" and isinstance(r, (int, float))]

                # Build the excluded positions mapping
                for i in range(min(len(filtered_excluded_wells), len(filtered_excluded_groups), len(filtered_excluded_replicates))):
                    replicate_key = "N" + str(int(filtered_excluded_replicates[i]))
                    if replicate_key in excluded_positions:
                        excluded_positions[replicate_key].append((filtered_excluded_wells[i], filtered_excluded_groups[i]))

                excluded_wells = None
            else:
                excluded_positions = None

            #make dict[replicate][condition][dose]
            for i in range(N):
                if row.iloc[0] not in layout["N"+str(i+1)].keys():
                    layout["N"+str(i+1)][row.iloc[0]]={}
            condition=row.iloc[0]
            conditions.append(condition)
        if sanitize_compare(row.name,'dose'):
            doses=row.dropna().tolist()

        #if well is same for all Ns
        if is_well_all_replicates_row(row.name):
            wells=row.dropna().tolist()
            specific_N = None
        # or not
        if is_well_specific_replicate_row(row.name):
            specific_N = int(row.name[-1])
            wells=row.dropna().tolist()

        # add plate group to wells from previous row
        if sanitize_compare(row.name,'plate group'):
            plate_groups=row.dropna().tolist()
            if specific_N == None:
                for i in range(N):
                    for y in range(len(doses)):
                        #add to all Ns
                        if doses[y] not in layout["N"+str(i+1)][condition].keys():
                            layout["N"+str(i+1)][condition][doses[y]]=[]
                        # Add ALL wells for this dose, not just wells[y]
                        for well_idx, well in enumerate(wells):
                            if well_idx < len(plate_groups):
                                layout["N"+str(i+1)][condition][doses[y]].append((well, plate_groups[well_idx]))
            else:
                for y in range(len(doses)):
                    #add to specific N
                    if doses[y] not in layout["N"+str(specific_N)][condition].keys():
                        layout["N"+str(specific_N)][condition][doses[y]]=[]
                    # Add ALL wells for this dose, not just wells[y]
                    for well_idx, well in enumerate(wells):
                        if well_idx < len(plate_groups):
                            layout["N"+str(specific_N)][condition][doses[y]].append((well, plate_groups[well_idx]))
    return scope, layout, conditions, ctrl_positions, excluded_positions, per_well_datapoints

def get_features_EDDU_CX5(raw_df):
    return raw_df.iloc[:,raw_df.columns.str.find("Replicate").argmax()+1:-1].columns

def get_features_EDDU_metaxpress(raw_df):
    # Check if this is CSV format by looking for "Well" in the data
    # CSV format has column headers in row 6 (0-indexed), Excel format has null rows with features
    try:
        # Try CSV format first: look for row with "Well" in first column
        well_row_idx = None
        for i in range(min(10, len(raw_df))):  # Check first 10 rows
            if str(raw_df.iloc[i, 0]).strip().lower() == 'well':
                well_row_idx = i
                break

        if well_row_idx is not None:
            # CSV format: features are in the same row as "Well", starting from column 1
            feature_row = raw_df.iloc[well_row_idx]
            features = [str(col).strip() for col in feature_row[1:] if pd.notna(col) and str(col).strip() != '']
        else:
            # Original Excel format: look for null rows with features
            feature_rows = raw_df[pd.isnull(raw_df.iloc[:,0])].iloc[0].tolist()[2:]
            features = [x for x in feature_rows if not pd.isnull(x)]
    except (IndexError, KeyError):
        # Fallback: try to extract from column names if available
        features = [col for col in raw_df.columns[1:] if col and str(col) != 'nan']

    return features

def create_well_dict(raw_df, wells=None,scope=None):
    if wells == None:
        rows=[string.ascii_uppercase[i] for i in range(8)]
        cols=[i+1 for i in range(12)]
        wells = []
        for row in rows:
            for col in cols:
                wells.append(str(row)+str(col).zfill(2))
    features = get_features(raw_df,scope=scope)
    return {well:{feature:None for feature in features} for well in wells}

def add_well_to_well_dict(wells,well_dict, raw_df):
    features = get_features(raw_df).columns
    for well in wells:
        well_dict[well]={feature:None for feature in features}
    return well_dict

def create_plates_dict(raw_df,scope=None):
    if scope == "EDDU_CX5":
        return create_plates_dict_EDDU_CX5(raw_df)
    if scope == "EDDU_metaxpress":
        return create_plates_dict_EDDU_metaxpress(raw_df)
    else:
        print("microscope "+str(scope)+" not known. Exiting")
        sys.exit()

def create_plates_dict_EDDU_metaxpress(raw_df):
    # Prioritize "Plate ID" over "Plate Name" for consistency with fill function
    plate_id_rows = raw_df[(raw_df == 'Plate ID').any(axis=1)]
    plate_name_rows = raw_df[(raw_df == 'Plate Name').any(axis=1)]

    if not plate_id_rows.empty:
        plate_names = plate_id_rows.iloc[:,1].tolist()
    elif not plate_name_rows.empty:
        plate_names = plate_name_rows.iloc[:,1].tolist()
    else:
        # Fallback: use a default plate name
        plate_names = ['default_plate']

    plate_dict = {str(plate_id):create_well_dict(raw_df,scope="EDDU_metaxpress") for plate_id in plate_names}
    return plate_dict

def create_plates_dict_EDDU_CX5(raw_df):
    plate_ids = raw_df['UniquePlateId'].tolist()
    plate_dict = {plate_id:create_well_dict(raw_df,scope="EDDU_CX5") for plate_id in plate_ids}
    return plate_dict

def indices_to_well(row,col,dim):
    rMax, cMax = dim[0],dim[1]
    col += 1
    total = row*cMax+col
    i=0
    i+=1
    offset = int((total-1)/(cMax)*i)
    rowIndex = str(chr(65 + offset))
    colIndex = str(total - (offset * (cMax)*i)).zfill(2)
    return rowIndex + str(colIndex)

def row_col_to_well(row,col):
    row_letter=chr(row+64)
    number=str(col).zfill(2)
    return row_letter+number

def well_to_num(well,dim):
    rMax, cMax = dim[0],dim[1]
    (rowIndex, colIndex) = (0,0)
    for i in range(0, len(well)):
        (left, right) = (well[:i], well[i:i+1])
        if right.isdigit():
            (rowIndex, colIndex) = (left, well[i:])
            break
    ascii_value = ord(rowIndex) - 65
    return ascii_value*(rMax+(4*i)) + int(colIndex)

def fill_plates_dict(raw_df,plates_dict,scope=None):
    features = get_features(raw_df,scope=scope)
    if scope == "EDDU_CX5":
        return fill_plates_dict_EDDU_CX5(raw_df,plates_dict,features)
    if scope == "EDDU_metaxpress":
        return fill_plates_dict_EDDU_metaxpress(raw_df,plates_dict,features)
    else:
        print("microscope "+str(scope)+" not known. Exiting")
        sys.exit()

def fill_plates_dict_EDDU_CX5(raw_df,plates_dict,features):
    for index,row in raw_df.iterrows():
        well = row_col_to_well(row[2],row[3])
        for feature in features:
            plates_dict[row[1]][well][feature]=row[feature]
    return plates_dict

def fill_plates_dict_EDDU_metaxpress(raw_df,plates_dict,features):
    # Check if this is CSV format (has "Well" in data rows)
    well_row_idx = None
    for i in range(min(10, len(raw_df))):
        if str(raw_df.iloc[i, 0]).strip().lower() == 'well':
            well_row_idx = i
            break

    if well_row_idx is not None:
        # CSV format: data starts after the "Well" header row
        # Get plate name from earlier rows
        plate_name = None
        for i in range(well_row_idx):
            if str(raw_df.iloc[i, 0]).strip() == "Plate ID":
                plate_name = str(raw_df.iloc[i, 1]).strip()
                break

        # Process data rows (starting after the header row)
        for i in range(well_row_idx + 1, len(raw_df)):
            row = raw_df.iloc[i]
            well_id = str(row.iloc[0]).strip()
            if well_id and well_id != 'nan' and well_id != '':
                # Map features by position (feature[j] corresponds to column[j+1])
                for j, feature in enumerate(features):
                    if j + 1 < len(row):  # Make sure we don't go out of bounds
                        plates_dict[plate_name][well_id][feature] = row.iloc[j + 1]
    else:
        # Original Excel format
        df_col_names = raw_df.set_axis(["Well","Laser Focus"]+features, axis=1)
        plate_name=None
        start_collect=False
        for index,row in df_col_names.iterrows():
            if row[0] == "Barcode":
                start_collect=False
            if start_collect:
                for feature in features:
                    plates_dict[plate_name][row[0]][feature]=row[feature]
            if row[0] == "Plate Name":
                plate_name=row[1]
            elif pd.isnull(row[0]):
                start_collect=True

    return plates_dict

def average_plates(plates,raw_df,scope=None):
    average_plate=create_well_dict(raw_df,scope=scope)
    features = get_features(raw_df)
    for well in average_plate.keys():
        for feature in features:
            average_value=0
            for plate in plates:
                average_value+=plate[well][feature]
            average_value=average_value/len(plates)
            average_plate[well][feature]=average_value
    return average_plate

def average_plates_all_replicates(plate_groups,plates_dict,raw_df):
    averaged_plates_dict = {replicate:None for replicate in plate_groups.keys()}
    for replicate in plate_groups.keys():
        one_replicate=average_plates_one_replicate(plate_groups[replicate],plates_dict,raw_df)
        averaged_plates_dict[replicate]=one_replicate
    return averaged_plates_dict

def average_plates_duplicate_rows(plate_groups,plates_dict,raw_df,wells_to_average=None,scope=None):
    features = get_features(raw_df,scope=scope)
    averaged_plates_dict={}
    for plate_name,plate in plates_dict.items():
        average_plate=create_well_dict(raw_df,scope=scope,wells=wells_to_average)
        for well in wells_to_average:
            average_plate=average_rows(plate,average_plate,well,features)
        averaged_plates_dict[plate_name]=average_plate
    return plates_dict

def average_rows(plate_dict,average_plate,well,features,num_rows_average=2):
    original_well=well
    wells_to_average = []
    wells_to_average.append(well)
    for i in range(num_rows_average-1):
        well_next_row = get_well_next_row(well)
        wells_to_average.append(well_next_row)
        well_next_row = well
    for feature in features:
        average_value=0
        for well in wells_to_average:
            average_value+=plate_dict[well][feature]
        average_value=average_value/num_rows_average
        average_plate[original_well][feature]=average_value
    return average_plate

def get_well_next_row(well):
    return chr(ord(well[0])+1)+well[1:]


def average_plates(plates,raw_df,scope=None):
    average_plate=create_well_dict(raw_df,scope=scope)
    features = get_features(raw_df)
    for well in average_plate.keys():
        for feature in features:
            average_value=0
            for plate in plates:
                average_value+=plate[well][feature]
            average_value=average_value/len(plates)
            average_plate[well][feature]=average_value
    return average_plate


def average_plates_one_replicate(averaged_plates_names_dict,plates_dict,raw_df):
    averaged_plates_dict = {plate_average_name:None for plate_average_name in averaged_plates_names_dict.keys()}
    for plate_average_name in averaged_plates_dict.keys():
        plates_to_average = averaged_plates_names_dict[plate_average_name]
        plates_to_average = [plates_dict[plate_name] for plate_name in plates_to_average]
        averaged_plates_dict[plate_average_name]=average_plates(plates_to_average,raw_df)
    return averaged_plates_dict

def filter_excluded_wells_from_data(data_dict, excluded_positions, current_replicate=None):
    """
    Filter out excluded wells from experimental data structures.

    Args:
        data_dict: Dictionary containing experimental data
        excluded_positions: Dictionary with excluded wells per replicate: {"N1": [(well, plate_group), ...], "N2": [...]}
        current_replicate: Current biological replicate context (e.g., 'N1')

    Returns:
        Filtered data dictionary with excluded wells removed
    """
    if excluded_positions is None or not excluded_positions:
        return data_dict

    # Get excluded wells for current replicate
    excluded_wells_for_replicate = []
    if current_replicate and current_replicate in excluded_positions:
        excluded_wells_for_replicate = [well for well, plate_group in excluded_positions[current_replicate]]

    # Convert to set for faster lookup
    excluded_set = set(str(well).upper() for well in excluded_wells_for_replicate)

    if not excluded_set:
        return data_dict

    # Filter the data structure
    if isinstance(data_dict, dict):
        filtered_dict = {}
        for key, value in data_dict.items():
            if isinstance(value, dict):
                # Check if this looks like a well ID (e.g., 'A01', 'B12')
                if isinstance(key, str) and len(key) == 3 and key[0].isalpha() and key[1:].isdigit():
                    # This is a well-level dictionary
                    if key.upper() not in excluded_set:
                        filtered_dict[key] = filter_excluded_wells_from_data(value, excluded_positions, current_replicate)
                else:
                    # Recursively filter nested dictionaries
                    filtered_dict[key] = filter_excluded_wells_from_data(value, excluded_positions, current_replicate)
            elif isinstance(value, list):
                # Filter lists that might contain well tuples
                filtered_list = []
                for item in value:
                    if isinstance(item, tuple) and len(item) >= 1:
                        # Check if first element looks like a well ID
                        well_id = str(item[0]).upper()
                        if well_id not in excluded_set:
                            filtered_list.append(item)
                    else:
                        filtered_list.append(item)
                filtered_dict[key] = filtered_list
            else:
                filtered_dict[key] = value
        return filtered_dict
    else:
        return data_dict


def filter_excluded_wells(data_dict, excluded_wells):
    """
    Filter out excluded wells from experimental data structures.

    Args:
        data_dict: Dictionary containing experimental data (plates_dict, experiment_dict_locations, etc.)
        excluded_wells: List of well IDs to exclude (e.g., ['A01', 'B03', 'C12'])

    Returns:
        Filtered data dictionary with excluded wells removed
    """
    if excluded_wells is None or len(excluded_wells) == 0:
        return data_dict

    # Convert excluded wells to set for faster lookup
    excluded_set = set(str(well).upper() for well in excluded_wells)

    # Filter plates_dict if it exists
    if isinstance(data_dict, dict):
        filtered_dict = {}
        for key, value in data_dict.items():
            if isinstance(value, dict):
                # Check if this looks like a well ID (e.g., 'A01', 'B12')
                if isinstance(key, str) and len(key) == 3 and key[0].isalpha() and key[1:].isdigit():
                    # This is a well-level dictionary
                    if key.upper() not in excluded_set:
                        filtered_dict[key] = filter_excluded_wells(value, excluded_wells)
                else:
                    # Recursively filter nested dictionaries
                    filtered_dict[key] = filter_excluded_wells(value, excluded_wells)
            elif isinstance(value, list):
                # Filter lists that might contain well tuples
                filtered_list = []
                for item in value:
                    if isinstance(item, tuple) and len(item) >= 1:
                        # Check if first element looks like a well ID
                        well_id = str(item[0]).upper()
                        if well_id not in excluded_set:
                            filtered_list.append(item)
                    else:
                        filtered_list.append(item)
                filtered_dict[key] = filtered_list
            else:
                filtered_dict[key] = value
        return filtered_dict
    else:
        return data_dict


def load_plate_groups(config_path):
    xls = pd.ExcelFile(config_path)
    df = pd.read_excel(xls, 'plate_groups',index_col=0,header=None)
    replicates = df.index.tolist()[1:]
    groups = [str(group) for group in df.columns.tolist()]
    plate_groups = {replicate:{group:None for group in groups} for replicate in replicates}
    for group in groups:
        for replicate in replicates:
            #well_replicates = df.filter(like=group).loc[replicate].tolist()[0]
            plate_groups[replicate][group]=df.loc[replicate][int(group)]
    return plate_groups

def normalize_plate(plate,reference_wells,raw_df,ctrl_avg_name):
    features = get_features(raw_df)
    normalized_plate=create_well_dict(raw_df)
    normalized_plate = add_well_to_well_dict([ctrl_avg_name],normalized_plate, raw_df)
    for feature in features:
        control_values = [plate[well][feature] for well in reference_wells]
        control_avg = np.mean(np.array(control_values))
        normalized_plate[ctrl_avg_name][feature]=control_avg
        for well in normalized_plate.keys():
            if well not in ctrl_avg_name:
                try:
                    normalized_plate[well][feature] = plate[well][feature]/control_avg
                except:
                    normalized_plate[well][feature] = plate[well][feature]
    return normalized_plate


def normalize_all_plates(plates_dict,reference_wells,raw_df,ctrl_avg_name):
    normalized_plates={replicate:{} for replicate in plates_dict.keys()}
    for replicate, condition_plates in plates_dict.items():
        for condition, plate in condition_plates.items():
            normalized_plates[replicate][condition]=normalize_plate(plate,reference_wells,raw_df,ctrl_avg_name)
    return normalized_plates

def create_table_for_feature(feature,experiment_dict_values):
    conditions = list(experiment_dict_values.keys())

    # Create hierarchical column structure: (condition, replicate)
    col_tuples = []
    values = []

    for condition in conditions:
        # Get replicates for this specific condition (they may differ in per-well mode)
        condition_replicates = list(experiment_dict_values[condition].keys())

        for replicate in condition_replicates:
            # Get the value from any available dose for this condition-replicate
            for dose in experiment_dict_values[condition][replicate].keys():
                try:
                    feature_data = experiment_dict_values[condition][replicate][dose][feature]
                    if isinstance(feature_data, dict):
                        # Handle both averaged and per-well dictionary formats
                        if "averaged" in feature_data:
                            # Averaged mode - single value
                            col_tuples.append((condition, replicate))
                            values.append(feature_data["averaged"])
                        else:
                            # Per-well mode - multiple values (each well becomes a separate column)
                            for well_id, value in feature_data.items():
                                col_tuples.append((condition, replicate))
                                values.append(value)
                    else:
                        # Fallback for old format (shouldn't happen now)
                        col_tuples.append((condition, replicate))
                        values.append(feature_data)
                    break  # Use the first available dose
                except:
                    continue

    # Create DataFrame in GraphPad Prism format: N as y-axis (rows), conditions as x-axis (columns)
    # Group values by condition
    condition_data = {}
    for i, (condition, replicate) in enumerate(col_tuples):
        if condition not in condition_data:
            condition_data[condition] = []
        condition_data[condition].append(values[i])

    # Create DataFrame with conditions as columns and N as rows
    max_n = max(len(vals) for vals in condition_data.values())
    data_matrix = []
    for n in range(max_n):
        row = []
        for condition in sorted(condition_data.keys()):
            if n < len(condition_data[condition]):
                row.append(condition_data[condition][n])
            else:
                row.append(None)  # Fill missing values with None
        data_matrix.append(row)

    feature_table = pd.DataFrame(data_matrix,
                               columns=sorted(condition_data.keys()),
                               index=[f'N{i+1}' for i in range(max_n)])

    return feature_table

def create_table_for_feature_per_well(feature,experiment_dict_values):
    """Create feature table with individual wells as columns."""
    conditions = list(experiment_dict_values.keys())
    replicates = list(list(experiment_dict_values.values())[0].keys())

    col_names = []
    values = []

    for condition in conditions:
        for replicate in replicates:
            # Get the value from any available dose for this condition-replicate
            for dose in experiment_dict_values[condition][replicate].keys():
                feature_data = experiment_dict_values[condition][replicate][dose][feature]
                if isinstance(feature_data, dict):  # Per-well mode
                    for well_id, value in feature_data.items():
                        col_names.append(f"{condition}_{replicate}_{well_id}")
                        values.append(value)
                else:  # Regular averaged mode (fallback)
                    col_names.append(f"{condition}_{replicate}")
                    values.append(feature_data)
                break  # Use first available dose

    return pd.DataFrame([values], columns=col_names)



def create_all_feature_tables(experiment_dict_values,features,per_well_datapoints=False):
    """Create feature tables. Both modes now use the same function since data is in dict format."""
    feature_tables={feature:None for feature in features}
    for feature in features:
        feature_tables[feature]=create_table_for_feature(feature,experiment_dict_values)
    return feature_tables

def feature_tables_to_excel(feature_tables,outpath):
    def remove_inval_chars(name):
        inval_chars=['[',']',':','*','?','/','\\']
        for char in inval_chars:
            name=name.replace(char,"")
        # Modern Excel supports up to 255 characters for sheet names
        return name[:255]
    with pd.ExcelWriter(outpath, engine='openpyxl') as writer:
        for feature in feature_tables.keys():
            table = feature_tables[feature]
            if table is not None:
                # Write with merge_cells=False to avoid Excel merge conflicts
                table.to_excel(writer, sheet_name=remove_inval_chars(feature), merge_cells=False)

def create_duplicate_wells():
    rows=[string.ascii_uppercase[i] for i in range(0,8,2)]
    cols=[i+1 for i in range(12)]
    wells = []
    for row in rows:
        for col in cols:
            wells.append(str(row)+str(col).zfill(2))
    return wells

def make_experiment_dict_locations(plate_groups,plate_layout,conditions):
    experiment_dict={condition:{} for condition in conditions}
    #experiment_dict={replicate:{} for replicate in plate_layout.keys()}
    for replicate, conditions in plate_layout.items():
        for condition,doses in conditions.items():
            experiment_dict[condition][replicate] = {dose:locations for dose,locations in doses.items()}
    return experiment_dict

def make_experiment_dict_values(plates,experiment_dict_locations,features,plate_groups,per_well_datapoints=False):
    if per_well_datapoints:
        # In per-well mode, restructure data so each well becomes a separate "replicate"
        experiment_dict_values = {}

        for condition, replicates in experiment_dict_locations.items():
            experiment_dict_values[condition] = {}
            well_counter = 1  # Counter for creating unique replicate names

            for replicate, doses in replicates.items():
                for dose, locations in doses.items():
                    # Each well becomes a separate "replicate"
                    for location in locations:
                        well, plate_group = location
                        plate_name = str(plate_groups[replicate][str(plate_group)])

                        # Create unique replicate name for this well
                        well_replicate_name = f"N{well_counter}"
                        well_counter += 1

                        # Get individual well values
                        feature_value_dict = {}
                        for feature in features:
                            value = plates[plate_name][well][feature]
                            try:
                                well_value = float(value) if value is not None else 0.0
                            except (ValueError, TypeError):
                                well_value = 0.0
                            # Store as single-well dictionary to maintain format consistency
                            well_id = f"{well}_P{plate_group}"
                            feature_value_dict[feature] = {well_id: well_value}

                        # Store this well as its own replicate
                        experiment_dict_values[condition][well_replicate_name] = {dose: feature_value_dict}
    else:
        # Original averaging mode
        experiment_dict_values = copy.deepcopy(experiment_dict_locations)
        for condition, replicates in experiment_dict_locations.items():
            for replicate, doses in replicates.items():
                for dose, locations in doses.items():
                    feature_value_dict = {feature: average_wells(locations, replicate, feature, plates, plate_groups) for feature in features}
                    experiment_dict_values[condition][replicate][dose] = feature_value_dict

    return experiment_dict_values

def average_wells(locations,replicate,feature,plates,plate_groups):
    """Return dict with averaged value to match per-well format."""
    if len(locations) == 0:
        return {"averaged": 0.0}

    average=0
    for location in locations:
        average+=location_to_value(location,replicate,feature,plates,plate_groups)
    averaged_value = average/float(len(locations))
    # Return as dictionary to match per-well format
    return {"averaged": averaged_value}

def individual_wells(locations,replicate,feature,plates,plate_groups):
    """Return dict of individual well values instead of averaging."""
    well_values = {}
    for location in locations:
        well, plate_group = location
        plate_name = str(plate_groups[replicate][str(plate_group)])
        value = plates[plate_name][well][feature]
        # Create unique well identifier including plate group
        well_id = f"{well}_P{plate_group}"
        try:
            well_values[well_id] = float(value) if value is not None else 0.0
        except (ValueError, TypeError):
            well_values[well_id] = 0.0
    return well_values

def location_to_value(location,replicate,feature,plates,plate_groups):
    well, plate_group = location
    plate_name = str(plate_groups[replicate][str(plate_group)])  # Ensure string conversion
    value = plates[plate_name][well][feature]
    # Convert to float for numerical operations
    try:
        return float(value)
    except (ValueError, TypeError):
        return 0.0  # Default for non-numeric values

def normalize_experiment(experiment_dict_values,ctrl_positions,features,plates,plate_groups):
    experiment_dict_values_normalized=copy.deepcopy(experiment_dict_values)

    # In per-well mode, use the original replicate (N1) for control positions
    # since all per-well replicates (N1, N2, N3...) come from the same original biological replicate
    original_replicate = list(ctrl_positions.keys())[0] if ctrl_positions else None

    for condition,replicates in experiment_dict_values.items():
        for replicate, doses in replicates.items():
            # Use original replicate for control positions (handles per-well mode)
            ctrl_replicate = replicate if replicate in ctrl_positions else original_replicate
            if ctrl_replicate and ctrl_replicate in ctrl_positions:
                ctrl_positions_replicate = ctrl_positions[ctrl_replicate]
                feature_control_vals={feature:average_wells(ctrl_positions_replicate,ctrl_replicate,feature,plates,plate_groups) for feature in features}

                for dose,values in doses.items():
                    feature_value_dict = {}
                    for feature in features:
                        ctrl_dict = feature_control_vals[feature]
                        ctrl_value = ctrl_dict["averaged"] if isinstance(ctrl_dict, dict) else ctrl_dict
                        if ctrl_value == 0:
                            ctrl_value = 1

                        condition_value_dict = experiment_dict_values[condition][replicate][dose][feature]
                        if isinstance(condition_value_dict, dict):
                            # Handle dictionary format (both averaged and per-well)
                            normalized_dict = {}
                            for key, value in condition_value_dict.items():
                                normalized_dict[key] = value / ctrl_value
                            feature_value_dict[feature] = normalized_dict
                        else:
                            # Fallback for old format
                            feature_value_dict[feature] = condition_value_dict / ctrl_value

                    experiment_dict_values_normalized[condition][replicate][dose] = feature_value_dict
            else:
                # No normalization if no control positions available
                experiment_dict_values_normalized[condition][replicate] = experiment_dict_values[condition][replicate]

    return experiment_dict_values_normalized

def write_values_heat_map(plates_dict,features,outpath):
    workbook = xlsxwriter.Workbook(outpath)
    with pd.ExcelWriter(outpath) as writer:
        for feature in features:
            sheet_rows=[]
            for plate in plates_dict.keys():
                sheet_rows.append([plate])
                values=[]
                for r in range(65,65+8,1):
                    values.append([])
                    row=[]
                    for c in range(12):
                        well=chr(r)+str(c+1).zfill(2)
                        row.append(plates_dict[plate][well][feature])
                    sheet_rows.append(row)
            sheet_rows.append([""])
            pd.DataFrame(sheet_rows).to_excel(writer, sheet_name=remove_inval_chars(feature[:31]))

def create_reference_wells():
    rows=[string.ascii_uppercase[i] for i in range(8)]
    cols=[i+1 for i in range(6,12)]
    wells = []
    for row in rows:
        for col in cols:
            wells.append((str(row)+str(col).zfill(2),2))
    return wells

def remove_inval_chars(name):
    inval_chars=['[',']',':','*','?','/','\\']
    for char in inval_chars:
        name=name.replace(char,"")
    return name

def run_experimental_analysis(
    results_path: str = "mx_results.xlsx",
    config_file: str = "./config.xlsx",
    compiled_results_path: str = "./compiled_results_normalized.xlsx",
    heatmap_path: str = "./heatmaps.xlsx"
):
    """
    Run complete experimental analysis pipeline for CX5/MetaXpress data.

    DEPRECATED: This function is maintained for backward compatibility.
    New code should use the unified analysis engine:

    from openhcs.processing.backends.experimental_analysis import ExperimentalAnalysisEngine
    from openhcs.core.config import ExperimentalAnalysisConfig

    config = ExperimentalAnalysisConfig()
    engine = ExperimentalAnalysisEngine(config)
    engine.run_analysis(results_path, config_file, compiled_results_path, heatmap_path)

    Args:
        results_path: Path to results Excel file (CX5 or MetaXpress format)
        config_file: Path to experimental configuration Excel file
        compiled_results_path: Output path for compiled results
        heatmap_path: Output path for heatmap visualization
    """
    import warnings
    warnings.warn(
        "run_experimental_analysis is deprecated. Use ExperimentalAnalysisEngine instead.",
        DeprecationWarning,
        stacklevel=2
    )
    # Parse experimental configuration
    scope, plate_layout, conditions, ctrl_positions, excluded_positions, per_well_datapoints = read_plate_layout(config_file)
    plate_groups = load_plate_groups(config_file)
    experiment_dict_locations = make_experiment_dict_locations(plate_groups, plate_layout, conditions)

    # Load and process results data
    df = read_results(results_path, scope=scope)
    features = get_features(df, scope=scope)
    well_dict = create_well_dict(df, scope=scope)
    plates_dict = create_plates_dict(df, scope=scope)
    plates_dict = fill_plates_dict(df, plates_dict, scope=scope)

    # Apply wells exclusion if specified
    if excluded_positions is not None:
        total_excluded = sum(len(wells) for wells in excluded_positions.values())
        if total_excluded > 0:
            print(f"Excluding {total_excluded} wells from analysis across replicates:")
            for replicate, wells_list in excluded_positions.items():
                if wells_list:
                    wells_only = [well for well, plate_group in wells_list]
                    print(f"  {replicate}: {wells_only}")

            # Filter experiment_dict_locations by replicate
            for condition in experiment_dict_locations:
                for replicate in experiment_dict_locations[condition]:
                    if replicate in excluded_positions:
                        excluded_wells_for_replicate = [well for well, plate_group in excluded_positions[replicate]]
                        excluded_set = set(str(well).upper() for well in excluded_wells_for_replicate)

                        # Filter each dose's well list
                        for dose in experiment_dict_locations[condition][replicate]:
                            filtered_wells = []
                            for well_tuple in experiment_dict_locations[condition][replicate][dose]:
                                well_id = str(well_tuple[0]).upper()
                                if well_id not in excluded_set:
                                    filtered_wells.append(well_tuple)
                            experiment_dict_locations[condition][replicate][dose] = filtered_wells

    # Create experiment data structure
    experiment_dict_values_raw = make_experiment_dict_values(plates_dict, experiment_dict_locations, features, plate_groups, per_well_datapoints)

    # Generate raw (non-normalized) results
    feature_tables_raw = create_all_feature_tables(experiment_dict_values_raw, features, per_well_datapoints)
    raw_results_path = compiled_results_path.replace('.xlsx', '_raw.xlsx')
    feature_tables_to_excel(feature_tables_raw, raw_results_path)

    # Apply normalization if controls are defined
    if ctrl_positions is not None:
        experiment_dict_values_normalized = normalize_experiment(experiment_dict_values_raw, ctrl_positions, features, plates_dict, plate_groups)
        # Generate normalized results
        feature_tables_normalized = create_all_feature_tables(experiment_dict_values_normalized, features, per_well_datapoints)
        feature_tables_to_excel(feature_tables_normalized, compiled_results_path)
        # Return normalized for backward compatibility
        experiment_dict_values = experiment_dict_values_normalized
        feature_tables = feature_tables_normalized
    else:
        # No normalization, use raw results
        experiment_dict_values = experiment_dict_values_raw
        feature_tables = feature_tables_raw

    # Generate heatmaps
    write_values_heat_map(plates_dict, features, heatmap_path)

    return experiment_dict_values, feature_tables


# Example usage - can be run as script
if __name__ == "__main__":
    rows = [string.ascii_uppercase[i] for i in range(8)]
    cols = [i+1 for i in range(12)]
    conditions = []
    for row in rows:
        for col in cols:
            conditions.append(str(row)+str(col).zfill(2))

    # Run with default paths
    experiment_dict_values, feature_tables = run_experimental_analysis()
