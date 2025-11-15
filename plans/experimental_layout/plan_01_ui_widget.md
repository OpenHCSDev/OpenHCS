# plan_01_ui_widget.md
## Component: Experimental Layout Configuration UI Widget

### Objective
Create a PyQt6-based UI widget for defining complex experimental designs with well-to-condition mapping, biological replicates, and dose-response curves. The widget should provide table-based editing for conditions, doses, wells, plate groups, and controls, with real-time validation.

### Plan

#### 1. Data Model (Dataclass-based)
Create `openhcs/formats/experimental_layout_config.py`:
- `ExperimentalLayoutConfig` dataclass with fields:
  - `n_replicates: int` (default 3)
  - `scope: str` (enum: EDDU_CX5, EDDU_metaxpress)
  - `conditions: List[ConditionConfig]`
  - `plate_groups: Dict[str, str]` (replicate_name → plate_id)
  - `controls: Optional[ControlConfig]`

- `ConditionConfig` dataclass:
  - `name: str`
  - `doses: List[str]` (e.g., ["0", "10", "50", "100"])
  - `wells_by_replicate: Dict[int, List[str]]` (replicate_num → well_ids)
  - `plate_groups_by_replicate: Dict[int, List[str]]` (replicate_num → plate_ids)
  - `technical_replicates: Dict[int, int]` (replicate_num → count)

- `ControlConfig` dataclass:
  - `well_ids: List[str]`
  - `plate_groups: List[str]`
  - `group_assignments: Dict[str, int]` (well_id → replicate_num)

#### 2. Validation Service
Create `openhcs/formats/experimental_layout_validator.py`:
- `ExperimentalLayoutValidator` class with methods:
  - `validate_dose_well_count()` - doses must match well count
  - `validate_all_replicates_defined()` - all Wells1..WellsN must exist
  - `validate_plate_groups_match()` - plate groups count must match wells count
  - `validate_well_format()` - well IDs must be valid (A01, B02, etc.)
  - `validate_scope()` - scope must be in allowed list
  - Returns `ValidationResult` with errors/warnings list

#### 3. PyQt6 Widget (`ExperimentalLayoutWidget`)
Create `openhcs/pyqt_gui/widgets/experimental_layout_widget.py`:

**Structure:**
- Main container: `QWidget` with `QVBoxLayout`
- Section 1: Global Parameters (using `ParameterFormManager`)
  - N (spinbox), Scope (combobox)
- Section 2: Conditions Table (`QTableWidget`)
  - Columns: Condition | Dose Series | Wells1 | Wells2 | Wells3 | Plate Groups | Tech Reps
  - Add/Remove Condition buttons
  - Inline editing via `setCellWidget()` with `QLineEdit`, `QComboBox`
- Section 3: Plate Groups Mapping Table
  - Columns: Replicate | Physical Plate ID
  - Add/Remove buttons
- Section 4: Controls Definition (collapsible)
  - Wells list, Plate Groups, Group assignments
- Section 5: Validation Panel
  - Shows errors/warnings in real-time
  - Color-coded: red (error), yellow (warning), green (valid)

**Key Methods:**
- `__init__(config: ExperimentalLayoutConfig, parent=None)`
- `_create_global_params_section()` - uses `ParameterFormManager`
- `_create_conditions_table()` - QTableWidget with dynamic columns
- `_create_plate_groups_table()` - simple 2-column table
- `_create_controls_section()` - collapsible group
- `_create_validation_panel()` - displays validation results
- `_populate_conditions_table()` - load data into table
- `_populate_plate_groups_table()` - load data into table
- `_on_cell_changed(row, col)` - update model, validate
- `_on_add_condition()` - insert new row
- `_on_remove_condition()` - delete row
- `_on_add_plate_group()` - insert new row
- `_on_remove_plate_group()` - delete row
- `get_config() -> ExperimentalLayoutConfig` - extract from UI
- `set_config(config: ExperimentalLayoutConfig)` - populate UI
- `validate() -> ValidationResult` - run validator

**Signals:**
- `config_changed(ExperimentalLayoutConfig)` - emitted on any change
- `validation_changed(ValidationResult)` - emitted after validation

#### 4. Excel I/O Integration
Extend `openhcs/formats/experimental_analysis.py`:
- `load_experimental_layout(excel_path: str) -> ExperimentalLayoutConfig`
- `save_experimental_layout(config: ExperimentalLayoutConfig, excel_path: str)`
- Use existing `read_plate_layout()` and `load_plate_groups()` functions

#### 5. Integration Points
- Add to `PlateManagerWidget` as a tab or dialog
- Add menu item: Tools → Experimental Layout Configuration
- Support drag-drop of Excel files to load config
- Export button to save config back to Excel

### Findings

**PyQt6 QTableWidget Capabilities** (from Context7 docs):
- `setColumnCount(int)` / `setRowCount(int)` - set dimensions
- `setHorizontalHeaderLabels(List[str])` - set column headers
- `insertRow(int)` / `removeRow(int)` - dynamic row management
- `setCellWidget(row, col, QWidget)` - place widgets in cells (QLineEdit, QComboBox, etc.)
- `cellChanged(int, int)` signal - track edits
- `setEditTriggers()` - control when cells become editable
- `setSelectionBehavior()` - row/column/cell selection modes
- `setSortingEnabled(bool)` - enable sorting
- `horizontalHeader().setSectionResizeMode()` - column resizing

**OpenHCS Patterns to Reuse:**
- `ParameterFormManager` (lines 128-300 in parameter_form_manager.py) - for global params
- `WIDGET_UPDATE_DISPATCH` / `WIDGET_GET_DISPATCH` (lines 19-35) - for reading/writing cell values
- `ImageBrowserWidget` pattern (image_browser.py lines 210-230) - dynamic column generation
- Dataclass-based config with lazy evaluation
- Validation service pattern from existing validators

**Excel Format** (from documentation):
- Sheet: `drug_curve_map` with rows: N, Scope, Controls, Condition, Dose, Wells1-N, Plate Group
- Sheet: `plate_groups` with columns: Replicate, Physical Plate ID
- Existing `read_plate_layout()` already parses this format

### Implementation Draft

(To be written after smell loop approval)

### Next Steps
1. Smell loop review of this plan
2. Implement dataclass models
3. Implement validator
4. Implement PyQt6 widget
5. Integrate with PlateManagerWidget
6. Add Excel I/O
7. Write tests

