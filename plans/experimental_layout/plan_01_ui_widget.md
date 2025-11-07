# plan_01_ui_widget.md
## Component: Experimental Layout Configuration UI Widget

### Objective
Create a PyQt6-based UI widget for defining complex experimental designs with well-to-condition mapping, biological replicates, and dose-response curves. The widget uses OpenHCS architectural patterns including registry-based validation, frozen dataclass configuration, service layer separation, and functional dispatch for UI operations.

### Architecture Overview

This implementation follows OpenHCS patterns:
- **Registry Pattern** for validators (AutoRegisterMeta)
- **Frozen Dataclasses** for immutable configuration
- **Service Layer** separating business logic from UI
- **Functional Dispatch** for widget operations (no if/elif chains)
- **Fail-Loud** validation (no defensive programming)
- **Lazy Config Integration** for dual-axis resolution

### Plan

#### 1. Data Model (Following OpenHCS Frozen Dataclass Pattern)

Create `openhcs/formats/experimental_layout_config.py`:

##### Core Configuration Classes

```python
from dataclasses import dataclass
from typing import List, Dict, Optional
from enum import Enum

class MicroscopeScope(Enum):
    """Microscope formats - matches existing experimental_analysis system."""
    EDDU_CX5 = "EDDU_CX5"
    EDDU_METAXPRESS = "EDDU_metaxpress"

@dataclass(frozen=True)
class WellsRow:
    """Represents one 'WellsN' row in Excel config.

    Multiple WellsRow for same replicate = technical replicates.
    Matches Excel structure: Wells1 / Plate Group pattern.
    """
    wells: tuple[str, ...]  # Immutable: ("A01", "A02", "A03", "A04")
    plate_groups: tuple[str, ...]  # Maps each well to plate group: ("1", "1", "1", "1")

    def __post_init__(self):
        """Validate dose-well-plate alignment."""
        if len(self.wells) != len(self.plate_groups):
            raise ValueError(f"Wells count {len(self.wells)} != plate_groups count {len(self.plate_groups)}")

@dataclass(frozen=True)
class ConditionConfig:
    """Experimental condition configuration.

    Represents one 'Condition' block from Excel config.
    Technical replicates = multiple WellsRow in wells_by_replicate[replicate_num].
    """
    name: str
    doses: tuple[str, ...]  # Immutable doses: ("0", "10", "50", "100")
    wells_by_replicate: Dict[int, tuple[WellsRow, ...]]  # replicate_num → tuple of WellsRows

    def __post_init__(self):
        """Validate dose-well alignment for all replicates."""
        for replicate_num, wells_rows in self.wells_by_replicate.items():
            for wells_row in wells_rows:
                if len(self.doses) != len(wells_row.wells):
                    raise ValueError(
                        f"Condition '{self.name}' N{replicate_num}: "
                        f"{len(self.doses)} doses != {len(wells_row.wells)} wells"
                    )

@dataclass(frozen=True)
class ControlConfig:
    """Control wells configuration - maps to Excel 'Controls' block."""
    well_ids: tuple[str, ...]  # ("A01", "B01", "C01", ...)
    plate_groups: tuple[str, ...]  # ("1", "1", "1", ...)
    group_assignments: Dict[str, int]  # well_id → replicate_num (1, 2, 3, ...)

@dataclass(frozen=True)
class ExcludedWellsConfig:
    """Excluded wells configuration - maps to Excel 'Exclude Wells' block."""
    well_ids: tuple[str, ...]
    plate_groups: tuple[str, ...]
    group_assignments: Dict[str, int]  # well_id → replicate_num

@dataclass(frozen=True)
class ExperimentalLayoutConfig:
    """Root configuration for experimental layout.

    Frozen dataclass following OpenHCS immutable config pattern.
    Integrates with existing experimental_analysis.py system.
    """
    n_replicates: int  # Number of biological replicates (N)
    scope: MicroscopeScope  # Microscope format
    conditions: tuple[ConditionConfig, ...]  # Immutable list of conditions

    # Global plate groups: replicate name → physical plate ID
    # From 'plate_groups' sheet: {"N1": "PLATE001", "N2": "PLATE002", ...}
    plate_groups: Dict[str, str]

    per_well_datapoints: bool = False  # Treat each well as individual datapoint
    controls: Optional[ControlConfig] = None
    excluded_wells: Optional[ExcludedWellsConfig] = None

    def __post_init__(self):
        """Validate configuration consistency."""
        # Ensure all conditions have all replicates defined
        for condition in self.conditions:
            for replicate_num in range(1, self.n_replicates + 1):
                if replicate_num not in condition.wells_by_replicate:
                    raise ValueError(
                        f"Condition '{condition.name}' missing Wells{replicate_num}"
                    )

        # Validate plate_groups has all replicates
        for replicate_num in range(1, self.n_replicates + 1):
            replicate_name = f"N{replicate_num}"
            if replicate_name not in self.plate_groups:
                raise ValueError(f"Missing plate group mapping for {replicate_name}")
```

#### 2. Validation Service (Registry Pattern with AutoRegisterMeta)

Create `openhcs/formats/experimental_layout_validator.py`:

Following OpenHCS registry pattern, create a base validator class with automatic subclass registration:

```python
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import List, Optional
from openhcs.core.auto_register_meta import AutoRegisterMeta

@dataclass(frozen=True)
class ValidationResult:
    """Immutable validation result following OpenHCS patterns."""
    is_valid: bool
    errors: tuple[str, ...] = ()
    warnings: tuple[str, ...] = ()

    @classmethod
    def success(cls) -> 'ValidationResult':
        """Create successful validation result."""
        return cls(is_valid=True)

    @classmethod
    def error(cls, *errors: str) -> 'ValidationResult':
        """Create failed validation with errors."""
        return cls(is_valid=False, errors=errors)

    @classmethod
    def warning(cls, *warnings: str) -> 'ValidationResult':
        """Create successful validation with warnings."""
        return cls(is_valid=True, warnings=warnings)

class ExperimentalLayoutValidatorBase(ABC, metaclass=AutoRegisterMeta):
    """
    Base validator using OpenHCS registry pattern.

    Subclasses auto-register by setting VALIDATOR_NAME class attribute.
    Registry stored as ExperimentalLayoutValidatorBase.__registry__.
    """
    __registry_key__ = 'VALIDATOR_NAME'

    VALIDATOR_NAME: str  # Each validator must define this

    @abstractmethod
    def validate(self, config: ExperimentalLayoutConfig) -> ValidationResult:
        """
        Validate configuration.

        Args:
            config: Configuration to validate

        Returns:
            ValidationResult with errors/warnings

        Note: This method respects OpenHCS fail-loud principles.
              Direct attribute access, no defensive programming.
        """
        pass

# Concrete validator implementations

class DoseWellCountValidator(ExperimentalLayoutValidatorBase):
    """Validates dose-well count matching."""
    VALIDATOR_NAME = "dose_well_count"

    def validate(self, config: ExperimentalLayoutConfig) -> ValidationResult:
        """Ensure len(doses) == len(wells) for all WellsRows."""
        errors = []

        for condition in config.conditions:
            for replicate_num, wells_rows in condition.wells_by_replicate.items():
                for tech_rep_idx, wells_row in enumerate(wells_rows, start=1):
                    if len(condition.doses) != len(wells_row.wells):
                        errors.append(
                            f"Condition '{condition.name}' N{replicate_num} tech rep {tech_rep_idx}: "
                            f"{len(condition.doses)} doses != {len(wells_row.wells)} wells"
                        )

        return ValidationResult.error(*errors) if errors else ValidationResult.success()

class WellFormatValidator(ExperimentalLayoutValidatorBase):
    """Validates well ID format (A01, B12, etc.)."""
    VALIDATOR_NAME = "well_format"

    WELL_PATTERN = re.compile(r'^[A-P](0[1-9]|1[0-6])$')  # Supports up to 384-well

    def validate(self, config: ExperimentalLayoutConfig) -> ValidationResult:
        """Validate well IDs match standard format."""
        errors = []

        for condition in config.conditions:
            for replicate_num, wells_rows in condition.wells_by_replicate.items():
                for wells_row in wells_rows:
                    for well_id in wells_row.wells:
                        if not self.WELL_PATTERN.match(well_id):
                            errors.append(
                                f"Invalid well format '{well_id}' in condition '{condition.name}' N{replicate_num}"
                            )

        # Also validate controls and excluded wells
        if config.controls:
            for well_id in config.controls.well_ids:
                if not self.WELL_PATTERN.match(well_id):
                    errors.append(f"Invalid control well format '{well_id}'")

        if config.excluded_wells:
            for well_id in config.excluded_wells.well_ids:
                if not self.WELL_PATTERN.match(well_id):
                    errors.append(f"Invalid excluded well format '{well_id}'")

        return ValidationResult.error(*errors) if errors else ValidationResult.success()

class ReplicateCompletenessValidator(ExperimentalLayoutValidatorBase):
    """Validates all replicates 1..N are defined."""
    VALIDATOR_NAME = "replicate_completeness"

    def validate(self, config: ExperimentalLayoutConfig) -> ValidationResult:
        """Ensure all Wells1..WellsN defined for each condition."""
        # This validation is now handled in ExperimentalLayoutConfig.__post_init__
        # but we keep it for explicit validation service
        errors = []

        for condition in config.conditions:
            missing_replicates = []
            for replicate_num in range(1, config.n_replicates + 1):
                if replicate_num not in condition.wells_by_replicate:
                    missing_replicates.append(str(replicate_num))

            if missing_replicates:
                errors.append(
                    f"Condition '{condition.name}' missing Wells{', Wells'.join(missing_replicates)}"
                )

        return ValidationResult.error(*errors) if errors else ValidationResult.success()

# Validation service using registry

class ExperimentalLayoutValidationService:
    """
    Service for validating experimental layouts.

    Uses registry pattern to automatically discover all validators.
    Following OpenHCS service layer pattern.
    """

    def __init__(self):
        """Initialize with all registered validators."""
        self.validators = [
            validator_class()
            for validator_class in ExperimentalLayoutValidatorBase.__registry__.values()
        ]

    def validate(self, config: ExperimentalLayoutConfig) -> ValidationResult:
        """
        Run all validators against configuration.

        Returns:
            Combined ValidationResult with all errors/warnings
        """
        all_errors = []
        all_warnings = []

        for validator in self.validators:
            result = validator.validate(config)
            all_errors.extend(result.errors)
            all_warnings.extend(result.warnings)

        if all_errors:
            return ValidationResult(is_valid=False, errors=tuple(all_errors), warnings=tuple(all_warnings))
        elif all_warnings:
            return ValidationResult(is_valid=True, warnings=tuple(all_warnings))
        else:
            return ValidationResult.success()
```

#### 3. Service Layer (Separating Business Logic from UI)

Create `openhcs/formats/experimental_layout_service.py`:

Following OpenHCS service layer pattern - all business logic separated from UI:

```python
class ExperimentalLayoutService:
    """
    Service layer for experimental layout operations.

    Separates business logic from UI following OpenHCS patterns.
    Framework-agnostic - can be used by PyQt6, Textual, or CLI.
    """

    def __init__(self):
        """Initialize service with validation service."""
        self.validation_service = ExperimentalLayoutValidationService()

    def create_default_config(self, n_replicates: int = 3) -> ExperimentalLayoutConfig:
        """Create default configuration with placeholder data."""
        return ExperimentalLayoutConfig(
            n_replicates=n_replicates,
            scope=MicroscopeScope.EDDU_CX5,
            conditions=(),
            plate_groups={f"N{i}": f"PLATE_{i:03d}" for i in range(1, n_replicates + 1)},
        )

    def add_condition(
        self,
        config: ExperimentalLayoutConfig,
        condition_name: str,
        doses: tuple[str, ...],
    ) -> ExperimentalLayoutConfig:
        """
        Add new condition to configuration.

        Returns new frozen configuration with added condition.
        """
        # Create wells placeholder for all replicates
        wells_by_replicate = {}
        for replicate_num in range(1, config.n_replicates + 1):
            # Single technical replicate by default
            wells_row = WellsRow(
                wells=tuple(f"PLACEHOLDER_{i}" for i in range(len(doses))),
                plate_groups=tuple("1" for _ in range(len(doses)))
            )
            wells_by_replicate[replicate_num] = (wells_row,)

        new_condition = ConditionConfig(
            name=condition_name,
            doses=doses,
            wells_by_replicate=wells_by_replicate
        )

        # Return new config with added condition (frozen dataclass pattern)
        return dataclasses.replace(
            config,
            conditions=config.conditions + (new_condition,)
        )

    def update_condition_wells(
        self,
        config: ExperimentalLayoutConfig,
        condition_index: int,
        replicate_num: int,
        tech_rep_index: int,
        wells: tuple[str, ...],
        plate_groups: tuple[str, ...]
    ) -> ExperimentalLayoutConfig:
        """
        Update wells for specific condition/replicate/tech rep.

        Returns new frozen configuration with updated wells.
        """
        condition = config.conditions[condition_index]
        wells_rows = list(condition.wells_by_replicate[replicate_num])

        # Update specific tech rep
        wells_rows[tech_rep_index] = WellsRow(wells=wells, plate_groups=plate_groups)

        # Create new condition with updated wells
        new_wells_by_replicate = dict(condition.wells_by_replicate)
        new_wells_by_replicate[replicate_num] = tuple(wells_rows)

        new_condition = dataclasses.replace(
            condition,
            wells_by_replicate=new_wells_by_replicate
        )

        # Create new config with updated condition
        new_conditions = list(config.conditions)
        new_conditions[condition_index] = new_condition

        return dataclasses.replace(config, conditions=tuple(new_conditions))

    def validate_config(self, config: ExperimentalLayoutConfig) -> ValidationResult:
        """Validate configuration using validation service."""
        return self.validation_service.validate(config)

    def get_condition_summary(self, condition: ConditionConfig) -> str:
        """
        Get human-readable summary of condition.

        Used for UI display.
        """
        n_tech_reps = sum(len(wells_rows) for wells_rows in condition.wells_by_replicate.values())
        return f"{condition.name}: {len(condition.doses)} doses, {n_tech_reps} tech reps"
```

#### 4. PyQt6 Widget with Functional Dispatch Pattern

Create `openhcs/pyqt_gui/widgets/experimental_layout_widget.py`:

Following OpenHCS UI patterns - functional dispatch, no if/elif chains, service layer separation:

```python
from PyQt6.QtWidgets import *
from PyQt6.QtCore import pyqtSignal
from typing import Callable, Dict, Type

# Functional dispatch tables (OpenHCS pattern)
CELL_WIDGET_FACTORIES: Dict[str, Callable] = {
    'condition': lambda: QLineEdit(),
    'doses': lambda: QLineEdit(),  # Comma-separated
    'wells': lambda: QPushButton("Edit..."),  # Opens modal
    'plate_groups': lambda: QLineEdit(),
}

CELL_VALUE_EXTRACTORS: Dict[Type, Callable] = {
    QLineEdit: lambda w: w.text(),
    QPushButton: lambda w: w.property('stored_value'),
    QComboBox: lambda w: w.currentData(),
}

CELL_VALUE_SETTERS: Dict[Type, Callable] = {
    QLineEdit: lambda w, v: w.setText(str(v)),
    QPushButton: lambda w, v: (w.setProperty('stored_value', v), w.setText(str(len(v)) + " wells")),
    QComboBox: lambda w, v: w.setCurrentData(v),
}

class ExperimentalLayoutWidget(QWidget):
    """
    PyQt6 widget for experimental layout configuration.

    Architecture:
    - Service layer handles all business logic
    - Functional dispatch for widget operations (no if/elif)
    - Frozen dataclass configuration (immutable)
    - Registry-based validation
    """

    config_changed = pyqtSignal(object)  # Emits ExperimentalLayoutConfig
    validation_changed = pyqtSignal(object)  # Emits ValidationResult

    def __init__(self, config: ExperimentalLayoutConfig = None, parent=None):
        super().__init__(parent)

        # Service layer (OpenHCS pattern)
        self.service = ExperimentalLayoutService()

        # Current config (immutable)
        self._config = config or self.service.create_default_config()

        # Build UI
        self._build_ui()
        self._populate_from_config()

    def _build_ui(self):
        """Build widget UI structure."""
        layout = QVBoxLayout(self)

        # Section 1: Global Parameters
        layout.addWidget(self._create_global_params_section())

        # Section 2: Conditions Table
        layout.addWidget(self._create_conditions_section())

        # Section 3: Plate Groups
        layout.addWidget(self._create_plate_groups_section())

        # Section 4: Controls (collapsible)
        layout.addWidget(self._create_controls_section())

        # Section 5: Validation Panel
        self.validation_panel = self._create_validation_panel()
        layout.addWidget(self.validation_panel)

    def _create_global_params_section(self) -> QWidget:
        """Create global parameters section."""
        group = QGroupBox("Global Parameters")
        form = QFormLayout()

        # N replicates
        self.n_spin = QSpinBox()
        self.n_spin.setRange(1, 10)
        self.n_spin.valueChanged.connect(self._on_config_changed)
        form.addRow("Number of Replicates (N):", self.n_spin)

        # Scope
        self.scope_combo = QComboBox()
        for scope in MicroscopeScope:
            self.scope_combo.addItem(scope.value, scope)
        self.scope_combo.currentIndexChanged.connect(self._on_config_changed)
        form.addRow("Microscope Scope:", self.scope_combo)

        # Per Well Datapoints
        self.per_well_check = QCheckBox()
        self.per_well_check.stateChanged.connect(self._on_config_changed)
        form.addRow("Per Well Datapoints:", self.per_well_check)

        group.setLayout(form)
        return group

    def _create_conditions_section(self) -> QWidget:
        """Create conditions table section with functional dispatch."""
        group = QGroupBox("Experimental Conditions")
        layout = QVBoxLayout()

        # Table
        self.conditions_table = QTableWidget()
        self.conditions_table.setColumnCount(5)
        self.conditions_table.setHorizontalHeaderLabels([
            "Condition", "Doses", "Replicates", "Tech Reps", "Actions"
        ])
        self.conditions_table.cellChanged.connect(self._on_condition_cell_changed)
        layout.addWidget(self.conditions_table)

        # Buttons
        button_layout = QHBoxLayout()
        add_btn = QPushButton("Add Condition")
        add_btn.clicked.connect(self._on_add_condition)
        remove_btn = QPushButton("Remove Condition")
        remove_btn.clicked.connect(self._on_remove_condition)
        button_layout.addWidget(add_btn)
        button_layout.addWidget(remove_btn)
        layout.addLayout(button_layout)

        group.setLayout(layout)
        return group

    def _get_widget_value(self, widget: QWidget) -> any:
        """
        Extract value from widget using functional dispatch.

        Following OpenHCS functional dispatch pattern - no if/elif chains.
        """
        extractor = CELL_VALUE_EXTRACTORS.get(type(widget))
        return extractor(widget) if extractor else None

    def _set_widget_value(self, widget: QWidget, value: any):
        """
        Set widget value using functional dispatch.

        Following OpenHCS functional dispatch pattern - no if/elif chains.
        """
        setter = CELL_VALUE_SETTERS.get(type(widget))
        if setter:
            setter(widget, value)

    def _on_config_changed(self):
        """
        Handle configuration change.

        Creates new frozen config, validates, emits signals.
        """
        # Extract config from UI (service layer handles this)
        new_config = self._extract_config_from_ui()

        # Validate using service
        validation_result = self.service.validate_config(new_config)

        # Update internal state
        self._config = new_config

        # Emit signals
        self.config_changed.emit(new_config)
        self.validation_changed.emit(validation_result)

        # Update validation panel
        self._update_validation_panel(validation_result)

    def get_config(self) -> ExperimentalLayoutConfig:
        """
        Get current configuration.

        Direct access following OpenHCS fail-loud principle.
        """
        return self._config

    def set_config(self, config: ExperimentalLayoutConfig):
        """
        Set configuration and update UI.

        Direct attribute assignment - respects architectural guarantees.
        """
        self._config = config
        self._populate_from_config()
```

**Structure:**
- Service layer (`ExperimentalLayoutService`) handles all business logic
- Functional dispatch tables for widget operations (no if/elif chains)
- Frozen dataclass configuration (immutable updates)
- Registry-based validation service
- Direct attribute access (no defensive programming)

#### 5. Excel I/O (Service Layer)

Create `openhcs/formats/experimental_layout_io.py`:

```python
class ExperimentalLayoutIOService:
    """
    Service for loading/saving experimental layouts from/to Excel.

    Integrates with existing experimental_analysis.py functions.
    """

    def load_from_excel(self, excel_path: str) -> ExperimentalLayoutConfig:
        """
        Load experimental layout from Excel file.

        Wraps existing read_plate_layout() and load_plate_groups() functions.
        """
        from openhcs.formats.experimental_analysis import read_plate_layout, load_plate_groups

        # Parse Excel using existing functions
        scope, plate_layout, conditions, ctrl_positions, excluded_positions, per_well_datapoints = read_plate_layout(excel_path)
        plate_groups = load_plate_groups(excel_path)

        # Convert to frozen dataclass configuration
        return self._convert_to_config(
            scope, plate_layout, conditions, plate_groups,
            ctrl_positions, excluded_positions, per_well_datapoints
        )

    def save_to_excel(self, config: ExperimentalLayoutConfig, excel_path: str):
        """Save experimental layout to Excel file."""
        # Convert config back to Excel format
        # Implementation details...
```

#### 6. Integration Points

- **PlateManagerWidget Integration**: Add as collapsible section or dialog
- **Menu Item**: Tools → Configure Experimental Layout
- **Drag-Drop Support**: Load Excel files via drag-drop
- **Export**: Save button to write config back to Excel

### Architecture Summary

**OpenHCS Patterns Applied:**

1. **Registry Pattern** (`AutoRegisterMeta`)
   - Validators auto-register via `ExperimentalLayoutValidatorBase`
   - Easy to add new validators without modifying core code

2. **Frozen Dataclasses**
   - Immutable configuration following OpenHCS config patterns
   - `dataclasses.replace()` for updates (pure functional style)

3. **Service Layer**
   - All business logic in service classes
   - UI only handles presentation
   - Services testable without UI dependencies

4. **Functional Dispatch**
   - Widget operations via dispatch tables
   - No if/elif chains (O(1) vs O(n))
   - Easy to add new widget types

5. **Fail-Loud Validation**
   - Direct attribute access (no `getattr` with defaults)
   - Validation in `__post_init__` catches errors early
   - No defensive programming

6. **Lazy Config Integration** (Future)
   - Can integrate with `@global_pipeline_config` for dual-axis resolution
   - Allows experimental layout config to inherit from global settings

### Redesign Improvements vs Original Plan

**Original Plan Issues:**
1. Mutable dataclasses (security risk, hard to track changes)
2. No service layer (business logic mixed with UI)
3. If/elif chains for widget operations (O(n) complexity)
4. Manual validator instantiation (no registry)
5. Defensive programming (`hasattr` checks)

**Redesigned Solutions:**
1. ✅ Frozen dataclasses (immutable, thread-safe)
2. ✅ Service layer (framework-agnostic, testable)
3. ✅ Functional dispatch (O(1), extensible)
4. ✅ Auto-registering validators (extensible, no imports)
5. ✅ Fail-loud (respects architectural guarantees)

### Next Steps

1. **Review & Approval**: Get stakeholder approval on data model and architecture
2. **Implement Core Models**: `experimental_layout_config.py` with frozen dataclasses
3. **Implement Validators**: Registry-based validation system
4. **Implement Service Layer**: Business logic separation
5. **Implement UI**: PyQt6 widget with functional dispatch
6. **Excel I/O Integration**: Wrap existing `experimental_analysis.py` functions
7. **Testing**: Unit tests for services, integration tests for UI
8. **Documentation**: Sphinx docs following OpenHCS patterns

### Testing Strategy

```python
# Unit tests (no UI dependencies)
def test_validation_service():
    config = ExperimentalLayoutConfig(...)
    service = ExperimentalLayoutValidationService()
    result = service.validate(config)
    assert result.is_valid

# Service layer tests
def test_experimental_layout_service():
    service = ExperimentalLayoutService()
    config = service.create_default_config(n_replicates=3)
    new_config = service.add_condition(config, "Drug_A", ("0", "10", "50"))
    assert len(new_config.conditions) == 1

# Integration tests (with UI)
def test_widget_integration(qtbot):
    widget = ExperimentalLayoutWidget()
    qtbot.addWidget(widget)
    # Test UI interactions...
```

