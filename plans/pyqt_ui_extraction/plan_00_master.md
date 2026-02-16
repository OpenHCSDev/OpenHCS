# plan_00_master.md
## Master Plan: PyQt UI Framework Extraction

### Objective
Extract a reusable, generic PyQt6 UI framework from OpenHCS into an external package (`pyqt-reactor` or similar). This framework will include ParameterFormManager and all supporting components, with ObjectState as an optional or required dependency.

### Package Name: `pyqt-reactor`
A React-quality reactive form generation framework for PyQt6.

### Key Design Decisions

1. **ObjectState as Required Dependency**: Since ObjectState is already external and provides the state management layer that ParameterFormManager depends on, it will be a required dependency of pyqt-reactor.

2. **python_introspect as Required Dependency**: The introspection layer is already external and provides parameter extraction.

3. **Layered Architecture**:
   - **Tier 1 (Core)**: Pure PyQt6 utilities with zero external deps beyond PyQt6
   - **Tier 2 (Protocols)**: Widget ABCs and adapters
   - **Tier 3 (Services)**: Reusable service layer
   - **Tier 4 (Forms)**: ParameterFormManager with ObjectState integration

### Package Structure
```
pyqt-reactor/
├── src/
│   └── pyqt_formgen/
│       ├── __init__.py
│       ├── core/                 # Tier 1: Pure PyQt utilities
│       │   ├── __init__.py
│       │   ├── debounce_timer.py
│       │   ├── reorderable_list_widget.py
│       │   └── rich_text_appender.py
│       ├── theming/              # Tier 1: Color scheme and styling
│       │   ├── __init__.py
│       │   ├── color_scheme.py
│       │   ├── palette_manager.py
│       │   └── style_generator.py
│       ├── protocols/            # Tier 2: Widget ABCs
│       │   ├── __init__.py
│       │   ├── widget_protocols.py
│       │   └── widget_adapters.py
│       ├── widgets/              # Tier 2: Extended widgets
│       │   ├── __init__.py
│       │   ├── no_scroll_spinbox.py
│       │   └── flashable_groupbox.py
│       ├── animation/            # Tier 3: Flash/animation system
│       │   ├── __init__.py
│       │   ├── flash_config.py
│       │   ├── flash_mixin.py
│       │   └── flash_overlay.py
│       ├── services/             # Tier 3: Reusable services
│       │   ├── __init__.py
│       │   ├── signal_service.py
│       │   ├── widget_service.py
│       │   ├── value_collection_service.py
│       │   └── flag_context_manager.py
│       └── forms/                # Tier 4: ParameterFormManager
│           ├── __init__.py
│           ├── parameter_form_manager.py
│           ├── form_manager_config.py
│           ├── widget_creation_types.py
│           ├── widget_creation_config.py
│           ├── widget_strategies.py
│           ├── widget_factory.py
│           ├── widget_operations.py
│           ├── widget_registry.py
│           └── form_init_service.py
├── tests/
├── docs/
├── pyproject.toml
└── README.md
```

### Execution Order (Sequenced Plans)

| Plan | Component | Description | Dependencies |
|------|-----------|-------------|--------------|
| 01 | Package Scaffold | Create external/pyqt-reactor with pyproject.toml | None |
| 02 | Core Utilities | Extract debounce_timer, reorderable_list_widget | Plan 01 |
| 03 | Theming Layer | Extract color_scheme, palette_manager, style_generator | Plan 01 |
| 04 | Widget Protocols | Extract widget_protocols.py, widget_adapters.py | Plan 01 |
| 05 | Extended Widgets | Extract no_scroll_spinbox.py with protocol deps | Plans 04 |
| 06 | Animation System | Extract flash_config, flash_mixin, overlay | Plans 03, 05 |
| 07 | Service Layer | Extract all services from services/ folder | Plans 04, 05 |
| 08 | Widget Factory | Extract widget_factory, widget_registry, widget_operations | Plans 04, 07 |
| 09 | Form Init Service | Extract form_init_service with introspection deps | Plans 07, 08 |
| 10 | ParameterFormManager | Extract the main form manager class | All previous |
| 11 | Import Updates | Update ALL OpenHCS imports, delete extracted files | Plan 10 |
| 12 | Test Migration | Migrate/create tests for extracted package | Plan 11 |
| 13 | Documentation | API docs and examples | Plan 12 |

### Dependencies for pyqt-reactor
```toml
[project]
dependencies = [
    "PyQt6>=6.4.0",
    "objectstate>=0.1.0",
    "python-introspect>=0.1.0",
]
```

### Critical Success Criteria
1. **Clean Break**: All OpenHCS imports updated to use pyqt_formgen directly
2. **File Deletion**: Original extracted files deleted from OpenHCS (no shims)
3. **All Tests Pass**: Existing tests must pass after import updates
4. **Independent Testability**: pyqt-reactor has its own test suite
5. **Documentation**: API docs with usage examples
6. **Minimal Coupling**: Clear dependency boundaries between tiers

### Smell Loop Gates
Each plan must pass smell review before implementation:
- No circular imports between tiers
- No OpenHCS-specific logic in generic components
- Proper ABC contracts at tier boundaries
- Consistent naming conventions

