# plan_01_package_scaffold.md
## Component: Package Scaffold

### Objective
Create the external package structure for `pyqt-reactor` with proper Python packaging, matching the ObjectState package structure in `external/ObjectState`.

### Plan

1. **Create directory structure**:
   ```
   external/pyqt-reactor/
   ├── src/
   │   └── pyqt_formgen/
   │       ├── __init__.py
   │       ├── core/
   │       │   └── __init__.py
   │       ├── theming/
   │       │   └── __init__.py
   │       ├── protocols/
   │       │   └── __init__.py
   │       ├── widgets/
   │       │   └── __init__.py
   │       ├── animation/
   │       │   └── __init__.py
   │       ├── services/
   │       │   └── __init__.py
   │       └── forms/
   │           └── __init__.py
   ├── tests/
   │   ├── __init__.py
   │   └── conftest.py
   ├── docs/
   ├── pyproject.toml
   ├── README.md
   └── LICENSE
   ```

2. **Create pyproject.toml** with:
   - hatchling build system (matching ObjectState)
   - PyQt6 >= 6.4.0 as required dependency
   - objectstate >= 0.1.0 as required dependency  
   - python-introspect >= 0.1.0 as required dependency
   - Optional dev dependencies (pytest, black, ruff, mypy)
   - Optional docs dependencies (sphinx, sphinx-rtd-theme)

3. **Create root __init__.py** with:
   - Version string
   - Public API re-exports from submodules
   - Docstring describing the package

4. **Create stub __init__.py** in each subpackage:
   - Empty for now, will be populated by subsequent plans
   - Include docstring describing the subpackage purpose

5. **Create conftest.py** with:
   - PyQt6 QApplication fixture for tests
   - Common test utilities

6. **Create README.md** with:
   - Package description
   - Installation instructions
   - Basic usage example
   - Link to documentation

7. **Add to OpenHCS editable install**:
   - Update openhcs pyproject.toml to include pyqt-reactor as editable dep
   - Or document manual `pip install -e external/pyqt-reactor`

### Findings

**Package naming**: Using `pyqt-reactor` (hyphenated) for PyPI name, `pyqt_formgen` (underscored) for import name. This matches Python packaging conventions.

**Build system**: Using hatchling to match ObjectState. This is a modern, standards-compliant build backend.

**Dependency versions**:
- PyQt6 >= 6.4.0: Minimum for stable API
- objectstate >= 0.1.0: Current version in external/ObjectState
- python-introspect: External introspection package

**Test framework**: pytest with pytest-qt for PyQt6 testing support.

### Implementation Draft
<!-- Only write code here AFTER smell loop passes -->

