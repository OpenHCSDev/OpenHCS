# plan_01_package_extraction.md
## Component: Package Extraction Strategy

### Objective
Extract the metaclass registry system and memory type system into two standalone PyPI packages, then make OpenHCS depend on them as external dependencies.

### Plan

#### Phase 1: Package Structure Creation

**1.1 Create `metaclass-registry` Package**
- Create new repository structure at `/home/ts/code/projects/metaclass-registry/`
- Package name: `metaclass-registry` (PyPI), import as `metaclass_registry`
- Directory structure:
  ```
  metaclass-registry/
  ├── src/
  │   └── metaclass_registry/
  │       ├── __init__.py
  │       ├── core.py              # AutoRegisterMeta, RegistryConfig
  │       ├── discovery.py         # LazyDiscoveryDict, discovery functions
  │       ├── cache.py             # RegistryCacheManager
  │       ├── helpers.py           # SecondaryRegistry, key extractors
  │       └── exceptions.py        # Custom exceptions
  ├── tests/
  │   ├── test_core.py
  │   ├── test_discovery.py
  │   ├── test_cache.py
  │   └── test_integration.py
  ├── docs/
  │   ├── index.md
  │   ├── quickstart.md
  │   ├── patterns.md
  │   └── api.md
  ├── examples/
  │   ├── basic_registry.py
  │   ├── secondary_registry.py
  │   └── cached_registry.py
  ├── pyproject.toml
  ├── README.md
  ├── LICENSE (MIT)
  └── .github/
      └── workflows/
          └── ci.yml
  ```

**1.2 Create `arraybridge` Package**
- Create new repository structure at `/home/ts/code/projects/arraybridge/`
- Package name: `arraybridge` (PyPI), import as `arraybridge`
- Directory structure:
  ```
  arraybridge/
  ├── src/
  │   └── arraybridge/
  │       ├── __init__.py
  │       ├── types.py             # MemoryType enum, constants
  │       ├── converters.py        # convert_memory, detect_memory_type
  │       ├── conversion_helpers.py # MemoryTypeConverter ABC
  │       ├── decorators.py        # @numpy, @torch, @cupy, etc.
  │       ├── framework_config.py  # _FRAMEWORK_CONFIG
  │       ├── stack_utils.py       # stack_slices, unstack_slices
  │       ├── utils.py             # _ensure_module, device management
  │       ├── oom_recovery.py      # OOM detection and recovery
  │       ├── dtype_scaling.py     # Dtype conversion utilities
  │       ├── slice_processing.py  # Slice processing utilities
  │       ├── gpu_cleanup.py       # GPU memory cleanup
  │       └── exceptions.py        # MemoryConversionError
  ├── tests/
  │   ├── test_converters.py
  │   ├── test_decorators.py
  │   ├── test_stack_utils.py
  │   ├── test_oom_recovery.py
  │   └── test_integration.py
  ├── docs/
  │   ├── index.md
  │   ├── quickstart.md
  │   ├── frameworks.md
  │   ├── decorators.md
  │   └── api.md
  ├── examples/
  │   ├── basic_conversion.py
  │   ├── decorator_usage.py
  │   ├── multi_gpu.py
  │   └── oom_handling.py
  ├── pyproject.toml
  ├── README.md
  ├── LICENSE (MIT)
  └── .github/
      └── workflows/
          └── ci.yml
  ```

#### Phase 2: Code Extraction and Adaptation

**2.1 Extract `metaclass-registry` Code**
- Copy from `openhcs/core/auto_register_meta.py` → `src/metaclass_registry/core.py`
- Copy from `openhcs/core/registry_discovery.py` → `src/metaclass_registry/discovery.py`
- Copy from `openhcs/core/registry_cache.py` → `src/metaclass_registry/cache.py`
- Remove OpenHCS-specific dependencies:
  - Replace `openhcs.constants` imports with package-local constants
  - Extract `optional_import` helper to package
  - Make XDG cache path configurable (default: `~/.cache/metaclass_registry/`)
- Add type hints throughout
- Add comprehensive docstrings

**2.2 Extract `arraybridge` Code**
- Copy from `openhcs/core/memory/` → `src/arraybridge/`
- Remove OpenHCS-specific dependencies:
  - Extract `MemoryType` enum to `types.py`
  - Extract `optional_import` to `utils.py`
  - Remove references to `openhcs.constants`
  - Remove Clause 278 enforcement (make it optional via decorator parameter)
- Make 3D enforcement optional:
  ```python
  @numpy(enforce_3d=True)  # Optional parameter
  def my_function(data):
      pass
  ```
- Add type hints throughout
- Add comprehensive docstrings

#### Phase 3: Testing Infrastructure

**3.1 `metaclass-registry` Tests**
- Test basic registration
- Test lazy discovery
- Test registry inheritance
- Test secondary registries
- Test caching (with mock filesystem)
- Test key extractors
- Test auto-configuration
- Integration tests with real plugin systems

**3.2 `arraybridge` Tests**
- Test conversions between all framework pairs (36 combinations)
- Test decorators with all frameworks
- Test OOM recovery (with mocked OOM errors)
- Test device management
- Test dtype preservation
- Test stack/unstack operations
- Test thread-local stream management
- Integration tests with real GPU operations (if available)

#### Phase 4: Documentation

**4.1 `metaclass-registry` Documentation**
- README with quick example
- Quickstart guide
- Pattern guide (when to use which pattern)
- API reference
- Migration guide (for OpenHCS)
- Comparison to alternatives (Django, SQLAlchemy patterns)

**4.2 `arraybridge` Documentation**
- README with quick example
- Quickstart guide
- Framework support matrix
- Decorator guide
- Device management guide
- OOM recovery guide
- API reference
- Migration guide (for OpenHCS)
- Comparison to alternatives (array-api-compat, einops)

#### Phase 5: Package Configuration

**5.1 `metaclass-registry` pyproject.toml**
```toml
[build-system]
requires = ["hatchling"]
build-backend = "hatchling.build"

[project]
name = "metaclass-registry"
version = "0.1.0"
description = "Zero-boilerplate metaclass-driven plugin registry system"
authors = [{name = "Tristan Simas", email = "tristan.simas@mail.mcgill.ca"}]
license = {text = "MIT"}
readme = "README.md"
requires-python = ">=3.9"
dependencies = []

[project.optional-dependencies]
dev = ["pytest>=7.0", "pytest-cov", "black", "ruff", "mypy"]
docs = ["mkdocs", "mkdocs-material", "mkdocstrings[python]"]

[project.urls]
Homepage = "https://github.com/trissim/metaclass-registry"
Documentation = "https://metaclass-registry.readthedocs.io"
Repository = "https://github.com/trissim/metaclass-registry"
```

**5.2 `arraybridge` pyproject.toml**
```toml
[build-system]
requires = ["hatchling"]
build-backend = "hatchling.build"

[project]
name = "arraybridge"
version = "0.1.0"
description = "Unified API for NumPy, CuPy, PyTorch, TensorFlow, JAX, and pyclesperanto"
authors = [{name = "Tristan Simas", email = "tristan.simas@mail.mcgill.ca"}]
license = {text = "MIT"}
readme = "README.md"
requires-python = ">=3.9"
dependencies = ["numpy>=1.20"]

[project.optional-dependencies]
cupy = ["cupy>=10.0"]
torch = ["torch>=1.10"]
tensorflow = ["tensorflow>=2.8"]
jax = ["jax>=0.3", "jaxlib>=0.3"]
pyclesperanto = ["pyclesperanto>=0.10"]
all = ["cupy>=10.0", "torch>=1.10", "tensorflow>=2.8", "jax>=0.3", "jaxlib>=0.3", "pyclesperanto>=0.10"]
dev = ["pytest>=7.0", "pytest-cov", "black", "ruff", "mypy"]
docs = ["mkdocs", "mkdocs-material", "mkdocstrings[python]"]

[project.urls]
Homepage = "https://github.com/trissim/arraybridge"
Documentation = "https://arraybridge.readthedocs.io"
Repository = "https://github.com/trissim/arraybridge"
```

#### Phase 6: OpenHCS Migration

**6.1 Update OpenHCS Dependencies**
- Add to `pyproject.toml`:
  ```toml
  dependencies = [
      "metaclass-registry>=0.1.0",
      "arraybridge>=0.1.0",
      # ... other deps
  ]
  ```

**6.2 Update OpenHCS Imports**
- Replace `from openhcs.core.auto_register_meta import ...` with `from metaclass_registry import ...`
- Replace `from openhcs.core.memory import ...` with `from arraybridge import ...`
- Update all affected files:
  - `openhcs/io/base.py`
  - `openhcs/io/backend_registry.py`
  - `openhcs/microscopes/microscope_base.py`
  - `openhcs/runtime/zmq_base.py`
  - `openhcs/processing/backends/lib_registry/unified_registry.py`
  - `openhcs/processing/backends/experimental_analysis/format_registry.py`
  - All files using memory decorators

**6.3 Remove Extracted Code from OpenHCS**
- Delete `openhcs/core/auto_register_meta.py`
- Delete `openhcs/core/registry_discovery.py`
- Delete `openhcs/core/registry_cache.py`
- Delete `openhcs/core/memory/` directory
- Update `openhcs/core/__init__.py` to remove deleted imports

**6.4 Update OpenHCS Tests**
- Update import statements in tests
- Verify all tests still pass

#### Phase 7: CI/CD Setup

**7.1 GitHub Actions for Both Packages**
- Test matrix: Python 3.9, 3.10, 3.11, 3.12
- Run tests with and without optional dependencies
- Code coverage reporting
- Linting (ruff, black)
- Type checking (mypy)
- Build and publish to PyPI on release tags

**7.2 Documentation Hosting**
- Set up ReadTheDocs for both packages
- Auto-deploy on main branch updates

#### Phase 8: Publication

**8.1 Initial Release (v0.1.0)**
- Tag releases in both repos
- Publish to PyPI
- Announce on:
  - Python subreddit
  - Scientific Python discourse
  - Twitter/X
  - LinkedIn

**8.2 Blog Posts**
- "Zero-Boilerplate Plugin Systems in Python"
- "Unified Array API: One Decorator to Rule Them All"
- "How We Eliminated 2,000+ Lines of Boilerplate"

**8.3 Potential Paper**
- "ArrayBridge: A Unified Memory Type System for Scientific Python"
- Submit to JOSS (Journal of Open Source Software)
- Or SciPy conference proceedings

### Implementation Order

1. ✅ Create plan file (this file)
2. ✅ Create `metaclass-registry` package structure
3. ✅ Create `arraybridge` package structure
4. ⏳ Extract and adapt `metaclass-registry` code
5. ⏳ Extract and adapt `arraybridge` code
6. ⏳ Write tests for `metaclass-registry`
7. ⏳ Write tests for `arraybridge`
8. ⏳ Write documentation for both
9. ⏳ Set up CI/CD for both
10. ⏳ Migrate OpenHCS to use packages
11. ⏳ Publish v0.1.0 to PyPI
12. ⏳ Write blog posts and announce

### Findings

**Package Structures Created:**

Both packages now have initial structure at:
- `/home/ts/code/projects/metaclass-registry/` (commit: bfd5961)
- `/home/ts/code/projects/arraybridge/` (commit: e4919ab)

**Files Created:**
- `pyproject.toml` - Package metadata and dependencies
- `README.md` - Quick start guide and examples
- `LICENSE` - MIT license
- `.gitignore` - Python project ignores
- `src/<package>/__init__.py` - Public API exports
- `src/<package>/exceptions.py` - Custom exceptions

**Directory Structure:**
```
<package>/
├── src/<package>/          # Source code (ready for extraction)
├── tests/                  # Test suite (empty, ready for tests)
├── docs/                   # Documentation (empty, ready for docs)
├── examples/               # Example scripts (empty, ready for examples)
├── .github/workflows/      # CI/CD (empty, ready for GitHub Actions)
├── pyproject.toml
├── README.md
├── LICENSE
└── .gitignore
```

**Infrastructure Reused from OpenHCS:**
- ✅ GitHub Actions workflows (adapted for both packages)
- ✅ mkdocs configuration (adapted from Sphinx setup)
- ✅ pytest configuration patterns
- ✅ Code quality tools (ruff, black, mypy)
- ✅ PyPI publish workflow

**CI/CD Setup Complete:**
- metaclass-registry: Tests Python 3.9-3.12 on Linux/Windows/macOS
- arraybridge: Tests Python 3.9-3.12 on Linux/Windows/macOS with framework matrix (none, torch, cupy)
- Both: Code quality checks, coverage reporting, PyPI publish on tags

**Commits:**
- metaclass-registry: `0428851` (CI/CD infrastructure)
- arraybridge: `25561b1` (CI/CD infrastructure)

**Next Immediate Steps:**
1. Create GitHub repositories for both packages
2. Push initial code to GitHub
3. Extract code from OpenHCS to both packages
4. Remove OpenHCS-specific dependencies
5. Add type hints and comprehensive docstrings
6. Write tests with >90% coverage
7. Create GitHub Project to track multi-repo work

### Success Criteria

- Both packages installable via `pip install`
- All tests passing with >90% coverage
- Documentation complete and hosted
- OpenHCS successfully using both packages
- Zero breaking changes in OpenHCS functionality
- CI/CD green on all platforms

