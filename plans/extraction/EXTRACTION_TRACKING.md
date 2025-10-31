# Package Extraction Tracking

**Multi-Repository Project**: Extracting metaclass-registry and arraybridge from OpenHCS

## Repositories

1. **metaclass-registry**: `/home/ts/code/projects/metaclass-registry/`
   - GitHub: `https://github.com/trissim/metaclass-registry` ✅ CREATED
   - PyPI: `metaclass-registry` (to be published)

2. **arraybridge**: `/home/ts/code/projects/arraybridge/`
   - GitHub: `https://github.com/trissim/arraybridge` ✅ CREATED
   - PyPI: `arraybridge` (to be published)

3. **lazy-config**: `/home/ts/code/projects/lazy-config-framework/`
   - GitHub: `https://github.com/trissim/lazy-config` ✅ CREATED
   - PyPI: `lazy-config` (to be published)

4. **openhcs-metaregister**: `/home/ts/code/projects/openhcs-metaregister/`
   - GitHub: `https://github.com/trissim/openhcs` (existing)
   - Branch: `metaregister`
   - Will be updated to depend on the three new packages

## Progress Overview

### Phase 1: Package Structure ✅ COMPLETE

- [x] Create `metaclass-registry` directory structure
- [x] Create `arraybridge` directory structure
- [x] Add `pyproject.toml` for both packages
- [x] Add README.md for both packages
- [x] Add LICENSE (MIT) for both packages
- [x] Add .gitignore for both packages
- [x] Create initial `__init__.py` files
- [x] Create exception classes
- [x] Copy CI/CD workflows from OpenHCS
- [x] Create mkdocs configuration
- [x] Initial git commits

**Commits:**
- metaclass-registry: `bfd5961` (initial structure)
- arraybridge: `e4919ab` (initial structure)

### Phase 2: Code Extraction ⏳ IN PROGRESS

#### metaclass-registry

- [ ] Extract `openhcs/core/auto_register_meta.py` → `src/metaclass_registry/core.py`
- [ ] Extract registry discovery code → `src/metaclass_registry/discovery.py`
- [ ] Extract cache manager → `src/metaclass_registry/cache.py`
- [ ] Extract helper classes → `src/metaclass_registry/helpers.py`
- [ ] Remove OpenHCS-specific dependencies
- [ ] Add comprehensive type hints
- [ ] Add comprehensive docstrings

**Files to extract:**
- `openhcs/core/auto_register_meta.py` (main file, ~600 lines)
- Registry discovery utilities
- Cache manager utilities

#### arraybridge

- [ ] Extract `openhcs/core/memory/` → `src/arraybridge/`
  - [ ] `types.py` (MemoryType enum from `openhcs/constants/constants.py`)
  - [ ] `converters.py` (from `converters.py`)
  - [ ] `conversion_helpers.py` (from `conversion_helpers.py`)
  - [ ] `decorators.py` (from `decorators.py`)
  - [ ] `framework_config.py` (from `framework_config.py`)
  - [ ] `stack_utils.py` (from `stack_utils.py`)
  - [ ] `utils.py` (from `utils.py` + `optional_import` from `openhcs/core/utils.py`)
  - [ ] `oom_recovery.py` (from `oom_recovery.py`)
  - [ ] `dtype_scaling.py` (from `dtype_scaling.py`)
  - [ ] `slice_processing.py` (from `slice_processing.py`)
  - [ ] `gpu_cleanup.py` (from `gpu_cleanup.py`)
- [ ] Remove OpenHCS-specific dependencies
- [ ] Make 3D enforcement optional (add `enforce_3d` parameter to decorators)
- [ ] Add comprehensive type hints
- [ ] Add comprehensive docstrings

**Files to extract:**
- All 12 files from `openhcs/core/memory/`
- `MemoryType` enum from `openhcs/constants/constants.py`
- `optional_import` from `openhcs/core/utils.py`

#### lazy-config

- [ ] Extract `openhcs/config_framework/` → `src/lazy_config/`
  - [ ] `config.py` (framework configuration)
  - [ ] `lazy_factory.py` (lazy dataclass factory)
  - [ ] `dual_axis_resolver.py` (dual-axis inheritance resolver)
  - [ ] `context_manager.py` (contextvars-based context management)
  - [ ] `placeholder.py` (placeholder text generation)
  - [ ] `global_config.py` (thread-local global config storage)
  - [ ] `cache_warming.py` (cache warming utilities)
- [ ] Remove OpenHCS-specific dependencies:
  - [ ] Remove `AutoRegisterMeta` import (replace with metaclass-registry dependency)
  - [ ] Remove UI-specific imports (make placeholder service optional)
  - [ ] Remove introspection imports (make cache warming optional)
- [ ] Add comprehensive type hints
- [ ] Add comprehensive docstrings

**Files to extract:**
- All 7 files from `openhcs/config_framework/`
- Will depend on `metaclass-registry` for AutoRegisterMeta

### Phase 3: Testing ⏳ NOT STARTED

#### metaclass-registry

- [ ] `tests/test_core.py` - Test AutoRegisterMeta
- [ ] `tests/test_discovery.py` - Test LazyDiscoveryDict
- [ ] `tests/test_cache.py` - Test RegistryCacheManager
- [ ] `tests/test_helpers.py` - Test SecondaryRegistry
- [ ] `tests/test_integration.py` - Integration tests
- [ ] Achieve >90% coverage

#### arraybridge

- [ ] `tests/test_converters.py` - Test all 36 conversion pairs
- [ ] `tests/test_decorators.py` - Test all decorators
- [ ] `tests/test_stack_utils.py` - Test stack/unstack
- [ ] `tests/test_oom_recovery.py` - Test OOM handling
- [ ] `tests/test_integration.py` - Integration tests
- [ ] Achieve >90% coverage

### Phase 4: Documentation ⏳ NOT STARTED

#### metaclass-registry

- [ ] `docs/index.md` - Home page
- [ ] `docs/quickstart.md` - Quick start guide
- [ ] `docs/patterns.md` - Pattern guide
- [ ] `docs/api.md` - API reference
- [ ] `docs/examples/` - Example scripts

#### arraybridge

- [ ] `docs/index.md` - Home page
- [ ] `docs/quickstart.md` - Quick start guide
- [ ] `docs/frameworks.md` - Framework support matrix
- [ ] `docs/decorators.md` - Decorator guide
- [ ] `docs/api.md` - API reference
- [ ] `docs/examples/` - Example scripts

### Phase 5: CI/CD Setup ✅ COMPLETE

- [x] GitHub Actions workflows for both packages
- [x] Test matrix: Python 3.9-3.12, Linux/Windows/macOS
- [x] Code quality checks (ruff, black, mypy)
- [x] PyPI publish workflow
- [x] mkdocs configuration

### Phase 6: OpenHCS Migration ⏳ NOT STARTED

- [ ] Add `metaclass-registry>=0.1.0` to `pyproject.toml`
- [ ] Add `arraybridge>=0.1.0` to `pyproject.toml`
- [ ] Update imports in all affected files:
  - [ ] `openhcs/io/base.py`
  - [ ] `openhcs/io/backend_registry.py`
  - [ ] `openhcs/microscopes/microscope_base.py`
  - [ ] `openhcs/runtime/zmq_base.py`
  - [ ] `openhcs/processing/backends/lib_registry/unified_registry.py`
  - [ ] `openhcs/processing/backends/experimental_analysis/format_registry.py`
  - [ ] All files using memory decorators (~50+ files)
- [ ] Delete extracted code:
  - [ ] `openhcs/core/auto_register_meta.py`
  - [ ] `openhcs/core/registry_discovery.py`
  - [ ] `openhcs/core/registry_cache.py`
  - [ ] `openhcs/core/memory/` (entire directory)
- [ ] Run full test suite
- [ ] Update documentation

### Phase 7: GitHub Setup ✅ COMPLETE

- [x] Create GitHub repository for `metaclass-registry`
- [x] Create GitHub repository for `arraybridge`
- [x] Create GitHub repository for `lazy-config`
- [x] Push initial code
- [ ] Enable GitHub Pages for all repos
- [ ] Set up branch protection
- [ ] Add repository descriptions and topics

### Phase 8: Publication ⏳ NOT STARTED

- [ ] Test PyPI upload (TestPyPI first)
- [ ] Publish `metaclass-registry` v0.1.0 to PyPI
- [ ] Publish `arraybridge` v0.1.0 to PyPI
- [ ] Create GitHub releases
- [ ] Write blog post: "Zero-Boilerplate Plugin Systems in Python"
- [ ] Write blog post: "Unified Array API: One Decorator to Rule Them All"
- [ ] Submit to JOSS (Journal of Open Source Software)

## Current Status

**Last Updated**: 2025-10-31

**Current Phase**: Phase 2 (Code Extraction)

**Next Steps**:
1. Extract code from OpenHCS to both packages
2. Remove OpenHCS-specific dependencies
3. Write comprehensive tests
4. Create documentation
5. Set up GitHub repositories
6. Publish to PyPI

## Notes

- Both packages reuse CI/CD infrastructure from OpenHCS
- Both packages use mkdocs for documentation (same as OpenHCS uses Sphinx)
- Both packages target Python 3.9+ (same as OpenHCS)
- Both packages use MIT license (same as OpenHCS)

