# GitHub Project Setup Guide

## Creating the Multi-Repository Project

### Step 1: Create GitHub Project

1. Go to https://github.com/users/trissim/projects
2. Click "New project"
3. Choose "Board" view
4. Name: **"Package Extraction: metaclass-registry & arraybridge"**
5. Description: **"Extract metaclass registry and memory type systems from OpenHCS into standalone PyPI packages"**

### Step 2: Configure Project Columns

Create the following columns:

1. **📋 Backlog** - Tasks not yet started
2. **🏗️ In Progress** - Currently working on
3. **✅ Done** - Completed tasks
4. **🚫 Blocked** - Waiting on something

### Step 3: Add Issues/Tasks

Create issues in the appropriate repositories and add them to the project:

#### Repository: `trissim/metaclass-registry` (to be created)

**Issue #1: Extract core metaclass code from OpenHCS**
```markdown
## Description
Extract `AutoRegisterMeta` and related code from OpenHCS to this package.

## Tasks
- [ ] Extract `openhcs/core/auto_register_meta.py` → `src/metaclass_registry/core.py`
- [ ] Extract registry discovery code → `src/metaclass_registry/discovery.py`
- [ ] Extract cache manager → `src/metaclass_registry/cache.py`
- [ ] Extract helper classes → `src/metaclass_registry/helpers.py`
- [ ] Remove OpenHCS-specific dependencies
- [ ] Add comprehensive type hints
- [ ] Add comprehensive docstrings

## Dependencies
None

## Labels
`extraction`, `phase-2`
```

**Issue #2: Write comprehensive tests**
```markdown
## Description
Write tests for all metaclass-registry functionality with >90% coverage.

## Tasks
- [ ] `tests/test_core.py` - Test AutoRegisterMeta
- [ ] `tests/test_discovery.py` - Test LazyDiscoveryDict
- [ ] `tests/test_cache.py` - Test RegistryCacheManager
- [ ] `tests/test_helpers.py` - Test SecondaryRegistry
- [ ] `tests/test_integration.py` - Integration tests
- [ ] Achieve >90% coverage

## Dependencies
Blocked by #1

## Labels
`testing`, `phase-3`
```

**Issue #3: Write documentation**
```markdown
## Description
Create comprehensive documentation for metaclass-registry.

## Tasks
- [ ] `docs/index.md` - Home page
- [ ] `docs/quickstart.md` - Quick start guide
- [ ] `docs/patterns.md` - Pattern guide
- [ ] `docs/api.md` - API reference
- [ ] `docs/examples/` - Example scripts

## Dependencies
Blocked by #1

## Labels
`documentation`, `phase-4`
```

**Issue #4: Publish to PyPI**
```markdown
## Description
Publish metaclass-registry v0.1.0 to PyPI.

## Tasks
- [ ] Test on TestPyPI
- [ ] Create GitHub release
- [ ] Publish to PyPI
- [ ] Verify installation works

## Dependencies
Blocked by #2, #3

## Labels
`publication`, `phase-8`
```

#### Repository: `trissim/arraybridge` (to be created)

**Issue #1: Extract memory type system from OpenHCS**
```markdown
## Description
Extract entire memory type system from OpenHCS to this package.

## Tasks
- [ ] Extract `openhcs/core/memory/` → `src/arraybridge/`
- [ ] Extract `MemoryType` enum from `openhcs/constants/constants.py`
- [ ] Extract `optional_import` from `openhcs/core/utils.py`
- [ ] Remove OpenHCS-specific dependencies
- [ ] Make 3D enforcement optional (add `enforce_3d` parameter)
- [ ] Add comprehensive type hints
- [ ] Add comprehensive docstrings

## Dependencies
None

## Labels
`extraction`, `phase-2`
```

**Issue #2: Write comprehensive tests**
```markdown
## Description
Write tests for all arraybridge functionality with >90% coverage.

## Tasks
- [ ] `tests/test_converters.py` - Test all 36 conversion pairs
- [ ] `tests/test_decorators.py` - Test all decorators
- [ ] `tests/test_stack_utils.py` - Test stack/unstack
- [ ] `tests/test_oom_recovery.py` - Test OOM handling
- [ ] `tests/test_integration.py` - Integration tests
- [ ] Achieve >90% coverage

## Dependencies
Blocked by #1

## Labels
`testing`, `phase-3`
```

**Issue #3: Write documentation**
```markdown
## Description
Create comprehensive documentation for arraybridge.

## Tasks
- [ ] `docs/index.md` - Home page
- [ ] `docs/quickstart.md` - Quick start guide
- [ ] `docs/frameworks.md` - Framework support matrix
- [ ] `docs/decorators.md` - Decorator guide
- [ ] `docs/api.md` - API reference
- [ ] `docs/examples/` - Example scripts

## Dependencies
Blocked by #1

## Labels
`documentation`, `phase-4`
```

**Issue #4: Publish to PyPI**
```markdown
## Description
Publish arraybridge v0.1.0 to PyPI.

## Tasks
- [ ] Test on TestPyPI
- [ ] Create GitHub release
- [ ] Publish to PyPI
- [ ] Verify installation works

## Dependencies
Blocked by #2, #3

## Labels
`publication`, `phase-8`
```

#### Repository: `trissim/openhcs` (existing)

**Issue: Migrate OpenHCS to use extracted packages**
```markdown
## Description
Update OpenHCS to depend on metaclass-registry and arraybridge packages.

## Tasks
- [ ] Add `metaclass-registry>=0.1.0` to `pyproject.toml`
- [ ] Add `arraybridge>=0.1.0` to `pyproject.toml`
- [ ] Update imports in ~60+ files
- [ ] Delete extracted code from OpenHCS
- [ ] Run full test suite
- [ ] Update documentation
- [ ] Merge `metaregister` branch to `main`

## Dependencies
Blocked by metaclass-registry#4, arraybridge#4

## Labels
`migration`, `phase-6`, `breaking-change`
```

### Step 4: Add Milestones

Create milestones for each phase:

1. **Phase 1: Package Structure** ✅ COMPLETE
2. **Phase 2: Code Extraction** (Due: 2025-11-07)
3. **Phase 3: Testing** (Due: 2025-11-14)
4. **Phase 4: Documentation** (Due: 2025-11-21)
5. **Phase 5: CI/CD Setup** ✅ COMPLETE
6. **Phase 6: OpenHCS Migration** (Due: 2025-11-28)
7. **Phase 7: GitHub Setup** (Due: 2025-11-30)
8. **Phase 8: Publication** (Due: 2025-12-05)

### Step 5: Link Repositories

In the project settings, link all three repositories:
- `trissim/metaclass-registry`
- `trissim/arraybridge`
- `trissim/openhcs`

## Quick Commands

### Create GitHub Repositories

```bash
# Create metaclass-registry repo
gh repo create trissim/metaclass-registry --public \
  --description "Zero-boilerplate metaclass-driven plugin registry system" \
  --homepage "https://metaclass-registry.readthedocs.io"

# Create arraybridge repo
gh repo create trissim/arraybridge --public \
  --description "Unified API for NumPy, CuPy, PyTorch, TensorFlow, JAX, and pyclesperanto" \
  --homepage "https://arraybridge.readthedocs.io"
```

### Push Initial Code

```bash
# Push metaclass-registry
cd /home/ts/code/projects/metaclass-registry
git remote add origin https://github.com/trissim/metaclass-registry.git
git branch -M main
git push -u origin main

# Push arraybridge
cd /home/ts/code/projects/arraybridge
git remote add origin https://github.com/trissim/arraybridge.git
git branch -M main
git push -u origin main
```

### Enable GitHub Pages

For both repos, go to Settings → Pages and set:
- Source: GitHub Actions
- This will enable automatic documentation deployment

## Project Board View

```
📋 Backlog                    🏗️ In Progress              ✅ Done                      🚫 Blocked
─────────────────────────────────────────────────────────────────────────────────────────────────
                              metaclass-registry#1        Phase 1: Structure           
                              (Code Extraction)           Phase 5: CI/CD               
                                                                                       
arraybridge#2                                                                          arraybridge#3
(Testing)                                                                              (Docs - blocked by #1)

metaclass-registry#2                                                                   metaclass-registry#4
(Testing)                                                                              (PyPI - blocked by #2,#3)

openhcs#XXX                                                                            arraybridge#4
(Migration)                                                                            (PyPI - blocked by #2,#3)
```

## Notes

- Use GitHub Project automation to move cards between columns
- Link PRs to issues using "Closes #X" in PR description
- Use labels to filter by phase, repository, and type
- Set up notifications for project updates

