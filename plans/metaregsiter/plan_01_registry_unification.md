# plan_01_registry_unification.md

## Component: Generic Metaclass Registry Framework

### Objective

Create a generic `AutoRegisterMeta` metaclass to unify the registration patterns used by `MicroscopeHandlerMeta` and `StorageBackendMeta`, reducing code duplication while preserving domain-specific features.

**Scope:** This plan focuses ONLY on metaclass unification. It does NOT touch:
- `openhcs/core/registry_discovery.py` (already exists and works well)
- Function registry system (uses appropriate service pattern)
- Discovery utilities (already generic and working)

**Value Proposition:**
- Unify **3 existing metaclass registries** (not just 2!):
  - MicroscopeHandlerMeta → MICROSCOPE_HANDLERS
  - StorageBackendMeta → STORAGE_BACKENDS
  - ContextProviderMeta → CONTEXT_PROVIDERS
- Reduce ~128 lines of duplicated metaclass code across 3 systems
- Provide reusable pattern for future plugin systems (ZMQ servers, custom steps, etc.)
- Maintain all existing functionality and domain-specific features
- Zero breaking changes to existing code

---

### Plan

#### Phase 1: Create Generic Metaclass (Minimal Viable Implementation)

**File:** `openhcs/core/auto_register_meta.py` (new file, ~80 lines)

**Components:**

1. **`RegistryConfig` dataclass** - Configuration for registration behavior
   ```python
   @dataclass
   class RegistryConfig:
       """Configuration for auto-registration behavior."""
       registry_dict: Dict[str, Type]  # Target registry (e.g., MICROSCOPE_HANDLERS)
       key_attribute: str              # Attribute name for registry key (e.g., '_microscope_type')
       key_extractor: Optional[Callable[[str, Type], str]] = None  # Function to derive key from class name
       skip_if_no_key: bool = False    # Skip registration if key is None
       secondary_registries: Optional[List[Tuple[Dict, Callable]]] = None  # Additional registries
   ```

2. **`AutoRegisterMeta` metaclass** - Generic registration logic
   ```python
   class AutoRegisterMeta(ABCMeta):
       """Generic metaclass for automatic class registration."""
       
       def __new__(mcs, name, bases, attrs, registry_config: RegistryConfig):
           new_class = super().__new__(mcs, name, bases, attrs)
           
           # Only register concrete classes (not abstract)
           if getattr(new_class, '__abstractmethods__', None):
               return new_class
           
           # Get or derive registry key
           registry_key = getattr(new_class, registry_config.key_attribute, None)
           
           if registry_key is None and registry_config.key_extractor:
               registry_key = registry_config.key_extractor(name, new_class)
           
           if registry_key is None and registry_config.skip_if_no_key:
               return new_class  # Skip registration
           
           # Register in primary registry
           registry_config.registry_dict[registry_key] = new_class
           setattr(new_class, registry_config.key_attribute, registry_key)
           
           # Register in secondary registries if configured
           if registry_config.secondary_registries:
               for secondary_dict, extractor_func in registry_config.secondary_registries:
                   secondary_key = extractor_func(new_class)
                   if secondary_key is not None:
                       secondary_dict[secondary_key] = extractor_func(new_class, return_value=True)
           
           logger.debug(f"Auto-registered {name} as '{registry_key}'")
           return new_class
   ```

3. **Helper functions** - Domain-specific key extractors
   ```python
   def extract_handler_type(class_name: str, cls: Type) -> str:
       """Extract microscope type from handler class name."""
       if class_name.endswith('Handler'):
           return class_name[:-7].lower()
       return class_name.lower()
   
   def extract_backend_type(class_name: str, cls: Type) -> Optional[str]:
       """Extract backend type from _backend_type attribute."""
       return getattr(cls, '_backend_type', None)
   ```

**Design Decisions:**
- Use `registry_config` as metaclass parameter (passed via `__init_subclass__` or class creation)
- Preserve all existing behavior (key extraction, secondary registries, skip logic)
- Keep it simple: ~80 lines total, easy to understand
- No magic: Explicit configuration over convention

---

#### Phase 2: Migrate MicroscopeHandlerMeta

**File:** `openhcs/microscopes/microscope_base.py`

**Changes:**

1. **Import generic metaclass:**
   ```python
   from openhcs.core.auto_register_meta import AutoRegisterMeta, RegistryConfig, extract_handler_type
   ```

2. **Create configuration:**
   ```python
   # Configuration for microscope handler registration
   _HANDLER_REGISTRY_CONFIG = RegistryConfig(
       registry_dict=MICROSCOPE_HANDLERS,
       key_attribute='_microscope_type',
       key_extractor=extract_handler_type,
       skip_if_no_key=False,
       secondary_registries=[
           (METADATA_HANDLERS, lambda cls: (
               getattr(cls, '_microscope_type', None),
               getattr(cls, '_metadata_handler_class', None)
           ))
       ]
   )
   ```

3. **Replace MicroscopeHandlerMeta:**
   ```python
   # Old: class MicroscopeHandlerMeta(ABCMeta): ...
   # New:
   class MicroscopeHandlerMeta(AutoRegisterMeta):
       """Metaclass for automatic registration of microscope handlers."""
       
       def __new__(mcs, name, bases, attrs):
           return super().__new__(mcs, name, bases, attrs, 
                                  registry_config=_HANDLER_REGISTRY_CONFIG)
   ```

**Validation:**
- All existing handlers still register correctly
- Metadata handler registration still works
- No changes to handler implementations needed
- Tests pass without modification

---

#### Phase 3: Migrate StorageBackendMeta

**File:** `openhcs/io/backend_registry.py`

**Changes:**

1. **Import generic metaclass:**
   ```python
   from openhcs.core.auto_register_meta import AutoRegisterMeta, RegistryConfig
   ```

2. **Create configuration:**
   ```python
   # Configuration for storage backend registration
   _BACKEND_REGISTRY_CONFIG = RegistryConfig(
       registry_dict=STORAGE_BACKENDS,
       key_attribute='_backend_type',
       key_extractor=None,  # Requires explicit _backend_type
       skip_if_no_key=True,  # Skip if no _backend_type set
       secondary_registries=None
   )
   ```

3. **Replace StorageBackendMeta:**
   ```python
   # Old: class StorageBackendMeta(ABCMeta): ...
   # New:
   class StorageBackendMeta(AutoRegisterMeta):
       """Metaclass for automatic registration of storage backends."""

       def __new__(mcs, name, bases, attrs):
           return super().__new__(mcs, name, bases, attrs,
                                  registry_config=_BACKEND_REGISTRY_CONFIG)
   ```

**Validation:**
- All existing backends still register correctly
- Skip logic for missing `_backend_type` still works
- No changes to backend implementations needed
- Tests pass without modification

---

#### Phase 4: Migrate ContextProviderMeta

**File:** `openhcs/config_framework/lazy_factory.py`

**Changes:**

1. **Import generic metaclass:**
   ```python
   from openhcs.core.auto_register_meta import AutoRegisterMeta, RegistryConfig
   ```

2. **Create configuration:**
   ```python
   # Configuration for context provider registration
   _CONTEXT_PROVIDER_REGISTRY_CONFIG = RegistryConfig(
       registry_dict=CONTEXT_PROVIDERS,
       key_attribute='_context_type',
       key_extractor=None,  # Requires explicit _context_type
       skip_if_no_key=True,  # Skip if no _context_type set
       secondary_registries=None
   )
   ```

3. **Replace ContextProviderMeta:**
   ```python
   # Old: class ContextProviderMeta(ABCMeta): ...
   # New:
   class ContextProviderMeta(AutoRegisterMeta):
       """Metaclass for automatic registration of context provider classes."""

       def __new__(mcs, name, bases, attrs):
           return super().__new__(mcs, name, bases, attrs,
                                  registry_config=_CONTEXT_PROVIDER_REGISTRY_CONFIG)
   ```

**Validation:**
- All existing context providers still register correctly
- Lazy configuration system still works
- No changes to provider implementations needed
- Tests pass without modification

---

#### Phase 5: Testing & Validation

**Test Coverage:**

1. **Unit tests for `AutoRegisterMeta`** (`tests/core/test_auto_register_meta.py`)
   - Test basic registration
   - Test key extraction (both explicit and derived)
   - Test skip logic
   - Test secondary registries
   - Test abstract class exclusion

2. **Integration tests**
   - Verify all microscope handlers still register
   - Verify all storage backends still register
   - Verify metadata handler registration
   - Verify discovery services still work

3. **Regression tests**
   - Run full test suite
   - Verify no breaking changes
   - Check import times (should be unchanged)

**Success Criteria:**
- All existing tests pass without modification
- New tests achieve >90% coverage of `auto_register_meta.py`
- No performance regression
- No breaking changes to public APIs

---

### Findings

**Codebase Validation (2025-10-30):**

1. **`openhcs/core/registry_discovery.py` already exists** - Generic discovery utilities are implemented and working. No changes needed.

2. **Two patterns coexist appropriately:**
   - Metaclass pattern: Handlers, backends, context providers (1:1 class-to-plugin mapping)
   - Service pattern: Functions (many-to-one, complex metadata)
   - Both patterns are appropriate for their domains

3. **THREE metaclass registries found** (not just two!):
   - `MicroscopeHandlerMeta` → `MICROSCOPE_HANDLERS` (~60 lines)
   - `StorageBackendMeta` → `STORAGE_BACKENDS` (~53 lines)
   - `ContextProviderMeta` → `CONTEXT_PROVIDERS` (~15 lines)
   - **Total duplication: ~128 lines**

4. **Domain-specific features to preserve:**
   - Microscope handlers: Metadata handler auto-discovery, name-based key extraction
   - Storage backends: Optional registration (skip if no `_backend_type`)
   - Context providers: Simple registration by `_context_type`

5. **Function registry should NOT be migrated** - Service pattern is more appropriate for:
   - Multiple functions per library
   - Complex metadata (FunctionMetadata with 8 fields)
   - Aggregation across libraries (574+ functions)

6. **Future plugin systems that could benefit:**
   - ZMQ servers (currently manual ABC pattern)
   - Custom pipeline step types
   - File format handlers
   - User-defined analysis modules

---

### Implementation Draft

(Code will be written here after smell loop approval)

---

### Migration Checklist

**Pre-Migration:**
- [ ] Review this plan with team
- [ ] Confirm value proposition justifies abstraction cost
- [ ] Get approval via smell loop

**Phase 1: Generic Metaclass**
- [ ] Create `openhcs/core/auto_register_meta.py`
- [ ] Implement `RegistryConfig` dataclass
- [ ] Implement `AutoRegisterMeta` metaclass
- [ ] Implement helper functions
- [ ] Write unit tests

**Phase 2: Microscope Handlers**
- [ ] Update `openhcs/microscopes/microscope_base.py`
- [ ] Create `_HANDLER_REGISTRY_CONFIG`
- [ ] Replace `MicroscopeHandlerMeta` implementation
- [ ] Run handler tests
- [ ] Verify all handlers register correctly

**Phase 3: Storage Backends**
- [ ] Update `openhcs/io/backend_registry.py`
- [ ] Create `_BACKEND_REGISTRY_CONFIG`
- [ ] Replace `StorageBackendMeta` implementation
- [ ] Run backend tests
- [ ] Verify all backends register correctly

**Phase 4: Context Providers**
- [ ] Update `openhcs/config_framework/lazy_factory.py`
- [ ] Create `_CONTEXT_PROVIDER_REGISTRY_CONFIG`
- [ ] Replace `ContextProviderMeta` implementation
- [ ] Run lazy config tests
- [ ] Verify all context providers register correctly

**Phase 5: Validation**
- [ ] Run full test suite
- [ ] Check import times
- [ ] Verify no breaking changes
- [ ] Update documentation if needed

**Post-Migration:**
- [ ] Archive this plan to `plans/metaregsiter/archive/`
- [ ] Document pattern in architecture docs
- [ ] Create template for future metaclass-based plugins

---

### Open Questions

1. **Is the abstraction worth it?**
   - Saves ~30-40 lines of code
   - Adds one layer of indirection
   - Makes pattern more reusable for future plugins
   - **Decision needed:** Proceed or document existing patterns instead?

2. **Should we keep domain-specific metaclasses?**
   - Option A: Keep thin wrappers (MicroscopeHandlerMeta, StorageBackendMeta) that use AutoRegisterMeta
   - Option B: Use AutoRegisterMeta directly with configuration
   - **Recommendation:** Option A (preserves clear naming, easier to understand)

3. **Future plugin systems:**
   - If we create this, what future plugins would use it?
   - ZMQ servers? (currently manual registration)
   - User-defined plugins?
   - **Action:** Identify concrete use cases before proceeding

---

### Success Metrics

**Quantitative:**
- Code reduction: ~128 lines removed from 3 duplicated metaclasses
- Framework cost: ~80 lines added for generic implementation
- Thin wrappers: ~45 lines (3 × 15 lines each)
- Net change: ~3 lines saved immediately
- Future savings: ~30-40 lines per new metaclass-based plugin system
- **With 3 existing systems + future plugins, ROI is positive**

**Qualitative:**
- Pattern consistency: Easier to create new metaclass-based plugins
- Maintainability: Single source of truth for registration logic
- Clarity: May be harder to understand (indirection cost)

**Risk Assessment:**
- **Low risk:** No breaking changes, existing code continues to work
- **Medium complexity:** Metaclass programming requires careful testing
- **Reversible:** Can revert to original implementation if issues arise

