# plan_02_comprehensive_registry_framework.md

## Component: Comprehensive Registry Framework for OpenHCS

### Objective

Create a unified registry framework that covers ALL plugin and extension systems in OpenHCS, providing appropriate patterns for different use cases while maintaining consistency and discoverability.

**Vision:** Every plugin system in OpenHCS should use one of four well-defined registry patterns, with generic infrastructure supporting each pattern. Developers should know immediately which pattern to use for new plugin systems.

**Scope:** This plan addresses the ENTIRE registry ecosystem:
- Metaclass-based registries (handlers, backends, context providers)
- Service-based registries (functions, formats)
- Functional registries (widgets, configurations)
- Manual registries (ZMQ servers, pipeline steps)
- Generic discovery utilities (already exists)

---

### Plan

#### Phase 0: Registry Pattern Taxonomy

**Goal:** Document and classify all existing registry patterns in OpenHCS.

**The Four Registry Patterns:**

**Pattern A: Metaclass Auto-Registration**
- **Use Case:** 1:1 class-to-plugin mapping with automatic discovery
- **Mechanism:** Metaclass `__new__` registers classes on definition
- **Examples:**
  - MicroscopeHandlerMeta → MICROSCOPE_HANDLERS
  - StorageBackendMeta → STORAGE_BACKENDS
  - ContextProviderMeta → CONTEXT_PROVIDERS
- **When to use:** Single class per plugin, simple metadata, automatic registration desired
- **Infrastructure:** `AutoRegisterMeta` (to be created)

**Pattern B: Service-Based Registry**
- **Use Case:** Many-to-one mapping with complex metadata and aggregation
- **Mechanism:** Abstract base class + service class for discovery and aggregation
- **Examples:**
  - LibraryRegistryBase → RegistryService (574+ functions)
  - MicroscopeFormatRegistryBase → FormatRegistryService
- **When to use:** Multiple items per plugin, rich metadata, need aggregation
- **Infrastructure:** Already well-established, no changes needed

**Pattern C: Functional Registry**
- **Use Case:** Simple type-to-handler mappings without classes
- **Mechanism:** Dict mapping types to functions/handlers
- **Examples:**
  - WIDGET_REPLACEMENT_REGISTRY (type → widget creator)
  - CONFIGURATION_REGISTRY (type → configurator)
  - WIDGET_PLACEHOLDER_STRATEGIES (widget type → placeholder applier)
- **When to use:** Simple mappings, no state, functional programming style
- **Infrastructure:** Already working well, document best practices

**Pattern D: Manual Registration**
- **Use Case:** Explicit control needed, complex initialization, or rare plugins
- **Mechanism:** Explicit registration calls or factory functions
- **Examples:**
  - ZMQ servers (ABC-based, no auto-registration)
  - Pipeline steps (AbstractStep, no auto-discovery)
- **When to use:** Complex initialization, explicit control desired, or very few plugins
- **Infrastructure:** Document when manual is appropriate

---

#### Phase 1: Create Generic Metaclass Infrastructure

**File:** `openhcs/core/auto_register_meta.py` (new file, ~100 lines)

**Goal:** Provide reusable metaclass infrastructure for Pattern A systems.

**Components:**

1. **`RegistryConfig` dataclass** - Configuration for registration behavior
2. **`AutoRegisterMeta` metaclass** - Generic registration logic
3. **Helper functions** - Domain-specific key extractors
4. **Documentation** - When to use metaclass pattern vs others

**Design Principles:**
- Explicit configuration over magic
- Preserve domain-specific features
- Zero breaking changes
- Easy to understand and debug

**Deliverables:**
- [ ] `openhcs/core/auto_register_meta.py` implementation
- [ ] Unit tests with >90% coverage
- [ ] Documentation with usage examples
- [ ] Migration guide for existing metaclasses

---

#### Phase 2: Migrate Metaclass Registries (Pattern A)

**Goal:** Unify all 3 existing metaclass registries to use `AutoRegisterMeta`.

**2.1: Migrate MicroscopeHandlerMeta**
- File: `openhcs/microscopes/microscope_base.py`
- Complexity: Medium (has secondary registry for metadata handlers)
- Risk: Low (well-tested system)

**2.2: Migrate StorageBackendMeta**
- File: `openhcs/io/backend_registry.py`
- Complexity: Low (simple registration)
- Risk: Low (well-tested system)

**2.3: Migrate ContextProviderMeta**
- File: `openhcs/config_framework/lazy_factory.py`
- Complexity: Low (simple registration)
- Risk: Low (well-tested system)

**Success Criteria:**
- All existing plugins still register correctly
- No breaking changes to plugin implementations
- All tests pass without modification
- Code reduction: ~128 lines → ~125 lines (net ~3 lines saved)

---

#### Phase 3: Document Service-Based Pattern (Pattern B)

**Goal:** Document the service-based registry pattern as the canonical approach for many-to-one mappings.

**Existing Systems (Keep As-Is):**

**3.1: Function Registry**
- Files: `openhcs/processing/backends/lib_registry/`
- Pattern: LibraryRegistryBase + RegistryService
- Status: ✅ Working excellently, no changes needed
- Documentation: Add architecture docs explaining the pattern

**3.2: Format Registry**
- Files: `openhcs/processing/backends/experimental_analysis/`
- Pattern: MicroscopeFormatRegistryBase + FormatRegistryService
- Status: ✅ Working well, no changes needed
- Documentation: Reference as example of pattern

**Deliverables:**
- [ ] Architecture doc: "Service-Based Registry Pattern"
- [ ] When to use service pattern vs metaclass pattern
- [ ] Template for new service-based registries
- [ ] Examples from function and format registries

---

#### Phase 4: Document Functional Registry Pattern (Pattern C)

**Goal:** Document functional registry pattern and establish best practices.

**Existing Systems (Keep As-Is):**

**4.1: Widget Registries**
- Files: `openhcs/pyqt_gui/widgets/shared/widget_strategies.py`
- Registries: WIDGET_REPLACEMENT_REGISTRY, CONFIGURATION_REGISTRY
- Status: ✅ Working well, functional style appropriate
- Documentation: Document pattern and best practices

**4.2: Widget Creation Registries**
- Files: `openhcs/ui/shared/widget_creation_registry.py`
- Pattern: Framework-specific factory functions
- Status: ✅ Clean separation, no changes needed
- Documentation: Reference as example

**Best Practices to Document:**
- When to use dict-based registries
- Type safety considerations
- Registration timing (module import vs runtime)
- Testing strategies for functional registries

**Deliverables:**
- [ ] Architecture doc: "Functional Registry Pattern"
- [ ] Best practices guide
- [ ] Type hints and validation strategies
- [ ] Testing patterns for functional registries

---

#### Phase 5: Evaluate Manual Registration Systems (Pattern D)

**Goal:** Determine if manual systems should stay manual or adopt auto-registration.

**5.1: ZMQ Servers**
- File: `openhcs/runtime/zmq_base.py`
- Current: ABC-based, no auto-registration
- Question: Would metaclass registration help?
- Analysis needed: How many ZMQ server types exist? How often are new ones added?

**5.2: Pipeline Steps**
- File: `openhcs/core/steps/abstract.py`
- Current: AbstractStep ABC, no auto-discovery
- Question: Should custom step types be auto-discoverable?
- Analysis needed: Do users create custom steps? Would auto-discovery help?

**Decision Criteria:**
- Number of implementations (few → manual OK, many → auto-registration)
- Frequency of new implementations (rare → manual OK, common → auto-registration)
- Complexity of initialization (complex → manual, simple → auto-registration)
- User extensibility needs (user plugins → auto-registration helpful)

**Deliverables:**
- [ ] Analysis of ZMQ server implementations
- [ ] Analysis of pipeline step implementations
- [ ] Decision: Keep manual or migrate to Pattern A
- [ ] If migrating: Implementation plan
- [ ] If staying manual: Documentation of why manual is appropriate

---

#### Phase 6: Create Registry Framework Documentation

**Goal:** Comprehensive documentation of the entire registry ecosystem.

**6.1: Architecture Documentation**
- Document: `docs/architecture/registry-framework.md`
- Content:
  - Overview of all 4 patterns
  - Decision tree: Which pattern to use?
  - Examples from each pattern
  - Migration guides

**6.2: Developer Guidelines**
- Document: `docs/development/creating-plugins.md`
- Content:
  - How to create new plugin systems
  - Pattern selection guide
  - Code templates for each pattern
  - Testing strategies

**6.3: API Reference**
- Document: `docs/api/registry-framework.md`
- Content:
  - AutoRegisterMeta API
  - RegistryConfig options
  - Discovery utilities API
  - Best practices

**Deliverables:**
- [ ] Architecture documentation
- [ ] Developer guidelines
- [ ] API reference
- [ ] Code templates for each pattern
- [ ] Decision tree diagram (Mermaid)

---

### Findings

**Registry Systems Inventory (2025-10-30):**

**Pattern A: Metaclass Auto-Registration (3 systems)**
1. MicroscopeHandlerMeta → MICROSCOPE_HANDLERS (~60 lines)
2. StorageBackendMeta → STORAGE_BACKENDS (~53 lines)
3. ContextProviderMeta → CONTEXT_PROVIDERS (~15 lines)
- Total duplication: ~128 lines
- Opportunity: Unify with AutoRegisterMeta

**Pattern B: Service-Based Registry (2 systems)**
1. LibraryRegistryBase → RegistryService (574+ functions)
2. MicroscopeFormatRegistryBase → FormatRegistryService
- Status: Working excellently
- Action: Document pattern, no code changes

**Pattern C: Functional Registry (3+ systems)**
1. WIDGET_REPLACEMENT_REGISTRY (PyQt6)
2. CONFIGURATION_REGISTRY (PyQt6)
3. WIDGET_PLACEHOLDER_STRATEGIES (PyQt6)
4. Widget creation registries (Textual/PyQt6)
- Status: Working well
- Action: Document best practices

**Pattern D: Manual Registration (2+ systems)**
1. ZMQ servers (ABC-based)
2. Pipeline steps (AbstractStep)
- Status: Needs evaluation
- Action: Analyze if auto-registration would help

**Generic Discovery (1 system)**
- openhcs/core/registry_discovery.py
- Status: ✅ Already exists and works well
- Action: No changes needed, reference in docs

---

---

### Success Metrics

**Quantitative:**
- Reduce metaclass duplication: ~128 lines → ~125 lines (3 systems unified)
- Documentation coverage: 4 patterns fully documented
- Code templates: 1 template per pattern (4 total)
- Test coverage: >90% for new AutoRegisterMeta infrastructure

**Qualitative:**
- Clear decision tree for choosing registry patterns
- Consistent approach across all plugin systems
- Easy onboarding for new contributors
- Future plugin systems follow established patterns

**Risk Assessment:**
- Phase 1-2 (Metaclass): Low risk, well-isolated changes
- Phase 3-4 (Documentation): Zero risk, documentation only
- Phase 5 (Evaluation): Low risk, analysis phase
- Phase 6 (Docs): Zero risk, documentation only

**Timeline Estimate:**
- Phase 1: 2-3 days (AutoRegisterMeta implementation + tests)
- Phase 2: 2-3 days (Migrate 3 metaclasses + validation)
- Phase 3: 1 day (Document service pattern)
- Phase 4: 1 day (Document functional pattern)
- Phase 5: 1-2 days (Evaluate manual systems)
- Phase 6: 2-3 days (Comprehensive documentation)
- **Total: 9-13 days**

---

### Decision Points

**Before Phase 1:**
- ✅ Approve comprehensive approach vs narrow unification
- ✅ Confirm all 4 patterns are appropriate
- ✅ Agree on documentation scope

**After Phase 2:**
- Evaluate if metaclass unification was successful
- Decide if pattern is worth recommending for future systems

**After Phase 5:**
- Decide if ZMQ servers should adopt auto-registration
- Decide if pipeline steps should adopt auto-discovery
- Determine if any other systems need evaluation

**After Phase 6:**
- Review documentation completeness
- Validate decision tree with team
- Confirm templates are usable

---

### Checklist

**Phase 0: Taxonomy**
- [x] Identify all registry systems in codebase
- [x] Classify into 4 patterns
- [x] Document pattern characteristics
- [ ] Create pattern decision tree

**Phase 1: Metaclass Infrastructure**
- [ ] Design RegistryConfig dataclass
- [ ] Implement AutoRegisterMeta
- [ ] Write unit tests (>90% coverage)
- [ ] Write usage documentation
- [ ] Create migration guide

**Phase 2: Migrate Metaclasses**
- [ ] Migrate MicroscopeHandlerMeta
- [ ] Migrate StorageBackendMeta
- [ ] Migrate ContextProviderMeta
- [ ] Run full test suite
- [ ] Validate all plugins register correctly

**Phase 3: Document Service Pattern**
- [ ] Write architecture doc for service pattern
- [ ] Document when to use service vs metaclass
- [ ] Create service pattern template
- [ ] Reference function/format registries as examples

**Phase 4: Document Functional Pattern**
- [ ] Write architecture doc for functional pattern
- [ ] Document best practices
- [ ] Create functional pattern template
- [ ] Reference widget registries as examples

**Phase 5: Evaluate Manual Systems**
- [ ] Analyze ZMQ server implementations
- [ ] Analyze pipeline step implementations
- [ ] Make decision: manual vs auto-registration
- [ ] Document rationale for decision
- [ ] Create implementation plan if migrating

**Phase 6: Framework Documentation**
- [ ] Write registry-framework.md (architecture)
- [ ] Write creating-plugins.md (developer guide)
- [ ] Write API reference
- [ ] Create code templates (4 patterns)
- [ ] Create decision tree diagram
- [ ] Review with team

---

### Implementation Draft

#### Phase 1: AutoRegisterMeta Infrastructure ✅ COMPLETE

**File:** `openhcs/core/auto_register_meta.py` (300 lines)

Created generic metaclass infrastructure with:
- `RegistryConfig` dataclass for configuration
- `AutoRegisterMeta` metaclass with generic registration logic
- Helper functions: `extract_key_from_handler_suffix`, `extract_key_from_backend_suffix`
- Comprehensive docstrings and pattern selection guide

**Key Design Decisions:**
1. Configuration-driven approach (explicit over magic)
2. Supports all 3 existing patterns without breaking changes
3. Secondary registry support for metadata handlers
4. Skip-if-no-key behavior for optional registration
5. Debug logging for all registration events

**Next:** Migrate the 3 existing metaclasses to use this infrastructure


