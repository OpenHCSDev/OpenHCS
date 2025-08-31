Literal Includes Audit Methodology
====================================

**Perpetual documentation accuracy through systematic code-documentation synchronization.**

*Status: CANONICAL*  
*Applies to: All OpenHCS documentation with code examples*

Overview
--------

Traditional documentation suffers from the "documentation drift" problem - code examples become outdated as implementation evolves. OpenHCS eliminates this through systematic replacement of code examples with literal includes from the actual codebase.

This methodology ensures documentation remains perpetually accurate by making the codebase itself the single source of truth for all code examples.

Core Principles
---------------

Codebase as Single Source of Truth
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Principle**: Documentation never contains manually written code examples that duplicate implementation.

**Implementation**:

.. code-block:: rst

   .. literalinclude:: ../../../openhcs/core/lazy_config.py
      :language: python
      :lines: 320-326
      :caption: Method signature from actual implementation

**Rationale**: When implementation changes, documentation automatically reflects the change. No manual synchronization required.

Architectural Accuracy Over Syntactic Accuracy
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Principle**: Documentation should reflect architectural patterns and design decisions, even when method names change during refactoring.

**Example**: Documentation describing ``_preserve_lazy_structure_if_needed`` functionality points to ``rebuild_lazy_config_with_new_global_reference`` implementation - same logic, evolved API.

**Implementation Strategy**:

- Map conceptual functionality to actual implementation
- Update line numbers when refactoring occurs
- Preserve architectural explanations even when method names evolve

Logical Method Decomposition for Documentation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Principle**: Large methods that serve multiple conceptual purposes should be documented as separate logical sections, even when architecturally unified.

**Example**:

.. code-block:: python

   # Single architectural method (lines 394-463)
   def _create_field_level_hierarchy_provider(...):
       # Section 1: Auto-discovery (lines 402-405)
       all_field_paths = FieldPathDetector.find_all_field_paths_for_type(...)
       parent_types = FieldPathDetector.find_inheritance_relationships(...)
       
       # Section 2: Context detection (lines 410-420)
       current_config = context_provider() if context_provider else _get_current_config(...)
       
       # Section 3: Hierarchy building (lines 425-437)
       hierarchy_paths = []
       if current_field_path:
           hierarchy_paths.append(('current', current_field_path))
       
       # Section 4: Field resolution (lines 440-461)
       for field_name in inherited_fields | own_fields:
           # Complex resolution logic...

**Documentation Approach**:

.. code-block:: rst

   Auto-Discovery Phase
   ~~~~~~~~~~~~~~~~~~~~

   .. literalinclude:: ../../../openhcs/core/lazy_config.py
      :language: python
      :lines: 402-405
      :caption: Automatic hierarchy path discovery

   Context Detection Phase
   ~~~~~~~~~~~~~~~~~~~~~~~

   .. literalinclude:: ../../../openhcs/core/lazy_config.py
      :language: python
      :lines: 410-420
      :caption: PyQt app context detection logic

   Hierarchy Building Phase
   ~~~~~~~~~~~~~~~~~~~~~~~~

   .. literalinclude:: ../../../openhcs/core/lazy_config.py
      :language: python
      :lines: 425-437
      :caption: Dynamic hierarchy path construction

Audit Methodology
------------------

Phase 1: Systematic Code Example Identification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Objective**: Catalog all code examples in documentation that reference implementation.

**Process**:

1. **Scan for code blocks**: Find all ``.. code-block:: python`` directives
2. **Classify examples**:

   - **Implementation references**: Examples showing actual method signatures, class definitions
   - **Usage examples**: Examples showing how to call actual functions
   - **Conceptual examples**: Pseudo-code illustrating patterns (keep as-is)

3. **Create mapping document**: File path, line range, description, implementation location

**Tools**:

.. code-block:: bash

   # Find all code blocks in documentation
   find docs/ -name "*.rst" -exec grep -l "code-block:: python" {} \;

   # Extract method references
   grep -r "def [a-zA-Z_]" docs/source/architecture/ | grep -v "literalinclude"

Phase 2: Implementation Verification
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Objective**: Verify each code example references actual, existing implementation.

**Process**:

1. **Method existence check**: Confirm referenced methods exist in current codebase
2. **Functionality mapping**: For renamed methods, verify functionality equivalence
3. **Line number verification**: Confirm line ranges contain expected code
4. **Phantom method detection**: Identify examples referencing non-existent methods

**Verification Script Pattern**:

.. code-block:: python

   def verify_method_exists(file_path: str, method_name: str) -> bool:
       """Verify method exists in specified file."""
       with open(file_path) as f:
           content = f.read()
       return f"def {method_name}" in content

   def verify_line_range_content(file_path: str, start: int, end: int, expected_pattern: str) -> bool:
       """Verify line range contains expected functionality."""
       with open(file_path) as f:
           lines = f.readlines()
       content = ''.join(lines[start-1:end])
       return expected_pattern in content

Phase 3: Systematic Replacement
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Objective**: Replace verified code examples with literal includes.

**Process**:

1. **High priority first**: Core implementation methods, class definitions
2. **Batch replacement**: Group related examples for efficient processing
3. **Build verification**: Test documentation build after each batch
4. **Cross-reference updates**: Update internal documentation links

**Replacement Template**:

.. code-block:: rst

   .. literalinclude:: ../../../{file_path}
      :language: python
      :lines: {start_line}-{end_line}
      :caption: {descriptive_caption_with_source_reference}

Phase 4: Perpetual Maintenance
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Objective**: Maintain accuracy as codebase evolves.

**Process**:

1. **Build integration**: Documentation build fails if literal includes reference non-existent lines
2. **Refactoring protocol**: When moving/renaming methods, update corresponding literal includes
3. **Review integration**: Code reviews must verify literal include accuracy for changed files
4. **Automated verification**: CI checks that verify literal includes point to expected functionality

OpenHCS-Specific Implementation Guidelines
------------------------------------------

Fail-Loud Documentation
~~~~~~~~~~~~~~~~~~~~~~~

**Principle**: Documentation build should fail immediately when literal includes become invalid.

**Implementation**: Use Sphinx's strict mode and verify all literal includes during CI.

Mathematical Simplification Applied to Documentation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Principle**: Eliminate duplicate explanations by referencing single implementation source.

**Before**:

.. code-block:: rst

   # Multiple explanations of the same concept
   Configuration Resolution (in config.rst)
   Lazy Field Resolution (in lazy_config.rst)  
   Thread-Local Context (in context.rst)

**After**:

.. code-block:: rst

   # Single implementation with multiple documentation perspectives
   .. literalinclude:: ../../../openhcs/core/lazy_config.py
      :lines: 126-129
      :caption: Core resolution logic (referenced from multiple docs)

Architectural Coherence Over Implementation Details
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Principle**: Document architectural patterns and design decisions, not implementation minutiae.

**Focus Areas**:

- **Why** code is structured a certain way
- **How** patterns solve architectural problems  
- **When** to use specific approaches
- **What** trade-offs were made

**Avoid**:

- Line-by-line code walkthroughs
- Implementation details that change frequently
- Language-specific syntax explanations

Breadth-First Documentation Structure
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Principle**: Organize documentation from architectural concepts to implementation details.

**Structure**:

1. **Architectural overview**: Why the system exists, what problems it solves
2. **Core patterns**: Key design patterns and their rationale
3. **Implementation examples**: Literal includes showing actual code
4. **Usage patterns**: How to use the implemented functionality
5. **Integration details**: How components work together

Advanced Techniques
--------------------

Phantom Method Resolution
~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Documentation references methods that were renamed or refactored during development.

**Solution**: Map phantom method functionality to actual implementation.

**Process**:

1. **Identify phantom methods**: Methods referenced in documentation but not found in codebase
2. **Functionality analysis**: Determine what the phantom method was supposed to do
3. **Implementation mapping**: Find actual code that performs the same functionality
4. **Line range verification**: Confirm the line numbers point to equivalent logic

**Example**:

.. code-block:: rst

   # Documentation references phantom method
   def _preserve_lazy_structure_if_needed(self, field_name: str, value: Any) -> Any:

   # Maps to actual implementation
   .. literalinclude:: ../../../openhcs/core/lazy_config.py
      :lines: 544-582
      :caption: Field state preservation (rebuild_lazy_config_with_new_global_reference)

Logical Method Decomposition
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Large architectural methods serve multiple conceptual purposes but cannot be split for architectural reasons.

**Solution**: Document logical sections as separate conceptual units.

**Technique**:

.. code-block:: rst

   Complex Provider Function
   ~~~~~~~~~~~~~~~~~~~~~~~~~

   This function performs four distinct logical operations:

   **Phase 1: Auto-Discovery**

   .. literalinclude:: ../../../openhcs/core/lazy_config.py
      :lines: 402-405
      :caption: Automatic hierarchy path discovery

   **Phase 2: Context Detection**

   .. literalinclude:: ../../../openhcs/core/lazy_config.py
      :lines: 410-420
      :caption: PyQt application context detection

   **Phase 3: Hierarchy Construction**

   .. literalinclude:: ../../../openhcs/core/lazy_config.py
      :lines: 425-437
      :caption: Dynamic hierarchy path building

   **Phase 4: Field Resolution**

   .. literalinclude:: ../../../openhcs/core/lazy_config.py
      :lines: 440-461
      :caption: Field-level inheritance resolution

Architectural Pattern Documentation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Principle**: Document the architectural reasoning behind implementation choices.

**Template**:

.. code-block:: rst

   Pattern: {Pattern Name}
   ~~~~~~~~~~~~~~~~~~~~~~~

   **Problem**: {What architectural problem does this solve?}

   **Solution**: {How does the implementation address the problem?}

   **Implementation**:

   .. literalinclude:: ../../../{source_file}
      :lines: {start}-{end}
      :caption: {Pattern implementation}

   **Rationale**: {Why this approach over alternatives?}

   **Trade-offs**: {What are the costs and benefits?}

Cross-Reference Accuracy
~~~~~~~~~~~~~~~~~~~~~~~~~

**Problem**: Documentation cross-references become stale when methods are renamed or moved.

**Solution**: Use literal includes for cross-references to maintain accuracy.

**Implementation**:

.. code-block:: rst

   # Instead of manual cross-reference
   See the `_create_lazy_dataclass` method for implementation details.

   # Use literal include reference
   The lazy dataclass creation process:

   .. literalinclude:: ../../../openhcs/core/lazy_config.py
      :lines: 253-299
      :caption: Core lazy dataclass creation (_create_lazy_dataclass_unified)

Integration with OpenHCS Development Workflow
----------------------------------------------

Code Review Protocol
~~~~~~~~~~~~~~~~~~~~~

**Requirement**: All code changes that affect documented functionality must update corresponding literal includes.

**Process**:

1. **Identify affected documentation**: Which docs reference the changed code?
2. **Verify line numbers**: Do literal includes still point to correct functionality?
3. **Update captions**: Do descriptions still accurately reflect the code?
4. **Test documentation build**: Ensure all literal includes resolve correctly

Refactoring Safety Net
~~~~~~~~~~~~~~~~~~~~~~

**Principle**: Documentation serves as a safety net during refactoring by exposing all usage patterns.

**Benefits**:

- **Visibility**: See all places where code is referenced
- **Impact assessment**: Understand documentation implications of changes
- **Architectural coherence**: Ensure refactoring preserves documented patterns
- **Regression prevention**: Documentation build fails if refactoring breaks examples

Continuous Integration Integration
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

**Requirements**:

.. code-block:: yaml

   # Documentation verification in CI
   documentation_check:
     - verify_literal_includes_exist
     - verify_line_ranges_contain_expected_content
     - build_documentation_strict_mode
     - check_cross_reference_accuracy

**Failure Modes**:

- **Missing files**: Literal include references non-existent file
- **Invalid line ranges**: Line numbers exceed file length
- **Empty ranges**: Line range contains no code
- **Functionality mismatch**: Code at line range doesn't match description

Quality Metrics
---------------

Quantitative Metrics
~~~~~~~~~~~~~~~~~~~~~

**Documentation Accuracy Rate**:

.. code-block:: text

   Accuracy = (Valid Literal Includes / Total Code Examples) × 100
   Target: >95% for core architecture docs

**Implementation Coverage**:

.. code-block:: text

   Coverage = (Documented Public Methods / Total Public Methods) × 100
   Target: >80% for core modules

**Maintenance Efficiency**:

.. code-block:: text

   Efficiency = Development Time / Documentation Update Time
   Target: <5% overhead

Qualitative Indicators
~~~~~~~~~~~~~~~~~~~~~~~

**Developer Experience**:

- Developers trust documentation examples to work
- Code reviews catch documentation inconsistencies
- Refactoring confidence increases due to documentation safety net

**Architectural Clarity**:

- Design decisions are clearly explained and justified
- Implementation patterns are consistently documented
- Complex logic is broken down into understandable sections

**Codebase Health**:

- Documentation pressure improves code quality
- Architectural patterns become more consistent
- Complex methods are naturally decomposed for documentability

Benefits
--------

For Developers
~~~~~~~~~~~~~~~

1. **Guaranteed accuracy**: Code examples always reflect current implementation
2. **Reduced maintenance**: No manual synchronization of code and documentation
3. **Architectural insight**: Documentation explains design decisions, not just syntax
4. **Refactoring safety**: Documentation automatically updates with code changes

For Users
~~~~~~~~~

1. **Reliable examples**: All code examples are guaranteed to work
2. **Current information**: Documentation never lags behind implementation
3. **Architectural understanding**: Learn not just how, but why
4. **Consistent patterns**: Same implementation referenced across multiple contexts

For Codebase Health
~~~~~~~~~~~~~~~~~~~

1. **Perpetual audit**: Documentation serves as continuous code review
2. **Architectural documentation**: Forces clear explanation of design decisions
3. **Implementation visibility**: Complex logic must be documentable to be maintainable
4. **Quality pressure**: Poor code becomes obvious when documented

Implementation Checklist
-------------------------

- [ ] Catalog all code examples in documentation
- [ ] Verify each example against current implementation
- [ ] Create systematic mapping of examples to source code
- [ ] Replace examples with literal includes (high priority first)
- [ ] Integrate literal include verification into CI pipeline
- [ ] Establish refactoring protocol for updating documentation
- [ ] Document architectural patterns and design rationale
- [ ] Set up automated accuracy metrics and monitoring

This methodology transforms documentation from a maintenance burden into a perpetual code audit system that ensures architectural coherence and implementation accuracy.
