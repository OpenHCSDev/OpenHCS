# OpenHCS Concepts Documentation Plan
**User-Facing Mental Models with Implementation-Priming Prose and Python Object References**

*Status: DRAFT PLAN*
*Target: Eliminate "expert curse" through progressive mental model building*

## Overview

This plan addresses the critical gap in OpenHCS documentation: the lack of user-facing conceptual explanations that build mental models for understanding the system. Following the literal includes audit methodology, all concepts will use Python object references with implementation-priming prose to ensure perpetual accuracy.

## Current State Analysis

### ✅ What Exists and Works
- `domain_fundamentals.rst` - Excellent scientific problem explanation
- `pipelines_and_steps.rst` - Good basic pipeline concepts
- `building_intuition.rst` - Some mental models for basic usage

### ❌ Critical Gaps (Expert Curse Problems)
1. **No Configuration System Mental Model** - Users encounter lazy configs immediately but have no framework
2. **No Visual Programming Explanation** - UI behavior (placeholders, inheritance) unexplained
3. **No Mathematical Foundations** - Why OpenHCS approaches problems differently
4. **No Memory/Type System Concepts** - Automatic GPU conversion uniqueness
5. **No Metaprogramming Rationale** - Why complexity exists and is justified

## Proposed Documentation Structure

### Phase 1: Foundational Mental Models
**Target: Build conceptual framework before technical details**

#### 1. `mathematical_foundations.rst`
**Problem**: Users don't understand why OpenHCS uses mathematical thinking for image processing
**Mental Model**: Configuration spaces as mathematical objects with transformations
**Key Concepts**:
- Why traditional tools fail at scale
- Configuration hierarchies as mathematical relationships
- Type systems as mathematical constraints

**Python Object References**:
- `:py:class:`~openhcs.core.config.GlobalPipelineConfig` - Mathematical structure example
- `:py:func:`~openhcs.core.lazy_config.LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy` - Hierarchy construction

#### 2. `configuration_as_mathematics.rst`
**Problem**: Users see config forms but don't understand the mathematical relationships
**Mental Model**: Configurations as mathematical spaces with inheritance operators
**Key Concepts**:
- Global → Pipeline → Step as mathematical hierarchy
- Inheritance as mathematical operations
- Lazy resolution as deferred computation

**Python Object References**:
- `:py:meth:`~openhcs.core.lazy_config.LazyDataclassFactory._create_field_level_hierarchy_provider` - Hierarchy math
- `:py:func:`~openhcs.core.lazy_placeholder._resolve_field_with_composition_awareness` - Resolution algorithm

#### 3. `visual_programming_principles.rst`
**Problem**: Users don't understand why UI behaves the way it does
**Mental Model**: UI as direct manipulation of mathematical objects
**Key Concepts**:
- Forms reflect mathematical structure
- Placeholders show mathematical relationships
- Visual inheritance hierarchy

**Python Object References**:
- `:py:class:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager` - UI-math bridge
- `:py:meth:`~openhcs.core.lazy_placeholder.LazyDefaultPlaceholderService.get_lazy_resolved_placeholder` - Placeholder math

### Phase 2: Core System Mental Models
**Target: Explain the systems users interact with daily**

#### 4. `lazy_configuration_mental_model.rst`
**Problem**: Users encounter lazy configs but don't understand the "lost edits" problem
**Mental Model**: Lazy configs as smart defaults that preserve user intent
**Key Concepts**:
- The "lost edits" problem in traditional systems
- Lazy resolution as context-aware computation
- Thread-local context as mathematical environment

**Python Object References**:
- `:py:func:`~openhcs.core.lazy_config.create_dataclass_for_editing` - Edit preservation
- `:py:func:`~openhcs.core.context.global_config.get_current_global_config` - Context system

#### 5. `inheritance_and_placeholders.rst`
**Problem**: Users see "Pipeline default: X" everywhere but don't understand it
**Mental Model**: Placeholders as windows into mathematical inheritance
**Key Concepts**:
- Rightmost parent precedence in multiple inheritance
- Placeholder text as inheritance visualization
- Sibling inheritance patterns

**Python Object References**:
- `:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager._field_inherits_from_dataclass` - Inheritance detection
- `:py:meth:`~openhcs.pyqt_gui.widgets.shared.parameter_form_manager.ParameterFormManager.refresh_placeholder_text_with_context` - Placeholder updates

#### 6. `memory_and_types.rst`
**Problem**: Users don't understand automatic GPU conversion uniqueness
**Mental Model**: Memory types as mathematical spaces with automatic transformations
**Key Concepts**:
- NumPy, CuPy, PyTorch as different mathematical spaces
- Automatic conversion as mathematical isomorphisms
- Performance implications of transformations

**Python Object References**:
- `:py:func:`~openhcs.core.memory_type_system.convert_memory_type` - Type conversion
- `:py:class:`~openhcs.core.memory_type_system.MemoryTypeManager` - Type management

### Phase 3: Advanced Understanding
**Target: Enable extension and debugging**

#### 7. `metaprogramming_rationale.rst`
**Problem**: Critics see complexity without understanding necessity
**Mental Model**: Metaprogramming as mathematical abstraction tools
**Key Concepts**:
- Why generic abstractions are necessary
- Domain complexity that cannot be reduced
- Metaprogramming as mathematical generalization

#### 8. `extensibility_patterns.rst`
**Problem**: Contributors don't know how to extend the system correctly
**Mental Model**: Extension points as mathematical interfaces
**Key Concepts**:
- Where and how to add new functionality
- Respecting architectural contracts
- Mathematical consistency requirements

#### 9. `debugging_complex_systems.rst`
**Problem**: When things break, users have no systematic approach
**Mental Model**: Debugging as mathematical proof verification
**Key Concepts**:
- Systematic troubleshooting methodology
- Understanding error patterns
- Using debug output effectively

## Implementation Methodology

### Python Object Reference Standards
Following literal includes audit methodology:

```rst
# Implementation-priming prose BEFORE Python object reference
:py:meth:`~openhcs.core.lazy_config.LazyDataclassFactory._create_lazy_dataclass_unified`
works like a dataclass compiler. It takes a regular dataclass definition and generates a new
class with the same fields and interface, but replaces the field access behavior.

# Architectural rationale AFTER Python object reference
This enables the same dataclass interface with different resolution behavior for different
contexts - step editors resolve against pipeline config, pipeline configs resolve against
global config, and global configs use static defaults.
```

### Literal Include Integration
Where appropriate, use literal includes for concrete examples:

```rst
.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 357-380
   :caption: Field-level auto-hierarchy creation with context awareness
```

### Progressive Disclosure Pattern
Each document follows:
1. **Problem Statement** - What user pain point does this solve?
2. **Mental Model** - How should users think about this?
3. **Implementation Context** - How does the code solve it?
4. **Python Object References** - Validated references to actual implementation
5. **Usage Patterns** - How do users interact with this?

## Quality Standards

### Validation Requirements
- All Python object references must pass Sphinx validation
- Implementation-priming prose for every `:py:` reference
- Progressive complexity (simple → advanced)
- Connection to user experience (what they see in UI)

### Success Metrics
- **Comprehension Test**: New contributors can understand system after reading concepts
- **Reference Accuracy**: 100% Python object reference validation
- **Mental Model Effectiveness**: Users can predict system behavior
- **Onboarding Speed**: Reduced time to productive contribution

## Implementation Timeline

### Week 1: Foundation Documents
- `mathematical_foundations.rst`
- `configuration_as_mathematics.rst`
- `visual_programming_principles.rst`

### Week 2: Core Systems
- `lazy_configuration_mental_model.rst`
- `inheritance_and_placeholders.rst`
- `memory_and_types.rst`

### Week 3: Advanced Topics
- `metaprogramming_rationale.rst`
- `extensibility_patterns.rst`
- `debugging_complex_systems.rst`

### Week 4: Integration and Polish
- Update `index.rst` with learning paths
- Cross-reference validation
- User testing with undergraduate student

## Draft Example: `lazy_configuration_mental_model.rst`

```rst
Lazy Configuration Mental Model
===============================

**Understanding the "lost edits" problem and how lazy resolution preserves user intent**

The Problem: Lost Edits in Traditional Systems
----------------------------------------------

Traditional configuration systems suffer from a fundamental problem: user edits get overwritten
when switching contexts. Imagine editing a pipeline configuration, then switching to view
global settings. When you return to the pipeline, your edits are gone - replaced by defaults.

This happens because traditional systems don't distinguish between "user set this value" and
"this is the default value." OpenHCS solves this through lazy configuration resolution.

The Solution: Lazy Resolution with Context Awareness
----------------------------------------------------

:py:func:`~openhcs.core.lazy_config.create_dataclass_for_editing` creates configurations that
preserve user intent while providing intelligent defaults. When you set a value, it's marked
as "user intent" and never overwritten. When you leave a field empty, it resolves from the
appropriate context (pipeline → global → static defaults).

.. literalinclude:: ../../../openhcs/core/lazy_config.py
   :language: python
   :lines: 574-587
   :caption: Creating editable configs with value preservation

Mental Model: Smart Defaults That Remember
------------------------------------------

Think of lazy configs as smart defaults that remember what you've explicitly set:

- **None values**: "I want to inherit from parent context"
- **Explicit values**: "I specifically want this value, don't change it"
- **Context switching**: Preserves your intent while updating inherited defaults

This enables the mathematical hierarchy: Global → Pipeline → Step, where each level
can override specific fields while inheriting others.
```

This plan transforms the concepts section from implementation-focused reference material into user-facing mental model documentation that builds understanding progressively while maintaining perpetual accuracy through Python object references.
