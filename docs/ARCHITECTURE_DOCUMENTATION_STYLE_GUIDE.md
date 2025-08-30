# Architecture Documentation Style Guide

## Philosophy: Design Rationale + Code Clarity

Architecture documentation should provide the **mental model** that makes code examples immediately comprehensible. The prose should set up context so well that readers can skim the code and understand both *what* it does and *why* it's architected that way.

## What to Keep: Valuable Design Rationale

### ✅ Context-Setting Prose
High-level English that builds understanding:

```markdown
Different component configurations have different valid combinations and constraints. 
Configuration-driven validation ensures that validation rules adapt automatically to 
the component structure without requiring manual rule updates for each configuration.

```python
class GenericValidator(Generic[T]):
    def __init__(self, config: ComponentConfiguration[T]):
        self.config = config
```

**Why This Works**: The prose explains the *why* behind generic validation, making the `ComponentConfiguration[T]` parameter immediately meaningful.

### ✅ Architectural Insights
Explain design decisions that aren't obvious:

```markdown
The system treats component integration as a cross-cutting concern. All subsystems 
consume component information through standardized interfaces, with the component 
configuration serving as the single source of truth for dimensional structure.
```

**Why This Works**: Explains the architectural pattern that unifies the system design.

### ✅ Problem/Solution Framing
Brief context about what problem the code solves:

```markdown
Traditional validation systems hardcode assumptions about component names and valid 
combinations. The GenericValidator eliminates these assumptions by deriving validation 
rules from component configuration metadata.
```

**Why This Works**: Sets up the problem context that makes the solution architecture meaningful.

## What to Cut: Documentation Theater

### ❌ Redundant Benefit Lists
```markdown
# Cut this noise:
**Validation Benefits**:
1. **Compile-Time Guarantees**: Dict patterns validated before execution
2. **Data-Driven Validation**: Keys validated against actual component data
3. **Clear Error Messages**: Missing keys reported with available alternatives
```

**Why Cut**: These benefits are obvious from the code examples and add no insight.

### ❌ Obvious Implementation Explanations
```markdown
# Cut this:
"The system uses several patterns to achieve axis independence"

# Keep this:
"Axis-agnostic design treats any component as a potential multiprocessing axis"
```

**Why Cut**: Don't explain *that* patterns exist, explain *what* the pattern accomplishes.

### ❌ Repetitive "Why This Matters" Sections
When the same concept is explained multiple times across documents with slightly different wording.

**Why Cut**: Redundancy without additional insight.

## Code Example Integration

### ✅ Prose → Code Flow
Structure sections as: **Context** → **Code** → **Brief Explanation**

```markdown
Each parser automatically generates component-specific interfaces using the 
DynamicParserMeta metaclass:

```python
class CustomFilenameParser(GenericFilenameParser):
    FILENAME_COMPONENTS = ['well', 'site', 'channel', 'timepoint']
    
# Interface automatically generated with component-specific methods:
# - get_well_keys(), get_site_keys(), get_channel_keys(), get_timepoint_keys()
# - construct_filename(well=..., site=..., channel=..., timepoint=...)
```

This eliminates hardcoded component assumptions while providing type-safe interfaces.
```

**Why This Works**: 
1. Prose sets up the concept
2. Code shows the implementation
3. Brief explanation connects them

### ❌ Code Without Context
Don't dump code examples without explaining the architectural reasoning.

### ❌ Prose Without Code
Don't explain concepts without showing concrete implementation.

## Practical Content Guidelines

### ✅ Include Common Gotchas
```markdown
**Common Gotchas**:
- Don't use `GroupBy.NONE` with dict patterns - validation will fail
- Component keys are cached on initialization - call `clear_component_cache()` if input directory changes
- Dict pattern keys must match actual component values, not enum names
```

### ❌ Skip Debugging Guides in Architecture Docs
Debugging content belongs in troubleshooting guides, not architecture documentation.

### ❌ Skip Migration Guides in Architecture Docs
Migration content belongs in upgrade guides, not architecture documentation.

## Writing Style

### Voice and Tone
- **Explanatory, not promotional**: Explain why the architecture works this way
- **Concise but complete**: Every sentence should add understanding
- **Technical precision**: Use accurate terminology consistently

### Structure Patterns
1. **Problem Context** (1-2 sentences)
2. **Solution Approach** (1-2 sentences) 
3. **Code Example** (concrete implementation)
4. **Key Insight** (1 sentence connecting problem to solution)

### Length Guidelines
- **Section prose**: 2-4 sentences maximum before code
- **Code examples**: Show complete, working patterns
- **Explanations**: 1-2 sentences after code to reinforce the concept

## Quality Checklist

Before publishing architecture documentation, verify:

### Content Quality
- [ ] Every code example is based on actual implementation
- [ ] Prose explains *why* the architecture works this way
- [ ] No redundant benefit lists or obvious explanations
- [ ] Design rationale provides mental model for understanding code

### Technical Accuracy
- [ ] All class names and method signatures verified against codebase
- [ ] Integration patterns tested and confirmed
- [ ] Cross-references point to existing documentation

### Reader Experience
- [ ] Can reader skim prose and understand code examples?
- [ ] Does prose answer "why is it designed this way?"
- [ ] Are architectural insights non-obvious and valuable?
- [ ] Is the signal-to-noise ratio high?

## Example: Good vs Bad Documentation

### ❌ Documentation Theater
```markdown
The Component Validation System provides generic, configuration-driven validation 
for component combinations and constraints in OpenHCS. The system eliminates 
hardcoded validation assumptions by providing a configurable validation framework 
that adapts to any component configuration and enforces processing constraints 
at compile time.

**Key Innovation**: The system provides generic validation that operates on 
component configurations rather than hardcoded component names.

**Architectural Approach**: The system treats validation as a configuration-driven concern.

**Benefits**:
1. **Configuration-Driven Validation**: All validation rules derived from metadata
2. **Compile-Time Constraint Enforcement**: Critical constraints validated during compilation
3. **Generic Constraint Patterns**: Validation rules expressed as generic patterns
```

**Problems**: Verbose, repetitive, obvious benefits, no code context.

### ✅ Effective Architecture Documentation
```markdown
Traditional validation systems hardcode assumptions about component names and valid 
combinations. The GenericValidator eliminates these assumptions by deriving validation 
rules from component configuration metadata.

```python
class GenericValidator(Generic[T]):
    def __init__(self, config: ComponentConfiguration[T]):
        self.config = config
    
    def validate_step(self, variable_components: List[T], group_by: Optional[T]) -> ValidationResult:
        # Core constraint: group_by ∉ variable_components
        self.config.validate_combination(variable_components, group_by)
```

This enables the same validation logic to work with any component configuration - 
wells, timepoints, batches - without code changes.
```

**Why This Works**: 
- Sets up the problem (hardcoded assumptions)
- Shows the solution (generic configuration)
- Demonstrates with concrete code
- Explains the key benefit (works with any configuration)
