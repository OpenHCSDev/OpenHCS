# plan_01_generic_compiler_spec.md
## Component: Declarative Compilation Phase System

### Objective

Transform OpenHCS compilation from imperative dict mutation into **declarative phase composition** following the patterns already cracked in the codebase:

- `@auto_create_decorator` → generates decorator → generates classes → injects fields
- `@numpy`, `@torch` → function declares contract → framework uses metadata
- `AutoRegisterMeta` → class declares key → auto-registers in global registry

The compilation system is the LAST piece still imperative. Fixing it completes the platform.

### The Pattern

Every cracked system in OpenHCS follows:

```
DECLARATION → INTROSPECTION → DERIVATION → EXECUTION
```

| System | Declaration | Introspection | Derivation |
|--------|-------------|---------------|------------|
| Config | Dataclass with defaults | `@auto_create_decorator` | Lazy class, field injection |
| Memory | `@torch` decorator | `func.input_memory_type` | Auto-conversion |
| Registry | `_microscope_type = 'imagexpress'` | `AutoRegisterMeta` | Auto-registration |
| **Compilation** | **Resolver methods** | **`__init_subclass__`** | **Schema + compile()** |

### The Disease

Current compilation is imperative mutation:

```python
# CURRENT (Imperative - Wrong)
class PathPlanner:
    def plan_step(self, step, context):
        plan = {}
        plan['input_dir'] = self._resolve_input_dir(step, context)  # Imperative
        plan['output_dir'] = self._resolve_output_dir(step, context)  # Imperative
        plan['func'] = step.func  # Imperative
        return plan  # Dict[str, Any] - stringly typed garbage
```

No contracts. No composition. No derivation.

### Plan

#### 1. CompilationPhase ABC with Introspection

```python
from abc import ABC, abstractmethod
from dataclasses import make_dataclass, field
from typing import get_type_hints, Callable, Dict, Type
import inspect

class CompilationPhase(ABC):
    """ABC that introspects resolver methods and derives provides/compile().

    Following @dataclass pattern: you declare fields, framework derives __init__.
    Here: you declare resolvers, framework derives provides + compile().

    ABC, not Protocol. MANIFESTO Section V: "A contract you must detect is not a contract."
    """

    # Derived by __init_subclass__ from resolver methods
    _resolvers: Dict[str, Callable]
    provides: Dict[str, Type]

    def __init_subclass__(cls, **kwargs):
        super().__init_subclass__(**kwargs)

        # Introspect resolver methods
        cls._resolvers = {}
        cls.provides = {}

        for name, method in inspect.getmembers(cls, predicate=inspect.isfunction):
            if name.startswith('_') or name in ('compile', 'validate'):
                continue

            sig = inspect.signature(method)
            params = list(sig.parameters.values())

            # Resolver signature: (self, step: AbstractStep, context: ProcessingContext) -> T
            if len(params) >= 3 and sig.return_annotation != inspect.Signature.empty:
                cls._resolvers[name] = method
                cls.provides[name] = sig.return_annotation

    def compile(self, step: 'AbstractStep', plan: 'StepPlan', context: 'ProcessingContext') -> 'StepPlan':
        """Auto-generated: calls all resolvers and returns updated plan."""
        from dataclasses import replace
        updates = {}
        for field_name, resolver in self._resolvers.items():
            updates[field_name] = resolver(self, step, context)
        return replace(plan, **updates)
```

#### 2. Phases Declare Resolvers as Methods

```python
class PathPlanningPhase(CompilationPhase):
    """Phase declares resolvers. Framework introspects and wires.

    Each method with signature (step, context) -> T becomes a field resolver.
    Method name = field name. Return annotation = field type.
    """

    def input_dir(self, step: AbstractStep, context: ProcessingContext) -> Path:
        if step.pipeline_position == 0:
            return context.input_dir
        prev_plan = context.step_plans[step.pipeline_position - 1]
        return prev_plan.output_dir

    def output_dir(self, step: AbstractStep, context: ProcessingContext) -> Path:
        return self._build_output_path(step, context)

    def func(self, step: AbstractStep, context: ProcessingContext) -> FuncPattern:
        return step.func

    def special_inputs(self, step: AbstractStep, context: ProcessingContext) -> Dict[str, Path]:
        return self._resolve_special_inputs(step, context)

    def special_outputs(self, step: AbstractStep, context: ProcessingContext) -> OrderedDict[str, Path]:
        return self._resolve_special_outputs(step, context)

    # Helper methods (prefixed with _) are NOT resolvers
    def _build_output_path(self, step, context) -> Path:
        ...


class MaterializationPhase(CompilationPhase):
    """Determines storage backends for each step."""

    def read_backend(self, step: AbstractStep, context: ProcessingContext) -> Backend:
        if step.pipeline_position == 0:
            return Backend.DISK
        return context.step_plans[step.pipeline_position - 1].write_backend

    def write_backend(self, step: AbstractStep, context: ProcessingContext) -> Backend:
        if self._needs_materialization(step, context):
            return Backend.ZARR
        return Backend.MEMORY


class MemoryContractPhase(CompilationPhase):
    """Validates and plans memory type conversions."""

    def input_memory_type(self, step: AbstractStep, context: ProcessingContext) -> MemoryType:
        func = context.step_plans[step.pipeline_position].func
        return getattr(func, 'input_memory_type', MemoryType.NUMPY)

    def output_memory_type(self, step: AbstractStep, context: ProcessingContext) -> MemoryType:
        func = context.step_plans[step.pipeline_position].func
        return getattr(func, 'output_memory_type', MemoryType.NUMPY)


class GPUAssignmentPhase(CompilationPhase):
    """Assigns GPU resources for GPU memory types."""

    def gpu_id(self, step: AbstractStep, context: ProcessingContext) -> Optional[int]:
        plan = context.step_plans[step.pipeline_position]
        if plan.input_memory_type in GPU_MEMORY_TYPES:
            return self._assign_gpu(context)
        return None
```

#### 3. StepPlan Schema Derived from All Phases

```python
# Phase registry - populated by __init_subclass__ or decorator
COMPILATION_PHASES: List[Type[CompilationPhase]] = [
    PathPlanningPhase,
    MaterializationPhase,
    MemoryContractPhase,
    GPUAssignmentPhase,
]

def derive_step_plan_schema() -> Type:
    """Derive StepPlan dataclass from all registered phases.

    Following @auto_create_decorator pattern: schema is DERIVED, not hardcoded.
    Adding a new phase automatically extends the schema.
    """
    all_fields = [
        # Base fields always present
        ('step_name', str, field(default='')),
        ('step_type', str, field(default='')),
        ('axis_id', str, field(default='')),
        ('pipeline_position', int, field(default=0)),
    ]

    # Collect fields from all phases
    for phase_cls in COMPILATION_PHASES:
        for field_name, field_type in phase_cls.provides.items():
            # Optional because not all phases may have run yet
            all_fields.append((field_name, Optional[field_type], field(default=None)))

    return make_dataclass('StepPlan', all_fields, frozen=True)

# Generated at import time
StepPlan = derive_step_plan_schema()
```

#### 4. Compiler Executes Phases in Order

```python
class PipelineCompiler:
    """Compiles pipeline by executing phases in order.

    Each phase transforms StepPlan, adding its provided fields.
    Final StepPlan has all fields from all phases.
    """

    phases: List[CompilationPhase] = [phase_cls() for phase_cls in COMPILATION_PHASES]

    def compile(self, steps: List[AbstractStep], context: ProcessingContext) -> List[StepPlan]:
        plans = []

        for i, step in enumerate(steps):
            # Initialize with base fields
            plan = StepPlan(
                step_name=step.name,
                step_type=step.__class__.__name__,
                axis_id=context.axis_id,
                pipeline_position=i,
            )

            # Each phase adds its fields
            for phase in self.phases:
                plan = phase.compile(step, plan, context)

            plans.append(plan)
            context.step_plans[i] = plan  # Inject for next step's resolvers

        return plans
```

#### 5. Steps Execute Against Typed StepPlan

```python
class FunctionStep(AbstractStep):
    def process(self, context: ProcessingContext, step_index: int) -> None:
        plan: StepPlan = context.step_plans[step_index]

        # Typed access - no more plan.get('func') or plan['input_dir']
        func = plan.func
        input_dir = plan.input_dir
        input_memory_type = plan.input_memory_type
        gpu_id = plan.gpu_id

        # Execute with typed plan
        ...
```

### OpenHCS as a Spec

This pattern makes OpenHCS a **spec for dimensional dataflow compilers**:

| Domain | Dimensions | Phases |
|--------|------------|--------|
| HCS | well, channel, site, z, time | PathPlanning, Materialization, Memory, GPU |
| Genomics | sample, lane, read, barcode | PathPlanning, ResourceAllocation, Parallelization |
| Astronomy | field, exposure, filter, chip | PathPlanning, Storage, Calibration |

The platform provides:
- `CompilationPhase` ABC with introspection
- `derive_step_plan_schema()` for runtime schema generation
- Frozen context for thread-safe execution

The domain provides:
- Dimension definitions
- Processing functions with contracts
- Domain-specific phases

### Findings

| Phase | Provides (derived from resolver methods) |
|-------|------------------------------------------|
| PathPlanningPhase | input_dir, output_dir, func, special_inputs, special_outputs, funcplan |
| MaterializationPhase | read_backend, write_backend, materialized_backend |
| MemoryContractPhase | input_memory_type, output_memory_type |
| GPUAssignmentPhase | gpu_id |

**The `func` redundancy is eliminated.** PathPlanningPhase stores it once. MemoryContractPhase reads from the existing plan.

### The Cascade

```
CompilationPhase subclass defined
    → __init_subclass__ introspects resolver methods
    → Derives provides = {method_name: return_type, ...}
    → Generates compile() that calls all resolvers

At import time:
    → derive_step_plan_schema() collects all phase.provides
    → make_dataclass creates StepPlan with typed fields
    → StepPlan is frozen dataclass, not Dict[str, Any]

At compile time:
    → Compiler iterates phases in order
    → Each phase.compile(step, plan, context) returns updated plan
    → Final StepPlan is typed, validated, frozen
```

### Cleanup — DELETE ALL OF THIS

**Code to DELETE from `path_planning.py`, `materialization.py`, etc.:**
```python
def plan_step(self, step, context):
    plan = {}
    plan['input_dir'] = self._resolve_input_dir(...)  # DELETE imperative dict mutation
    plan['output_dir'] = self._resolve_output_dir(...)
    return plan  # DELETE Dict[str, Any] return
```

**Patterns to DELETE:**
- All `plan = {}` dict initialization → replaced by typed dataclass construction
- All `plan['key'] = value` mutations → replaced by resolver method declarations
- All `Dict[str, Any]` return types → replaced by frozen `StepPlan` dataclass

**No wrappers. No backwards compatibility.**
- `StepPlan` is a frozen dataclass, not `Dict[str, Any]`
- Code that accesses `plan['key']` → fails loud, update to `plan.key`
- Code that mutates plan after creation → fails loud, plans are frozen

### ❌ ANTIPATTERNS TO AVOID

**DO NOT keep Dict[str, Any] with TypedDict hints:**
```python
# ❌ WRONG: TypedDict is still a dict
class StepPlanDict(TypedDict):
    input_dir: Path
    output_dir: Path
    func: Callable
```
Use frozen dataclass. TypedDict is runtime-mutable and has no frozen semantics.

**DO NOT add __getitem__ for dict-style access:**
```python
# ❌ WRONG: Backwards-compatible dict access
@dataclass(frozen=True)
class StepPlan:
    input_dir: Path

    def __getitem__(self, key):
        return getattr(self, key)  # DON'T ADD THIS
```
Attribute access only. `plan.input_dir`, not `plan['input_dir']`.

**DO NOT create mutable intermediate plans:**
```python
# ❌ WRONG: Mutable during compilation
plan = StepPlan()  # mutable
for phase in phases:
    phase.compile(plan)  # mutates
plan.freeze()  # DON'T
```
Each phase returns a NEW frozen plan. Immutable by construction.

**DO NOT create abstract compile() methods for phases:**
```python
# ❌ WRONG: Abstract method per phase
class PathPlanningPhase(CompilationPhase):
    @abstractmethod
    def compile(self, step, plan, context): ...  # DON'T
```
Phases declare resolver METHODS (e.g., `resolve_input_dir()`). `__init_subclass__` derives `compile()`. No abstract `compile()`.

**DO NOT create phase subclasses per step type:**
```python
# ❌ WRONG: Per-step phase classes
class FunctionStepPathPlanningPhase(PathPlanningPhase): ...
class CustomStepPathPlanningPhase(PathPlanningPhase): ...
```
ONE phase class per concern. Dispatch on step attributes, not step type.

**DO NOT store `func` in multiple phases:**
```python
# ❌ WRONG: Redundant storage
class PathPlanningPhase:
    provides = ['input_dir', 'func']  # func here

class MemoryContractPhase:
    provides = ['memory_type', 'func']  # func here too - DON'T
```
`func` is in PathPlanningPhase. Later phases read from existing plan.

### Implementation Draft

*Awaiting smell loop approval.*
