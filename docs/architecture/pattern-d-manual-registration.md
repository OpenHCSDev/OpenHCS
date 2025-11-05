# Pattern D: Manual Registration

## Overview

**Pattern D** is used for systems where **explicit control** over registration is needed, typically due to complex initialization logic, rare plugins, or when automatic discovery would add unnecessary complexity.

## When to Use Pattern D

Use Manual Registration when:
- ✅ **Complex initialization**: Plugins require complex setup logic
- ✅ **Explicit control needed**: Registration timing must be carefully controlled
- ✅ **Very few plugins**: < 3 implementations (auto-discovery overhead not justified)
- ✅ **Rare additions**: New plugins added infrequently (< 1 per year)
- ✅ **Context-dependent**: Registration depends on runtime conditions

**Examples in OpenHCS:**
- **ZMQ Servers**: 2 implementations (Execution, Fiji Viewer) with complex initialization
- **Pipeline Steps**: User-defined steps with explicit instantiation

## Architecture

### Core Pattern

```
┌─────────────────────────────────────────────────────────────┐
│                  Abstract Base Class                         │
│  ┌────────────────────────────────────────────────────────┐ │
│  │         ZMQServer (ABC)                                │ │
│  │  - Defines interface for all servers                   │ │
│  │  - Provides common functionality                       │ │
│  │  - No automatic registration                           │ │
│  └────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────┘
                            │
                            │ implemented by
                            ▼
┌─────────────────────────────────────────────────────────────┐
│              Concrete Implementations                        │
│  ┌──────────────────┐  ┌──────────────────┐                │
│  │  ZMQExecution    │  │  FijiViewer      │                │
│  │     Server       │  │     Server       │                │
│  └──────────────────┘  └──────────────────┘                │
└─────────────────────────────────────────────────────────────┘
                            │
                            │ manually instantiated
                            ▼
┌─────────────────────────────────────────────────────────────┐
│                  Explicit Usage                              │
│  server = ZMQExecutionServer(port=7777)                     │
│  server.start()                                              │
└─────────────────────────────────────────────────────────────┘
```

## Implementation Examples

### 1. ZMQ Servers

**Use Case**: Dual-channel ZMQ servers with complex initialization

**Why Manual**:
- Only 2 implementations (Execution, Fiji Viewer)
- Complex initialization (ports, transport modes, logging)
- Explicit control over server lifecycle needed
- New servers added rarely (< 1 per year)

**Implementation**:

```python
# openhcs/runtime/zmq_base.py

class ZMQServer(ABC):
    """ABC for ZMQ servers - dual-channel pattern with ping/pong handshake."""

    def __init__(self, port, host='*', log_file_path=None, data_socket_type=None, transport_mode=None):
        self.port = port
        self.host = host
        self.control_port = port + CONTROL_PORT_OFFSET
        self.log_file_path = log_file_path
        self.data_socket_type = data_socket_type if data_socket_type is not None else zmq.PUB
        self.transport_mode = transport_mode or get_default_transport_mode()
        # ... complex initialization
    
    @abstractmethod
    def handle_control_message(self, message: Dict[str, Any]) -> Dict[str, Any]:
        """Handle control messages. Subclasses must implement."""
        pass
    
    def start(self):
        """Start the server (complex setup)."""
        # ... socket binding, thread management, etc.
        pass

# openhcs/runtime/zmq_execution_server.py

class ZMQExecutionServer(ZMQServer):
    """ZMQ execution server for OpenHCS pipelines."""

    def __init__(self, port=DEFAULT_EXECUTION_SERVER_PORT, host='*', log_file_path=None, transport_mode=TransportMode.IPC):
        super().__init__(port, host, log_file_path, transport_mode=transport_mode)
        self.active_executions = {}
        self.start_time = None
        self.progress_queue = queue.Queue()
        # ... more complex state

# Usage: Explicit instantiation
server = ZMQExecutionServer(port=7777, transport_mode=TransportMode.TCP)
server.start()
```

**Analysis**:
- **Implementations**: 2 (ZMQExecutionServer, FijiViewerServer)
- **Frequency**: New servers added < 1 per year
- **Complexity**: High (ports, sockets, threads, transport modes)
- **Decision**: ✅ **Keep Manual** - Auto-registration not justified

### 2. Pipeline Steps

**Use Case**: User-defined pipeline steps with explicit instantiation

**Why Manual**:
- Steps are instantiated explicitly by users in pipeline definitions
- Each step has unique configuration
- No need for discovery (users create steps directly)
- Steps are not "plugins" in the traditional sense

**Implementation**:

```python
# openhcs/core/steps/abstract.py

class AbstractStep(ABC, ContextProvider):
    """Abstract base class for all steps in the OpenHCS pipeline."""

    def __init__(self, name=None, description=None, enabled=True, variable_components=None, ...):
        self.name = name or self.__class__.__name__
        self.description = description
        self.enabled = enabled
        # ... many configuration parameters
    
    @abstractmethod
    def execute(self, context: ProcessingContext) -> Any:
        """Execute the step. Subclasses must implement."""
        pass

# openhcs/core/steps/function_step.py

class FunctionStep(AbstractStep):
    """Step that executes a processing function."""

    def __init__(self, func, name=None, **kwargs):
        super().__init__(name=name, **kwargs)
        self.func = func
    
    def execute(self, context):
        return self.func(context)

# Usage: Explicit instantiation in pipeline
pipeline = Pipeline([
    FunctionStep(func=normalize, name="normalize"),
    FunctionStep(func=segment, name="segment"),
    FunctionStep(func=measure, name="measure"),
])
```

**Analysis**:
- **Implementations**: 10+ step types (FunctionStep, SegmentationStep, etc.)
- **User-defined**: Users create custom steps frequently
- **Instantiation**: Explicit in pipeline definitions
- **Discovery**: Not needed (steps are not discovered, they're created)
- **Decision**: ✅ **Keep Manual** - Steps are not plugins, they're user-defined components

## When to Migrate from Pattern D

Consider migrating to Pattern A (metaclass) if:

1. **Number of implementations grows**: > 5 implementations
2. **Frequent additions**: New implementations added > 4 times per year
3. **Simple initialization**: No complex setup logic
4. **Discovery needed**: Need to list all available implementations
5. **Plugin ecosystem**: Want users to create plugins easily

**Migration Example**:

```python
# Before: Manual (Pattern D)
class MyHandler:
    pass

# Explicit registration
HANDLERS = {
    'type1': MyHandler1(),
    'type2': MyHandler2(),
}

# After: Metaclass (Pattern A)
class MyHandlerMeta(AutoRegisterMeta):
    def __new__(mcs, name, bases, attrs):
        return super().__new__(mcs, name, bases, attrs,
                              registry_config=_HANDLER_REGISTRY_CONFIG)

class MyHandler(metaclass=MyHandlerMeta):
    _handler_type = None  # Override in subclasses

class MyHandler1(MyHandler):
    _handler_type = 'type1'  # Auto-registered!

class MyHandler2(MyHandler):
    _handler_type = 'type2'  # Auto-registered!
```

## Best Practices

### 1. Use Abstract Base Classes

Define clear interfaces even without auto-registration:

```python
class MyPluginBase(ABC):
    @abstractmethod
    def process(self, data):
        """Process data. Subclasses must implement."""
        pass
```

### 2. Document Why Manual

Add comments explaining why manual registration is appropriate:

```python
class ZMQServer(ABC):
    """
    ABC for ZMQ servers.
    
    Note: No auto-registration - servers require complex initialization
    with ports, transport modes, and logging configuration. Only 2
    implementations exist and new servers are added < 1 per year.
    """
    pass
```

### 3. Provide Factory Functions

If initialization is complex, provide factory functions:

```python
def create_execution_server(port=None, transport_mode=None):
    """Create execution server with sensible defaults."""
    port = port or DEFAULT_EXECUTION_SERVER_PORT
    transport_mode = transport_mode or get_default_transport_mode()
    return ZMQExecutionServer(port=port, transport_mode=transport_mode)
```

### 4. Keep It Simple

Don't add auto-registration just because other systems have it:

```python
# Good: Simple and explicit
server = ZMQExecutionServer(port=7777)
server.start()

# Overkill: Auto-registration for 2 implementations
class ZMQServerMeta(AutoRegisterMeta):
    ...  # Unnecessary complexity
```

## Comparison with Other Patterns

| Aspect | Pattern A (Metaclass) | Pattern B (Service) | Pattern C (Functional) | Pattern D (Manual) |
|--------|----------------------|---------------------|------------------------|-------------------|
| **Registration** | Automatic | Automatic | Manual (dict) | Manual (explicit) |
| **Complexity** | Medium | High | Low | Variable |
| **Use Case** | Plugin classes | Many items/plugin | Type dispatch | Complex init |
| **Implementations** | 3-20+ | 3-20+ | 5-50+ | 1-3 |
| **Discovery** | Automatic | Automatic | N/A | Not needed |
| **When to use** | Plugin ecosystem | Rich metadata | Simple mappings | Rare plugins |

## Evaluation Results

### ZMQ Servers

**Current State**:
- 2 implementations (ZMQExecutionServer, FijiViewerServer)
- Complex initialization (ports, sockets, threads, transport modes)
- New servers added < 1 per year
- Explicit control over lifecycle needed

**Decision**: ✅ **Keep Manual (Pattern D)**

**Rationale**:
- Only 2 implementations (threshold for auto-registration is 5+)
- Complex initialization logic not suitable for metaclass
- Explicit control over server lifecycle is important
- No discovery needed (servers are explicitly created)

### Pipeline Steps

**Current State**:
- 10+ step types (FunctionStep, SegmentationStep, etc.)
- User-defined steps created frequently
- Explicit instantiation in pipeline definitions
- No discovery needed (steps are not discovered, they're created)

**Decision**: ✅ **Keep Manual (Pattern D)**

**Rationale**:
- Steps are not "plugins" - they're user-defined components
- Explicit instantiation is the correct pattern for pipeline DSL
- No discovery needed (users create steps directly)
- Auto-registration would add complexity without benefit

## Summary

**Pattern D is appropriate when**:
- Very few implementations (< 3)
- Complex initialization required
- Explicit control needed
- Rare additions (< 1 per year)
- No discovery needed

**Keep it simple**: Don't add auto-registration infrastructure for systems that don't need it. Manual registration is perfectly fine for rare, complex plugins.

## See Also

- [Pattern A: Metaclass Auto-Registration](pattern-a-metaclass-registry.md)
- [Pattern B: Service-Based Registry](pattern-b-service-based-registry.md)
- [Pattern C: Functional Registry](pattern-c-functional-registry.md)
- [Registry Pattern Decision Tree](registry-framework.md#decision-tree)

