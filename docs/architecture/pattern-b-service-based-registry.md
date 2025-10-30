# Pattern B: Service-Based Registry

## Overview

**Pattern B** is used for registry systems with **many-to-one mapping** where multiple items (functions, formats, etc.) belong to a single plugin, and each item has **complex metadata** requiring aggregation and discovery across multiple sources.

## When to Use Pattern B

Use Service-Based Registry when:
- ✅ **Many-to-one mapping**: Multiple items per plugin (e.g., 574+ functions across 4 libraries)
- ✅ **Rich metadata**: Each item has 8+ metadata fields (name, contract, module, doc, tags, etc.)
- ✅ **Aggregation needed**: Need to collect and unify items from multiple sources
- ✅ **Discovery complexity**: Items are discovered through introspection, not just class definition
- ✅ **Caching beneficial**: Discovery is expensive and results should be cached

**Examples in OpenHCS:**
- **Function Registry**: LibraryRegistryBase → RegistryService (574+ functions from 4 libraries)
- **Format Registry**: MicroscopeFormatRegistryBase → FormatRegistryService (multiple microscope formats)

## Architecture

### Core Components

```
┌─────────────────────────────────────────────────────────────┐
│                    Service Layer                             │
│  ┌────────────────────────────────────────────────────────┐ │
│  │         RegistryService (Discovery + Caching)          │ │
│  │  - Discovers all registry implementations              │ │
│  │  - Aggregates metadata from all sources                │ │
│  │  - Provides unified access with caching                │ │
│  └────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────┘
                            │
                            │ discovers
                            ▼
┌─────────────────────────────────────────────────────────────┐
│                  Abstract Base Class                         │
│  ┌────────────────────────────────────────────────────────┐ │
│  │      LibraryRegistryBase (ABC)                         │ │
│  │  - Defines contract for all registries                 │ │
│  │  - Provides common functionality (caching, wrapping)   │ │
│  │  - Abstract methods for discovery                      │ │
│  └────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────┘
                            │
                            │ implemented by
                            ▼
┌─────────────────────────────────────────────────────────────┐
│              Concrete Registry Implementations               │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐      │
│  │   OpenHCS    │  │  Skimage     │  │ Pyclesper.   │ ...  │
│  │   Registry   │  │  Registry    │  │   Registry   │      │
│  └──────────────┘  └──────────────┘  └──────────────┘      │
└─────────────────────────────────────────────────────────────┘
```

### Metadata Dataclass

Each item is wrapped in a rich metadata dataclass:

```python
@dataclass(frozen=True)
class FunctionMetadata:
    """Clean metadata with no library-specific leakage."""
    name: str                          # Function name
    func: Callable                     # The actual function
    contract: ProcessingContract       # Execution contract (PURE_3D, PURE_2D, etc.)
    registry: 'LibraryRegistryBase'    # Reference to parent registry
    module: str = ""                   # Source module
    doc: str = ""                      # Documentation
    tags: List[str] = field(default_factory=list)  # Categorization tags
    original_name: str = ""            # Original function name
```

## Implementation Pattern

### 1. Define Abstract Base Class

```python
class LibraryRegistryBase(ABC):
    """Minimal ABC for all library registries."""
    
    # Class attributes each implementation must define
    MODULES_TO_SCAN: List[str]
    MEMORY_TYPE: str
    FLOAT_DTYPE: Any
    
    def __init__(self, library_name: str):
        self.library_name = library_name
        self._cache_path = get_cache_file_path(f"{library_name}_function_metadata.json")
    
    @abstractmethod
    def get_library_version(self) -> str:
        """Get library version for cache validation."""
        pass
    
    @abstractmethod
    def discover_functions(self) -> Dict[str, FunctionMetadata]:
        """Discover and classify all library functions."""
        pass
    
    def _load_or_discover_functions(self) -> Dict[str, FunctionMetadata]:
        """Load from cache or discover fresh (with caching)."""
        # Try cache first
        if self._cache_path.exists():
            cached = self._load_from_cache()
            if cached:
                return cached
        
        # Discover fresh and cache
        functions = self.discover_functions()
        self._save_to_cache(functions)
        return functions
```

### 2. Implement Concrete Registries

```python
class OpenHCSRegistry(LibraryRegistryBase):
    """Registry for OpenHCS native functions."""
    
    MODULES_TO_SCAN = ['openhcs.processing.functions']
    MEMORY_TYPE = 'numpy'
    FLOAT_DTYPE = np.float32
    
    def __init__(self):
        super().__init__(library_name='openhcs')
    
    def get_library_version(self) -> str:
        return openhcs.__version__
    
    def discover_functions(self) -> Dict[str, FunctionMetadata]:
        """Discover OpenHCS functions with memory type decorators."""
        functions = {}
        modules = self.get_modules_to_scan()
        
        for module_name, module in modules:
            for name, obj in inspect.getmembers(module, inspect.isfunction):
                # Check for memory type decorator
                if hasattr(obj, '_memory_types'):
                    contract = self._infer_contract(obj)
                    metadata = FunctionMetadata(
                        name=name,
                        func=obj,
                        contract=contract,
                        registry=self,
                        module=module_name,
                        doc=obj.__doc__ or "",
                        tags=self._generate_tags(name)
                    )
                    functions[name] = metadata
        
        return functions
```

### 3. Create Discovery Service

```python
class RegistryService:
    """Service for registry discovery and function metadata access."""
    
    _metadata_cache: Optional[Dict[str, FunctionMetadata]] = None
    
    @classmethod
    def get_all_functions_with_metadata(cls) -> Dict[str, FunctionMetadata]:
        """Get unified metadata for all functions from all registries."""
        if cls._metadata_cache is not None:
            return cls._metadata_cache
        
        all_functions = {}
        
        # Discover all registry classes automatically
        registry_classes = cls._discover_registries()
        
        for registry_class in registry_classes:
            try:
                registry_instance = registry_class()
                functions = registry_instance._load_or_discover_functions()
                
                # Use composite keys to prevent collisions
                for func_name, metadata in functions.items():
                    composite_key = f"{registry_instance.library_name}:{func_name}"
                    all_functions[composite_key] = metadata
            except Exception as e:
                logger.warning(f"Failed to load registry {registry_class.__name__}: {e}")
        
        cls._metadata_cache = all_functions
        return all_functions
    
    @classmethod
    def _discover_registries(cls) -> List[type]:
        """Automatically discover all registry implementations."""
        import openhcs.processing.backends.lib_registry as registry_package
        
        return discover_registry_classes(
            package_path=registry_package.__path__,
            package_prefix=registry_package.__name__ + ".",
            base_class=LibraryRegistryBase,
            exclude_modules={'unified_registry'}
        )
```

## Key Features

### 1. Automatic Discovery

The service automatically discovers all registry implementations using the generic `discover_registry_classes()` utility:

```python
registry_classes = discover_registry_classes(
    package_path=registry_package.__path__,
    package_prefix=registry_package.__name__ + ".",
    base_class=LibraryRegistryBase,
    exclude_modules={'unified_registry'}
)
```

### 2. Caching Strategy

Two-level caching:
- **Registry-level cache**: Each registry caches its discovered functions to disk
- **Service-level cache**: Service caches aggregated metadata in memory

```python
# Registry-level: Disk cache
self._cache_path = get_cache_file_path(f"{library_name}_function_metadata.json")

# Service-level: Memory cache
_metadata_cache: Optional[Dict[str, FunctionMetadata]] = None
```

### 3. Composite Keys

Prevents function name collisions between registries:

```python
composite_key = f"{registry_instance.library_name}:{func_name}"
# Example: "torch:stack_percentile_normalize"
```

### 4. Rich Metadata

Each item carries comprehensive metadata:
- Function reference
- Execution contract
- Source module
- Documentation
- Tags for categorization
- Registry reference

## Comparison with Pattern A

| Aspect | Pattern A (Metaclass) | Pattern B (Service) |
|--------|----------------------|---------------------|
| **Mapping** | 1:1 (class → plugin) | Many:1 (items → plugin) |
| **Metadata** | Simple (just a key) | Rich (8+ fields) |
| **Registration** | Automatic (class definition) | Discovery (introspection) |
| **Caching** | Not needed | Essential (2-level) |
| **Discovery** | Metaclass `__new__` | Service + ABC pattern |
| **Use Case** | Handlers, backends | Functions, formats |

## Best Practices

### 1. Use Abstract Base Class

Define clear contracts that all implementations must follow:

```python
class LibraryRegistryBase(ABC):
    @abstractmethod
    def discover_functions(self) -> Dict[str, FunctionMetadata]:
        """Each registry must implement discovery."""
        pass
```

### 2. Implement Caching

Discovery is expensive - always cache results:

```python
def _load_or_discover_functions(self) -> Dict[str, FunctionMetadata]:
    if self._cache_path.exists():
        cached = self._load_from_cache()
        if cached:
            return cached
    
    functions = self.discover_functions()
    self._save_to_cache(functions)
    return functions
```

### 3. Use Service Layer

Provide unified access through a service class:

```python
class RegistryService:
    @classmethod
    def get_all_functions_with_metadata(cls) -> Dict[str, FunctionMetadata]:
        """Single entry point for all registries."""
        pass
```

### 4. Leverage Generic Discovery

Use `discover_registry_classes()` for automatic registry discovery:

```python
registry_classes = discover_registry_classes(
    package_path=package.__path__,
    package_prefix=package.__name__ + ".",
    base_class=YourRegistryBase
)
```

## Examples in OpenHCS

### Function Registry System

**Location**: `openhcs/processing/backends/lib_registry/`

**Structure**:
- `unified_registry.py` - Base classes (LibraryRegistryBase, FunctionMetadata)
- `registry_service.py` - Discovery service
- `openhcs_registry.py` - OpenHCS native functions
- `pyclesperanto_registry.py` - GPU functions
- `scikit_image_registry.py` - CPU functions
- `cupy_registry.py` - GPU array functions

**Stats**: 574+ functions across 4 libraries

### Format Registry System

**Location**: `openhcs/processing/backends/experimental_analysis/`

**Structure**:
- `format_registry.py` - Base class (MicroscopeFormatRegistryBase)
- `format_registry_service.py` - Discovery service
- `imagexpress_registry.py` - ImageXpress format
- `operetta_registry.py` - Operetta format
- etc.

## Migration Guide

If you have a Pattern A system that's growing complex metadata, consider migrating to Pattern B:

1. **Create metadata dataclass** for your items
2. **Define abstract base class** with discovery contract
3. **Implement concrete registries** for each source
4. **Create service class** for unified access
5. **Add caching** at both registry and service levels
6. **Use generic discovery** utilities

## See Also

- [Pattern A: Metaclass Auto-Registration](pattern-a-metaclass-registry.md)
- [Pattern C: Functional Registry](pattern-c-functional-registry.md)
- [Pattern D: Manual Registration](pattern-d-manual-registration.md)
- [Registry Pattern Decision Tree](registry-framework.md#decision-tree)

