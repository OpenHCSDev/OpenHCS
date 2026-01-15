# Parametric Axes Refactoring Analysis

This document analyzes how each OpenHCS subsystem could benefit from parametric axes (`__axes__`), with concrete before/after comparisons.

## Summary Table

| Subsystem | Benefit Level | Key Improvement |
|-----------|---------------|-----------------|
| AutoRegisterMeta | **HIGH** | Eliminate `_key_attribute` convention entirely |
| Microscope Handlers | **HIGH** | `axes={"microscope_type": "imagexpress"}` replaces `_microscope_type` |
| Storage Backends | **HIGH** | Same pattern as microscope handlers |
| ObjectState | **HIGH** | `scope` becomes intrinsic; provenance tracking simplified |
| Library Registries | **MEDIUM** | Declarative metadata vs methods |
| Lazy Dataclasses | **MEDIUM** | `{"lazy": True, "concrete_type": T}` for introspection |
| Pipeline Steps | **LOW** | Step metadata is mostly instance-level, not type-level |
| Metadata Handlers | **MEDIUM** | Secondary registrations become axes lookups |

---

## 1. AutoRegisterMeta (Core Framework)

**Current complexity:**
```python
# openhcs/core/auto_register_meta.py

class AutoRegisterMeta(ABCMeta):
    def __new__(mcs, name, bases, namespace, **kwargs):
        cls = super().__new__(mcs, name, bases, namespace)
        
        # 1. Find registry config (walks MRO)
        config = mcs._find_registry_config(cls, bases)
        
        # 2. Extract key using underscore attribute
        key = getattr(cls, config.key_attribute, None)  # e.g., '_microscope_type'
        
        # 3. Optionally run key_extractor function
        if config.key_extractor:
            key = config.key_extractor(name, cls)
        
        # 4. Register in dictionary
        if key:
            config.registry_dict[key] = cls
        
        return cls
```

**With axes:**
```python
class AutoRegisterMeta(ABCMeta):
    def __new__(mcs, name, bases, namespace, *, axes=None, **kwargs):
        cls = super().__new__(mcs, name, bases, namespace)
        cls.__axes__ = axes or {}
        
        # Key is now explicit in axes
        registry_axis = cls.__axes__.get("registry")
        key = cls.__axes__.get("registry_key")
        
        if registry_axis and key:
            registry_axis[key] = cls
        
        return cls
```

**Complexity reduction:**
- No `_underscore` attribute convention
- No `key_attribute` configuration field
- No `key_extractor` functions
- Key is explicit and introspectable

---

## 2. Microscope Handlers

**Current:**
```python
# openhcs/microscopes/microscope_base.py

class MicroscopeHandler(ABC, metaclass=AutoRegisterMeta):
    __registry_key__ = '_microscope_type'
    __key_extractor__ = extract_key_from_handler_suffix
    __skip_if_no_key__ = False
    __secondary_registries__ = [
        SecondaryRegistry(
            registry_dict=METADATA_HANDLERS,
            key_source=PRIMARY_KEY,
            attr_name='_metadata_handler_class'
        )
    ]

# Concrete handler
class ImageXpressHandler(MicroscopeHandler):
    _microscope_type = "imagexpress"
    _metadata_handler_class = ImageXpressMetadataHandler
```

**With axes:**
```python
class MicroscopeHandler(ABC, metaclass=AxesMeta):
    pass  # No configuration needed on base

# Concrete handler - all metadata is explicit
class ImageXpressHandler(
    MicroscopeHandler,
    axes={
        "microscope_type": "imagexpress",
        "metadata_handler": ImageXpressMetadataHandler,
        "registry": MICROSCOPE_HANDLERS,
    }
):
    pass

# Registration happens in AxesMeta.__new__:
# if "registry" in cls.__axes__ and "microscope_type" in cls.__axes__:
#     cls.__axes__["registry"][cls.__axes__["microscope_type"]] = cls
```

**Benefits:**
- No underscore attributes (`_microscope_type` → axes)
- No secondary registry configuration (just another axis)
- Introspectable: `ImageXpressHandler.__axes__["microscope_type"]`
- IDE autocomplete works on axes keys

---

## 3. Storage Backends

**Current:**
```python
class BackendBase(metaclass=AutoRegisterMeta):
    __registry_key__ = '_backend_type'
    __registry_config__ = RegistryConfig(
        registry_dict=LazyDiscoveryDict(),
        key_attribute='_backend_type',
        skip_if_no_key=True,
        registry_name='backend',
        discovery_package='openhcs.io',
    )

class ZarrBackend(BackendBase):
    _backend_type = "zarr"
```

**With axes:**
```python
class BackendBase(metaclass=AxesMeta):
    pass

class ZarrBackend(
    BackendBase,
    axes={
        "backend_type": "zarr",
        "registry": BACKEND_REGISTRY,
        "discovery_package": "openhcs.io",
    }
):
    pass
```

**Same benefits as microscope handlers.**

---

## 4. ObjectState (Scope Hierarchy)

**Current:**
```python
class ObjectState:
    def __init__(self, object_instance, scope_id: Optional[str] = None, ...):
        self.scope_id = scope_id  # e.g., "/plate::step_0"
        self._live_provenance: Dict[str, Tuple[str, type]] = {}  # Parallel structure!
    
    def get_provenance(self, param_name: str) -> Optional[Tuple[str, type]]:
        result = self._live_provenance.get(param_name)
        if result is None:
            return None
        scope_id, source_type = result
        return (scope_id, source_type)
```

**With axes (instance-level):**
```python
class ObjectState(AxesBase):
    def __init__(self, object_instance, *, scope: str, **kwargs):
        super().__init__(axes={"scope": scope})
        # NO _live_provenance - provenance IS the ObjectState reference
    
    def get_provenance(self, param_name: str) -> Optional['ObjectState']:
        # Returns the ObjectState that provided the value
        return self._field_sources.get(param_name)
    
    # Caller can then do:
    # source_state = obj.get_provenance("field")
    # source_state.__axes__["scope"]  # "/parent::step_0"
```

**Benefits:**
- Eliminates `_live_provenance` parallel structure entirely
- Provenance is intrinsic (ObjectState reference carries scope)
- `StateSnapshot` drops from 5 fields to 4
- All invalidation logic simplified (one structure, not two)

---

## 5. Library Registries

**Current:**
```python
class LibraryRegistryBase(ABC, metaclass=AutoRegisterMeta):
    @abstractmethod
    def get_library_name(self) -> str: ...
    
    @abstractmethod
    def get_display_name(self) -> str: ...
    
    @abstractmethod
    def get_module_patterns(self) -> List[str]: ...

class OpenHCSRegistry(LibraryRegistryBase):
    def get_library_name(self) -> str:
        return "openhcs"
    
    def get_display_name(self) -> str:
        return "OpenHCS"
    
    def get_module_patterns(self) -> List[str]:
        return ["openhcs"]
```

**With axes:**
```python
class LibraryRegistryBase(ABC, metaclass=AxesMeta):
    pass

class OpenHCSRegistry(
    LibraryRegistryBase,
    axes={
        "library_name": "openhcs",
        "display_name": "OpenHCS",
        "module_patterns": ["openhcs"],
    }
):
    pass

# Access: OpenHCSRegistry.__axes__["display_name"]
```

**Benefits:**
- Static metadata is declarative, not methods
- Methods reserved for behavior, not data
- Uniform introspection across all registries

---

## 6. Lazy Dataclasses

**Current:**
```python
# Lazy class created dynamically
LazyStepConfig = LazyDataclassFactory.make_lazy_simple(StepConfig)

# How to tell if a class is lazy?
is_lazy = cls.__name__.startswith("Lazy")  # Fragile!
# Or:
is_lazy = cls in _lazy_type_registry  # Requires module-level dict
```

**With axes:**
```python
LazyStepConfig = LazyDataclassFactory.make_lazy_simple(
    StepConfig,
    axes={"lazy": True, "concrete_type": StepConfig}
)

# Introspection is now standard:
is_lazy = getattr(cls, "__axes__", {}).get("lazy", False)
concrete = cls.__axes__.get("concrete_type")
```

**Benefits:**
- No naming conventions or separate registries
- Standard introspection pattern
- Concrete type reference is explicit

---

## 7. Pipeline Steps

**Lower benefit** - step metadata is mostly instance-level (name, description, enabled), not type-level.

However, step *categories* could use axes:

```python
class FunctionStep(
    AbstractStep,
    axes={"step_category": "function", "configurable": True}
):
    pass

class QCStep(
    AbstractStep,
    axes={"step_category": "qc", "breaks_chain": True}
):
    pass
```

This would enable:
- Step palette organization by `__axes__["step_category"]`
- Compile-time validation based on axes

---

## 8. Metadata Handlers (Secondary Registries)

**Current:**
```python
__secondary_registries__ = [
    SecondaryRegistry(
        registry_dict=METADATA_HANDLERS,
        key_source=PRIMARY_KEY,
        attr_name='_metadata_handler_class'
    )
]
```

**With axes:**
Secondary registrations become additional axes:

```python
class ImageXpressHandler(
    MicroscopeHandler,
    axes={
        "microscope_type": "imagexpress",
        "metadata_handler": ImageXpressMetadataHandler,  # Was secondary registry
    }
):
    pass
```

**Benefits:**
- No `SecondaryRegistry` class needed
- No `attr_name` configuration
- All registrations are uniform axes lookups

---

## Conclusion

Parametric axes would allow OpenHCS to:

1. **Eliminate `AutoRegisterMeta`** complexity by ~60%
2. **Remove all `_underscore` attribute conventions**
3. **Simplify ObjectState provenance tracking** (biggest win)
4. **Unify introspection** across all subsystems
5. **Make metadata declarative** instead of method-based

The highest-value refactors are:
1. **ObjectState** — eliminates parallel data structure
2. **AutoRegisterMeta** — simplifies core framework machinery
3. **Microscope/Backend handlers** — cleaner plugin declaration

