# PEP Draft: Parametric Type Axes

**Status**: Draft
**Author**: Tristan Simas
**Created**: 2026-01-03
**Updated**: 2026-01-12

## Abstract

This PEP proposes extending `type()` to accept an `axes={}` parameter for attaching semantic metadata to classes. Axes are inherited per-key following MRO, stored as `__axes__` (immutable), and introspectable at runtime.

## Motivation

### The problem

Python's `type(name, bases, namespace)` provides two semantic axes:
- **B (Bases)**: Inheritance hierarchy (`__bases__`)
- **S (Namespace)**: Attribute dictionary (`__dict__`)

Frameworks that need additional metadata (registry keys, scope identifiers, handler mappings) resort to:
1. Underscore attributes (`_microscope_type = "imagexpress"`)
2. Configuration objects (`RegistryConfig(key_attribute='_backend_type', ...)`)
3. Custom metaclasses that walk MRO to find these attributes

This scatters metadata across class bodies, configuration objects, and metaclass logic. The metadata cannot be introspected uniformly.

### Why this is necessity, not convenience

These workarounds are not stylistic choices—they exist because certain domains *require* metadata axes that Python's type system does not provide. The workarounds simulate what the language should express directly.

Machine-checked proofs (9,000 lines of Lean 4) establish:
1. Some domains require axes beyond (B, S)
2. Without native axis support, Single Source of Truth (SSOT) is impossible for those domains
3. The current workarounds cannot be made correct—they are structurally incomplete

This is not "loops are nicer than goto." This is "some programs cannot be expressed without loops."

### Zen of Python alignment

> *Explicit is better than implicit.*

`axes={"registry": R}` is explicit. `_registry_type = "foo"` is a convention that only works if a metaclass knows to look for it.

> *There should be one—and preferably only one—obvious way to do it.*

Currently there are many ways: underscore attributes, class decorators, `__init_subclass__`, metaclass `__new__`, external registration calls. Axes provide one obvious way.

> *Simple is better than complex.*

A 12-line metaclass replaces hundreds of lines of registry machinery.

> *If the implementation is hard to explain, it's a bad idea.*

"Axes are inherited per-key via MRO" is one sentence. Explaining `AutoRegisterMeta` with `RegistryConfig`, `SecondaryRegistry`, and `LazyDiscoveryDict` takes pages.

## Specification

### Extended `type()` signature

```python
type(name, bases, namespace, /, *, axes=None, **kwargs)
```

### `__axes__` attribute

Every class gains `__axes__`: a `MappingProxyType` (immutable) containing inherited and declared axes.

### Per-key MRO inheritance

Axes inherit per-key, not all-or-nothing. Each key follows MRO independently; child declarations override inherited values for that key only.

### Prototype implementation

This metaclass demonstrates what `type.__new__` would do natively:

```python
from types import MappingProxyType

class AxesMeta(type):
    def __new__(mcs, name, bases, namespace, axes=None, **kwargs):
        cls = super().__new__(mcs, name, bases, namespace)
        parent_axes = {}
        for parent in cls.__mro__[1:]:
            for k, v in getattr(parent, '__axes__', {}).items():
                if k not in parent_axes:
                    parent_axes[k] = v
        if axes:
            parent_axes.update(axes)
        cls.__axes__ = MappingProxyType(parent_axes)
        return cls
```

## Examples (from OpenHCS codebase)

### Before: Microscope handler registration

```python
# openhcs/microscopes/microscope_base.py
class MicroscopeHandler(ABC, metaclass=AutoRegisterMeta):
    __registry_key__ = '_microscope_type'
    __key_extractor__ = extract_key_from_handler_suffix
    __secondary_registries__ = [
        SecondaryRegistry(
            registry_dict=METADATA_HANDLERS,
            key_source=PRIMARY_KEY,
            attr_name='_metadata_handler_class'
        )
    ]

class ImageXpressHandler(MicroscopeHandler):
    _microscope_type = "imagexpress"
    _metadata_handler_class = ImageXpressMetadataHandler
```

### After: With axes

```python
class MicroscopeHandler(ABC, metaclass=AxesMeta):
    pass

class ImageXpressHandler(
    MicroscopeHandler,
    axes={
        "microscope_type": "imagexpress",
        "metadata_handler": ImageXpressMetadataHandler,
        "registry": MICROSCOPE_HANDLERS,
    }
):
    pass

# Introspection:
ImageXpressHandler.__axes__["microscope_type"]  # "imagexpress"
```

### Before: Storage backend registration

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

### After: With axes

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

## What dies

- Underscore attribute conventions (`_microscope_type`)
- `RegistryConfig` objects
- `SecondaryRegistry` objects
- `__registry_key__`, `__key_extractor__`, `__secondary_registries__`
- Per-framework metaclass complexity

## Audience

This proposal is for **framework authors**, not everyday application developers.

Most Python developers will never write `axes={}`. They don't write metaclasses, registries, or plugin systems. That's fine—this feature is invisible to them. `__axes__` defaults to `{}`, and nothing changes for code that doesn't use it.

But framework authors—the people building Django, Flask, Pydantic, SQLAlchemy, pytest, and countless internal systems—deal with this problem constantly. They write the metaclass machinery that axes would replace. They maintain the underscore-attribute conventions. They debug the registry conflicts.

This PEP makes frameworks simpler, which makes the code that uses those frameworks simpler. The benefit flows downstream even to developers who never see `axes={}`.

## Backward Compatibility

- `type(name, bases, ns)` unchanged
- `__axes__` defaults to `{}` for existing classes
- No changes to `isinstance()`, `issubclass()`, MRO, or `typing`
- Invisible to code that doesn't use it

## Design Decisions

**Immutable**: `__axes__` is `MappingProxyType`. Axes are fixed at class creation.

**Per-key inheritance**: Each axis key inherits independently via MRO. This matches how method resolution works—closer parents win—but applied per-key to metadata.

**No standard axes**: This PEP does not define standard axis names. Frameworks choose their own (`scope`, `registry`, `version`, etc.).

## Formal Foundation

The design is backed by machine-checked proofs (9,000 lines of Lean 4, no `sorry`):

- **Paper 1**: Axis selection completeness ([Zenodo](https://zenodo.org/records/18173678))
- **Paper 2**: SSOT requirements ([Zenodo](https://zenodo.org/records/18185711))
- **Prototype**: [ObjectState](https://github.com/trissim/ObjectState/blob/main/src/objectstate/parametric_axes.py)

## References

- PEP 487: `__init_subclass__` (Martin Teichmann) — this proposal moves axis logic into `type.__new__`
- OpenHCS: High-content screening framework using parametric axes

