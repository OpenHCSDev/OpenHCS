Fair point about the paper. Here's the short version with real code.

---

### Real Example: Plugin Registration

I maintain OpenHCS (microscopy automation). We have ~8 microscope handlers that auto-register themselves. Here's the actual pattern today:

```python
# Real code from openhcs/microscopes/imagexpress.py
class ImageXpressHandler(MicroscopeHandler):
    _microscope_type = 'imagexpress'  # <- this is the registry key
    _metadata_handler_class = None     # <- secondary registration
    
    def microscope_type(self) -> str:  # <- wait, is this related?
        return 'imagexpress'
```

A metaclass reads `_microscope_type` and registers the class:

```python
# openhcs/core/auto_register_meta.py (simplified)
class AutoRegisterMeta(ABCMeta):
    def __new__(mcs, name, bases, attrs):
        cls = super().__new__(mcs, name, bases, attrs)
        key = getattr(cls, '_microscope_type', None)
        if key:
            MICROSCOPE_HANDLERS[key] = cls
        return cls
```

**The problem:** Looking at `ImageXpressHandler.__dict__`, you see:

```
_microscope_type        # registry metadata
_metadata_handler_class # more metadata  
microscope_type         # actual method (returns same string!)
parser                  # real attribute
root_dir                # real property
```

Which of these are "metadata for framework machinery" vs "actual class behavior"? You can't tell programmatically. Neither can a type checker.

---

### With `__axes__`

```python
class ImageXpressHandler(MicroscopeHandler, 
                         axes={"registry_key": "imagexpress"}):
    
    @property
    def microscope_type(self) -> str:
        return self.__axes__["registry_key"]  # or just return the string
```

Now introspection is trivial:

```python
ImageXpressHandler.__axes__   # {"registry_key": "imagexpress"}
ImageXpressHandler.__dict__   # {microscope_type, parser, root_dir, ...}
```

Framework machinery reads `__axes__`. Application code reads `__dict__`. No collision, no guessing.

---

### Why not `**kwargs` to `type()`?

You can already pass kwargs:

```python
MyClass = type("MyClass", (Base,), {}, registry="foo")  # works today!
```

But where does `registry="foo"` go? Into `__dict__`, lost among methods. There's no standard place to find it. Every framework invents `_registry_`, `__registry__`, `FORMAT_NAME`, `_microscope_type`...

`__axes__` is just "here's the standard place for that metadata."


