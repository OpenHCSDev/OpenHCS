Hi Martin,

I have no credentials and we've never met. I'm emailing because you authored PEP 487.

__init_subclass__ is the right hook. This moves the logic into type.__new__:

class AxesMeta(type):
    def __new__(mcs, name, bases, namespace, axes=None, **kwargs):
        cls = super().__new__(mcs, name, bases, namespace)
        parent_axes = {}
        for parent in cls.__mro__[1:]:
            for k, v in parent.__axes__.items():
                if k not in parent_axes:
                    parent_axes[k] = v
        if axes:
            parent_axes.update(axes)
        cls.__axes__ = MappingProxyType(parent_axes)
        return cls

Per-key MRO inheritance. In the real implementation, this would be in type.__new__ and every class would have __axes__ by default.

I have formal proofs that the design is sound—11k lines of Lean 4, no sorry. I'm not asking you to evaluate them, but if you're curious:

Paper 1 (axis selection): https://zenodo.org/records/18123532
Paper 2 (SSOT requirements): https://zenodo.org/records/18141366
Prototype: https://github.com/trissim/ObjectState/blob/main/src/objectstate/parametric_axes.py
Thread: https://discuss.python.org/t/semantic-axes-beyond-b-s-why-type-needs-extension/105628

Guido referred me to discuss.python.org. Responders didn't engage with the substance, suggested ChainMap in __init_subclass__ then moved it to Ideas. Guido, fairly: "I can't think of other venues."

I don't know where else to go. You'd know whether this is worth finishing.

Guido thread below.

Sincerely,
Tristan

