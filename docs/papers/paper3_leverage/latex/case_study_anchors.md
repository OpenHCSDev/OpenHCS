# Case Study File Anchors (after-state loci)

Anchors collected so far; add pre-state references as available.

## CS1: Metaclass auto-registration (DOF_post = 1)
- Metaclass that performs registration at class definition time: `openhcs/core/auto_register_meta.py`:379-468.
- Domain uses (no manual register calls): e.g.
  - `openhcs/io/base.py` (BackendBase metaclass=AutoRegisterMeta)
  - `openhcs/runtime/zmq_base.py` (ZMQServer metaclass=AutoRegisterMeta)
  - `openhcs/processing/backends/experimental_analysis/format_registry.py` (MicroscopeFormatRegistryBase metaclass=AutoRegisterMeta)

## CS2: Configuration consolidation (DOF_post = 5 overrides)
- Global-default injection decorator and lazy rebuild: `openhcs/config_framework/lazy_factory.py`:918-980 (`create_global_default_decorator`).
- Lazy resolution binding for inherited fields: `openhcs/config_framework/lazy_factory.py`:354-420 (`bind_lazy_resolution_to_class`, resolver/getattribute bindings).

## CS3: Genericized widget ops (duck-typing elimination) (DOF_post = 1)
- Centralized ABC-based widget operations replacing dispatch tables: `openhcs/ui/shared/widget_operations.py`:1-200.

## TODO: anchors for remaining cases (after-state loci)
- CS4 Database schema normalization (DOF_post=1)
- CS5 Type annotations SSOT (DOF_post=1)
- CS6 Error handling centralization (DOF_post=2)
- CS7 Logging format (DOF_post=1)
- CS8 Validation rules (DOF_post=1)
- CS9 Serialization (DOF_post=1)
- CS10 Auth middleware (DOF_post=1)
- CS11 Cache strategy (DOF_post=1)
- CS12 Query builder (DOF_post=2)
- CS13 Event handlers (DOF_post=1)
