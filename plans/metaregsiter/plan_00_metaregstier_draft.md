Complete Plan: Generalize Auto-Registration Pattern Across OpenHCS
Executive Summary
Goal: Extract the auto-registration pattern from microscope handlers into a reusable framework that can be applied to any plugin system in OpenHCS.
Scope: Create generic metaprogramming utilities that work for:

Microscope handlers (existing)
Storage backends (existing)
Processing functions (existing)
Future plugin systems

Value Proposition: Enable plugin ecosystems without code modification, consistent patterns across codebase, reduced boilerplate, and extensibility for users.

Current State Assessment
Systems Already Using Auto-Registration

Microscope Handlers (openhcs/microscopes/microscope_base.py)

Uses MicroscopeHandlerMeta metaclass
Auto-registers handler classes
Manual metadata handler registration at end of files
Magic strings: 'Handler', 7 (length)


Storage Backends (openhcs/io/backend_registry.py)

Uses StorageBackendMeta metaclass
Auto-registers backend classes
Requires explicit _backend_type attribute
Has discovery service with module scanning


Processing Functions (openhcs/processing/func_registry.py)

Uses decorator-based registration
Registry service for external libraries
Complex hybrid system with multiple registries
Not using metaclass pattern


ZMQ Servers (openhcs/runtime/zmq_base.py)

Manual registration (no metaclass)
ABC-based with manual subclass tracking
Could benefit from auto-registration



Common Patterns Identified
All systems need:

Registry dict to store classes/functions
Auto-discovery of implementations
Naming conventions for key derivation
Optional metadata extraction
Lazy initialization to avoid import-time overhead
Plugin support for external extensions


Proposed Solution: Generic Registry Framework
Core Architecture
openhcs/core/registry_framework.py
├── RegistryConfig (dataclass)
├── AutoRegisterMeta (metaclass)
├── AutoDiscoverMixin (base class)
└── RegistryService (discovery utilities)
Design Principles

Convention over Configuration: Follow naming patterns, get auto-registration
Fail-Loud: Missing required classes/attributes crash immediately
Opt-In Complexity: Simple cases are simple, complex cases are possible
Zero Boilerplate: Subclasses just implement abstract methods
Plugin-Ready: External packages can extend without modification


Implementation Plan
Phase 1: Create Generic Framework (2-3 hours)
1.1: Core Data Structures
File: openhcs/core/registry_framework.py
pythonfrom dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Callable, Any, Type
from abc import ABCMeta
import sys
import logging

logger = logging.getLogger(__name__)


@dataclass
class RegistryConfig:
    """
    Configuration for auto-registration behavior.
    
    This defines how a plugin system should behave:
    - What to call classes (suffix)
    - Where to store them (registry dict)
    - What related classes to discover (parser, metadata, etc.)
    - How to derive registry keys from class names
    """
    
    # Required fields
    class_suffix: str  # e.g., 'Handler', 'Backend', 'Processor'
    registry_dict: Dict[str, Type]  # Global dict to populate
    
    # Optional fields
    related_classes: List[Tuple[str, str]] = field(default_factory=list)
    # List of (suffix, attr_name) for auto-discovery
    # Example: [('Parser', 'parser_class'), ('Config', 'config_class')]
    
    key_transform: Optional[Callable[[str], str]] = None
    # Function to transform class name → registry key
    # Default: strip suffix and lowercase
    
    auto_instantiate: bool = True
    # Whether base class should auto-instantiate related classes
    
    metadata_attrs: List[str] = field(default_factory=list)
    # Additional class attributes to extract and store
    # Example: ['description', 'version', 'author']
    
    allow_explicit_key: bool = True
    # Whether to allow explicit key via class attribute
    
    explicit_key_attr: str = '_registry_key'
    # Name of attribute for explicit key override
    
    def get_registry_key(self, class_name: str, explicit_key: Any = None) -> str:
        """Derive registry key from class name or explicit override."""
        if self.allow_explicit_key and explicit_key is not None:
            return str(explicit_key)
        
        if self.key_transform:
            return self.key_transform(class_name)
        
        # Default: strip suffix and lowercase
        if class_name.endswith(self.class_suffix):
            return class_name[:-len(self.class_suffix)].lower()
        return class_name.lower()
1.2: Auto-Registration Metaclass
pythonclass AutoRegisterMeta(ABCMeta):
    """
    Metaclass for automatic registration of plugin classes.
    
    Usage:
        1. Create a RegistryConfig
        2. Set as _registry_config on your ABC
        3. All concrete subclasses auto-register
    
    Example:
        class MicroscopeHandler(ABC, metaclass=AutoRegisterMeta):
            _registry_config = MICROSCOPE_REGISTRY_CONFIG
    """
    
    def __new__(cls, name, bases, attrs):
        new_class = super().__new__(cls, name, bases, attrs)
        
        # Only register concrete classes (not abstract base)
        if bases and not getattr(new_class, '__abstractmethods__', None):
            config = getattr(new_class, '_registry_config', None)
            
            if config is None:
                # No config = no registration (allow opt-out)
                return new_class
            
            # Get explicit key if provided
            explicit_key = getattr(new_class, config.explicit_key_attr, None)
            
            # Derive registration key
            registry_key = config.get_registry_key(name, explicit_key)
            
            # Store key on class
            setattr(new_class, config.explicit_key_attr, registry_key)
            
            # Register in global dict
            config.registry_dict[registry_key] = new_class
            
            # Extract and store metadata if configured
            if config.metadata_attrs:
                metadata = {
                    attr: getattr(new_class, attr, None)
                    for attr in config.metadata_attrs
                }
                # Store metadata alongside class (optional enhancement)
                if hasattr(config, 'metadata_dict'):
                    config.metadata_dict[registry_key] = metadata
            
            logger.debug(f"Auto-registered {name} as '{registry_key}'")
        
        return new_class
1.3: Auto-Discovery Mixin
pythonclass AutoDiscoverMixin:
    """
    Mixin for auto-discovery of related classes.
    
    Discovers related classes based on naming conventions:
    - ImageXpressHandler → ImageXpressFilenameParser
    - ImageXpressHandler → ImageXpressMetadataHandler
    
    Usage:
        class MicroscopeHandler(ABC, AutoDiscoverMixin, metaclass=AutoRegisterMeta):
            _registry_config = MICROSCOPE_REGISTRY_CONFIG
            
            def __init__(self, filemanager, pattern_format=None):
                self._auto_discover_related_classes(filemanager, pattern_format)
    """
    
    _registry_config: RegistryConfig
    
    def _auto_discover_related_classes(self, *init_args, **init_kwargs):
        """Auto-discover and instantiate related classes by convention."""
        config = self._registry_config
        
        if not config.auto_instantiate:
            return
        
        module = sys.modules[self.__class__.__module__]
        class_name = self.__class__.__name__
        
        # Derive prefix: ImageXpressHandler → ImageXpress
        if class_name.endswith(config.class_suffix):
            prefix = class_name[:-len(config.class_suffix)]
        else:
            prefix = class_name
        
        # Auto-discover each related class
        for suffix, attr_name in config.related_classes:
            related_name = f"{prefix}{suffix}"
            
            # Fail-loud if missing (convention violation)
            RelatedClass = getattr(module, related_name)
            
            # Instantiate and store
            try:
                instance = RelatedClass(*init_args, **init_kwargs)
            except TypeError:
                # Try without pattern_format
                try:
                    instance = RelatedClass(init_args[0]) if init_args else RelatedClass()
                except TypeError:
                    # Try no args
                    instance = RelatedClass()
            
            setattr(self, attr_name, instance)
            
            logger.debug(f"Auto-discovered {related_name} as {attr_name}")
1.4: Registry Discovery Service
pythondef discover_registry_classes(
    package_path: List[str],
    package_prefix: str,
    base_class: Type,
    registry_dict: Dict[str, Type],
    exclude_modules: Optional[set] = None
) -> Dict[str, Type]:
    """
    Discover and register all subclasses of base_class in package.
    
    Args:
        package_path: Package __path__ attribute
        package_prefix: Package name prefix (e.g., 'openhcs.microscopes.')
        base_class: Base class to find subclasses of
        registry_dict: Registry dict to populate
        exclude_modules: Module names to skip
    
    Returns:
        Registry dict (same as input, for chaining)
    """
    import importlib
    import pkgutil
    
    exclude_modules = exclude_modules or set()
    
    for _, module_name, _ in pkgutil.walk_packages(package_path, package_prefix):
        # Skip excluded modules
        if any(excluded in module_name for excluded in exclude_modules):
            continue
        
        try:
            # Import module (triggers metaclass registration)
            importlib.import_module(module_name)
            logger.debug(f"Discovered module: {module_name}")
        except Exception as e:
            logger.warning(f"Failed to import {module_name}: {e}")
    
    return registry_dict

Phase 2: Migrate Microscope Handlers (1-2 hours)
2.1: Create Microscope Registry Config
File: openhcs/microscopes/microscope_base.py
pythonfrom openhcs.core.registry_framework import (
    AutoRegisterMeta,
    AutoDiscoverMixin,
    RegistryConfig
)

# Global registries
MICROSCOPE_HANDLERS = {}
METADATA_HANDLERS = {}

# Registry configuration
MICROSCOPE_REGISTRY_CONFIG = RegistryConfig(
    class_suffix='Handler',
    registry_dict=MICROSCOPE_HANDLERS,
    related_classes=[
        ('FilenameParser', 'parser'),
        ('MetadataHandler', 'metadata_handler')
    ],
    auto_instantiate=True,
    allow_explicit_key=True,
    explicit_key_attr='_microscope_type'
)


class MicroscopeHandler(ABC, AutoDiscoverMixin, metaclass=AutoRegisterMeta):
    """Base handler with auto-registration and auto-discovery."""
    
    _registry_config = MICROSCOPE_REGISTRY_CONFIG
    
    def __init__(self, filemanager: FileManager, pattern_format: Optional[str] = None):
        """Auto-discover parser and metadata handler."""
        self._auto_discover_related_classes(filemanager, pattern_format)
        self.plate_folder = None
        
        # Auto-register metadata handler
        if hasattr(self, 'metadata_handler'):
            METADATA_HANDLERS[self._microscope_type] = self.metadata_handler.__class__
    
    @property
    @abstractmethod
    def root_dir(self) -> str:
        pass
    
    # ... rest of abstract interface
2.2: Update Handler Implementations
Files: imagexpress.py, opera_phenix.py, omero.py
Remove:

_microscope_type attribute (auto-derived, or keep for explicit override)
_metadata_handler_class attribute (not needed)
__init__ method (unless custom logic needed)
End-of-file registration code

Keep:

Abstract method implementations
Custom logic in _build_virtual_mapping, etc.

Example - ImageXpress:
pythonclass ImageXpressHandler(MicroscopeHandler):
    """ImageXpress microscope handler - zero boilerplate."""
    
    # Optional: explicit override if auto-derivation fails
    # _microscope_type = 'imagexpress'
    
    @property
    def root_dir(self) -> str:
        return "."
    
    @property
    def compatible_backends(self) -> List[Backend]:
        return [Backend.DISK]
    
    def _build_virtual_mapping(self, plate_path: Path, filemanager: FileManager) -> Path:
        # Custom logic...
        pass


class ImageXpressFilenameParser(FilenameParser):
    """Parser - naming convention enforced."""
    pass


class ImageXpressMetadataHandler(MetadataHandler):
    """Metadata handler - naming convention enforced."""
    pass

# No manual registration needed!
2.3: Handle Special Cases
OpenHCS (dynamic parser loading):
pythonclass OpenHCSMicroscopeHandler(MicroscopeHandler):
    """OpenHCS with deferred parser loading."""
    
    _microscope_type = 'openhcsdata'  # Explicit override
    
    def __init__(self, filemanager: FileManager, pattern_format: Optional[str] = None):
        # Skip auto-discovery for parser (load dynamically)
        self.filemanager = filemanager
        self.pattern_format = pattern_format
        self._parser = None
        
        # Auto-discover only metadata handler
        import sys
        module = sys.modules[self.__class__.__module__]
        MetadataClass = getattr(module, 'OpenHCSMetadataHandler')
        self.metadata_handler = MetadataClass(filemanager)
        
        self.plate_folder = None
    
    @property
    def parser(self):
        """Lazy-load parser from metadata."""
        if self._parser is None:
            # Existing dynamic loading logic...
            pass
        return self._parser

Phase 3: Migrate Storage Backends (30 minutes)
3.1: Update Backend Registry Config
File: openhcs/io/backend_registry.py
pythonfrom openhcs.core.registry_framework import AutoRegisterMeta, RegistryConfig

STORAGE_BACKENDS = {}

BACKEND_REGISTRY_CONFIG = RegistryConfig(
    class_suffix='Backend',
    registry_dict=STORAGE_BACKENDS,
    auto_instantiate=False,  # Backends instantiated lazily
    allow_explicit_key=True,
    explicit_key_attr='_backend_type'
)


# Update base class to use new metaclass
class StorageBackendMeta(AutoRegisterMeta):
    """Backward-compatible alias."""
    pass
Result: Existing backend code works unchanged, but now uses generic framework.

Phase 4: Migrate Processing Functions (1 hour)
4.1: Create Function Registry Config
File: openhcs/processing/func_registry.py
pythonfrom openhcs.core.registry_framework import RegistryConfig

FUNC_REGISTRY = {}

FUNCTION_REGISTRY_CONFIG = RegistryConfig(
    class_suffix='',  # No suffix for functions
    registry_dict=FUNC_REGISTRY,
    auto_instantiate=False,
    allow_explicit_key=True,
    explicit_key_attr='input_memory_type',
    key_transform=lambda name: getattr(name, 'input_memory_type', name.lower())
)
Note: Function registry is more complex (decorators, not classes). May need custom variant of framework or keep existing hybrid approach.
Decision: Keep processing function registry as-is (already well-designed), but document that it follows similar principles.

Phase 5: Documentation & Testing (1-2 hours)
5.1: Developer Guide
File: docs/developer/plugin_system.md
markdown# Plugin System Architecture

## Quick Start

To create a new plugin system:

1. Define your registry config:
```python
from openhcs.core.registry_framework import RegistryConfig

MY_PLUGINS = {}

MY_PLUGIN_CONFIG = RegistryConfig(
    class_suffix='Plugin',
    registry_dict=MY_PLUGINS,
    related_classes=[('Config', 'config')],
    auto_instantiate=True
)
```

2. Create your base class:
```python
from openhcs.core.registry_framework import AutoRegisterMeta, AutoDiscoverMixin

class MyPlugin(ABC, AutoDiscoverMixin, metaclass=AutoRegisterMeta):
    _registry_config = MY_PLUGIN_CONFIG
    
    def __init__(self, *args, **kwargs):
        self._auto_discover_related_classes(*args, **kwargs)
    
    @abstractmethod
    def process(self, data):
        pass
```

3. Implement plugins:
```python
class ExamplePlugin(MyPlugin):
    """Auto-registered as 'example'."""
    
    def process(self, data):
        return data * 2

class ExampleConfig:
    """Auto-discovered and instantiated."""
    pass
```

4. Use your plugins:
```python
plugin = MY_PLUGINS['example'](config_arg)
result = plugin.process(data)
```

## Naming Conventions

- Plugin class: `{Name}Plugin`
- Related classes: `{Name}{RelatedSuffix}`
- Registry key: derived by stripping suffix and lowercasing

## Advanced Features

- Explicit key override: Set `_registry_key` attribute
- Skip auto-instantiation: Set `auto_instantiate=False`
- Custom key derivation: Provide `key_transform` function
- Extract metadata: List attributes in `metadata_attrs`
5.2: User Plugin Guide
File: docs/user/creating_plugins.md
markdown# Creating OpenHCS Plugins

## Microscope Handler Plugins

To add support for a new microscope type:

1. Create a Python file (e.g., `zeiss_handler.py`)
2. Follow the naming convention:
   - `{Name}Handler`
   - `{Name}FilenameParser`
   - `{Name}MetadataHandler`

3. Implement the required interface:
```python
from openhcs.microscopes.microscope_base import MicroscopeHandler
from openhcs.microscopes.microscope_interfaces import FilenameParser, MetadataHandler

class ZeissHandler(MicroscopeHandler):
    @property
    def root_dir(self) -> str:
        return "Images"
    
    @property
    def compatible_backends(self) -> List[Backend]:
        return [Backend.DISK]

class ZeissFilenameParser(FilenameParser):
    # Implement parsing...
    pass

class ZeissMetadataHandler(MetadataHandler):
    # Implement metadata...
    pass
```

4. Place file in `~/.openhcs/plugins/`
5. OpenHCS will auto-discover on startup

No registration code needed!
5.3: Testing
File: tests/core/test_registry_framework.py
pythondef test_auto_registration():
    """Test that classes auto-register on definition."""
    test_registry = {}
    config = RegistryConfig(
        class_suffix='Test',
        registry_dict=test_registry
    )
    
    class TestBase(ABC, metaclass=AutoRegisterMeta):
        _registry_config = config
    
    class ExampleTest(TestBase):
        pass
    
    assert 'example' in test_registry
    assert test_registry['example'] == ExampleTest


def test_auto_discovery():
    """Test that related classes auto-discover."""
    # Create module with related classes
    # Test auto-instantiation
    # Verify attributes set correctly
    pass


def test_explicit_key_override():
    """Test explicit registry key override."""
    test_registry = {}
    config = RegistryConfig(
        class_suffix='Test',
        registry_dict=test_registry,
        allow_explicit_key=True
    )
    
    class TestBase(ABC, metaclass=AutoRegisterMeta):
        _registry_config = config
    
    class WeirdNameTest(TestBase):
        _registry_key = 'custom_key'
    
    assert 'custom_key' in test_registry
    assert 'weirdname' not in test_registry

Migration Checklist
Core Framework

 Create openhcs/core/registry_framework.py
 Implement RegistryConfig dataclass
 Implement AutoRegisterMeta metaclass
 Implement AutoDiscoverMixin mixin
 Implement discover_registry_classes function
 Write unit tests for framework

Microscope Handlers

 Update microscope_base.py to use framework
 Remove boilerplate from imagexpress.py
 Remove boilerplate from opera_phenix.py
 Remove boilerplate from omero.py
 Handle special case: openhcs.py (dynamic parser)
 Delete register_metadata_handler() function
 Update tests to verify auto-registration
 Test factory function still works
 Test auto-detection still works

Storage Backends

 Update backend_registry.py to use framework
 Verify existing backends still work
 Update tests

Documentation

 Write developer plugin guide
 Write user plugin guide
 Add examples to README
 Document naming conventions
 Document explicit override mechanism

Testing & Validation

 All existing tests pass
 New framework tests pass
 Manual test: create test plugin
 Manual test: external plugin package
 Performance: no import slowdown
 Performance: lazy initialization works


Decision Points
Decision 1: Processing Functions
Question: Should processing functions use the metaclass pattern?
Options:

A) Migrate to metaclass (consistency)
B) Keep decorator-based (already works well)
C) Hybrid approach (decorators + registry service)

Recommendation: Option B - Keep existing system. It's already well-designed for function registration, and functions don't fit the class hierarchy pattern as naturally.
Decision 2: Lazy vs Eager Initialization
Question: When should registries be populated?
Options:

A) Import-time (eager) - simple but slow imports
B) First-access (lazy) - fast imports but complex
C) Explicit initialize() call - manual but predictable

Recommendation: Option B - Lazy initialization for GUI/interactive use, but keep explicit discover_all_*() functions for scripts/tests that need deterministic behavior.
Decision 3: Backward Compatibility
Question: How to handle existing code that uses old patterns?
Options:

A) Breaking change - clean slate
B) Deprecation warnings - gradual migration
C) Full backward compatibility - keep old aliases

Recommendation: Option C - Full backward compatibility. Keep MicroscopeHandlerMeta as alias to AutoRegisterMeta, keep MICROSCOPE_HANDLERS dict, etc. No code breaks.

Success Metrics
Quantitative

 Lines of boilerplate removed: ~75 lines (5 handlers × 15 lines each)
 Framework lines added: ~200 lines (one-time cost)
 Net code reduction: Still positive when 4+ systems use framework
 Import time: No regression (lazy initialization)
 Test coverage: >90% for framework code

Qualitative

 New plugin creation: <30 minutes for experienced developer
 User plugin creation: Documented and tested
 Code clarity: Easier to understand handler implementations
 Maintainability: Centralized registration logic

---

## Findings

### Validation Against Codebase (2025-10-30)

#### 1. Critical Discovery: Infrastructure Already Exists

**Finding:** The plan proposes creating `openhcs/core/registry_framework.py` with generic discovery utilities, but **`openhcs/core/registry_discovery.py` already exists and is actively used** across the codebase.

**Evidence:**
- **File:** `openhcs/core/registry_discovery.py` (203 lines)
- **Functions:**
  - `discover_registry_classes()` - Non-recursive discovery using pkgutil + importlib
  - `discover_registry_classes_recursive()` - Recursive discovery using pkgutil.walk_packages
- **Current Usage:**
  - Microscope handlers: `handler_registry_service.py` uses `discover_registry_classes_recursive()`
  - Storage backends: `backend_registry.py` uses `discover_registry_classes()`
  - Function registry: `registry_service.py` uses `discover_registry_classes()`
  - Format registry: `format_registry_service.py` uses `discover_registry_classes_recursive()`

**Impact:** The plan's proposed discovery utilities (Section 4.1.3) are redundant. This infrastructure is already implemented, tested, and working.

---

#### 2. Two Distinct Registry Patterns Coexist

**Finding:** The codebase uses **two different registry patterns**, each appropriate for its domain:

**Pattern A: Metaclass Auto-Registration**
- **Used by:** Microscope handlers, Storage backends
- **Mechanism:** Metaclass `__new__` method registers classes in global dict on class definition
- **Examples:**
  - `MicroscopeHandlerMeta` → `MICROSCOPE_HANDLERS` dict
  - `StorageBackendMeta` → `STORAGE_BACKENDS` dict

**Pattern B: Service-Based Registry**
- **Used by:** Function registry
- **Mechanism:** Abstract base class + service class that discovers and aggregates
- **Examples:**
  - `LibraryRegistryBase` (abstract) → `RegistryService` (discovery + aggregation)
  - Each library has a registry class (CupyRegistry, PyclesperantoRegistry, etc.)
  - Returns rich metadata objects (`FunctionMetadata` dataclass)

**Analysis:** Pattern B is used for functions because:
- Multiple functions per library (not 1:1 like handlers/backends)
- Complex metadata requirements (FunctionMetadata with 8 fields)
- Need for aggregation across libraries (574+ functions)
- Service pattern provides better separation of concerns

**Impact:** The plan assumes all systems should use metaclass registration, but Pattern B is deliberately different and appropriate for its domain.

---

#### 3. Metaclass Code Duplication Assessment

**Finding:** MicroscopeHandlerMeta and StorageBackendMeta share similar structure but have domain-specific differences.

**Common Pattern (~15 lines):**
```python
def __new__(cls, name, bases, attrs):
    new_class = super().__new__(cls, name, bases, attrs)
    if not getattr(new_class, '__abstractmethods__', None):  # Check if concrete
        registry_key = <derive or get key>
        GLOBAL_REGISTRY[registry_key] = new_class
        new_class._registry_key = registry_key
    return new_class
```

**Domain-Specific Differences:**

**MicroscopeHandlerMeta (60 lines):**
- Derives key from class name: `ImageXpressHandler` → `'imagexpress'`
- Fallback logic: `name[:-7].lower()` if ends with 'Handler'
- **Additional feature:** Auto-discovers and registers metadata handlers via `_metadata_handler_class` attribute
- Registers to two dicts: `MICROSCOPE_HANDLERS` and `METADATA_HANDLERS`

**StorageBackendMeta (53 lines):**
- Requires explicit `_backend_type` attribute (e.g., `Backend.DISK.value`)
- Skips registration if `_backend_type` is None (allows abstract intermediates)
- Simpler: Only registers to `STORAGE_BACKENDS`

**Duplication Estimate:** ~30-40 lines of similar code across both metaclasses.

**Trade-off Analysis:**
- **Abstracting to generic AutoRegisterMeta:** Saves ~30 lines, adds abstraction complexity
- **Keeping separate:** Clear, domain-specific, easy to understand and modify
- **Current state:** Working well, tested, no reported issues

---

#### 4. Auto-Discovery Patterns Already Implemented

**Finding:** The plan proposes `AutoDiscoverMixin` for convention-based discovery, but this is already implemented via:

**Convention-Based Discovery (Microscope Handlers):**
- Pattern: `ImageXpressHandler` → `ImageXpressFilenameParser` (by convention)
- Implementation: Parser is instantiated in handler's `__init__` method
- Example from `imagexpress.py`:
  ```python
  def __init__(self, filemanager: FileManager, pattern_format: Optional[str] = None):
      self.parser = ImageXpressFilenameParser(filemanager, pattern_format)
      self.metadata_handler = ImageXpressMetadataHandler(filemanager)
  ```

**Explicit Attribute-Based Discovery (Metadata Handlers):**
- Pattern: Set `_metadata_handler_class` attribute after class definition
- Metaclass auto-registers it in `METADATA_HANDLERS` dict
- Example from `openhcs.py`:
  ```python
  OpenHCSMicroscopeHandler._metadata_handler_class = OpenHCSMetadataHandler
  register_metadata_handler(OpenHCSMicroscopeHandler, OpenHCSMetadataHandler)
  ```

**Impact:** The proposed `AutoDiscoverMixin` would duplicate existing, working patterns.