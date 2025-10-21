"""
Unified registry base class for external library function registration.

This module provides a common base class that eliminates ~70% of code duplication
across library registries (pyclesperanto, scikit-image, cupy, etc.) while enforcing
consistent behavior and making it impossible to skip dynamic testing or hardcode
function lists.

Key Benefits:
- Eliminates ~1000+ lines of duplicated code
- Enforces consistent testing and registration patterns
- Makes adding new libraries trivial (60-120 lines vs 350-400)
- Centralizes bug fixes and improvements
- Type-safe abstract interface prevents shortcuts

Architecture:
- LibraryRegistryBase: Abstract base class with common functionality
- ProcessingContract: Unified contract enum across all libraries
- Dimension error adapter factory for consistent error handling
- Integrated caching system using existing cache_utils.py patterns
"""

import importlib
import inspect
import json
import logging
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum
from functools import wraps
from typing import Any, Callable, Dict, List, Optional, Tuple


from openhcs.core.xdg_paths import get_cache_file_path
from openhcs.core.memory.stack_utils import unstack_slices, stack_slices

logger = logging.getLogger(__name__)


# Enums for OpenHCS principle compliance (replace magic strings)
class ModuleFilterComponents(Enum):
    """Components to filter out when generating tags from module paths."""
    BACKENDS = "backends"
    PROCESSING = "processing"
    OPENHCS = "openhcs"

    @classmethod
    def should_skip(cls, component: str) -> bool:
        """Check if component should be skipped in tag generation."""
        return any(component == item.value for item in cls)


class ProcessingContract(Enum):
    """
    Unified contract classification with direct method execution.
    """
    PURE_3D = "_execute_pure_3d"
    PURE_2D = "_execute_pure_2d"
    FLEXIBLE = "_execute_flexible"
    VOLUMETRIC_TO_SLICE = "_execute_volumetric_to_slice"

    def execute(self, registry, func, image, *args, **kwargs):
        """Execute the contract method on the registry."""
        method = getattr(registry, self.value)
        return method(func, image, *args, **kwargs)


@dataclass(frozen=True)
class FunctionMetadata:
    """Clean metadata with no library-specific leakage."""

    # Core fields only
    name: str
    func: Callable
    contract: ProcessingContract
    registry: 'LibraryRegistryBase'  # Reference to the registry that registered this function - REQUIRED
    module: str = ""
    doc: str = ""
    tags: List[str] = field(default_factory=list)
    original_name: str = ""  # Original function name for cache reconstruction

    def get_memory_type(self) -> str:
        """
        Get the actual memory type (backend) of this function.

        Returns the function's input_memory_type if available, otherwise falls back
        to the registry's memory type. This ensures UI shows the actual backend
        (cupy, numpy, etc.) instead of the registry name (openhcs).

        Returns:
            Memory type string (e.g., "cupy", "numpy", "torch", "pyclesperanto")
        """
        # First try to get memory type from function attributes
        if hasattr(self.func, 'input_memory_type'):
            return self.func.input_memory_type
        elif hasattr(self.func, 'output_memory_type'):
            return self.func.output_memory_type
        elif hasattr(self.func, 'backend'):
            return self.func.backend

        # Fallback to registry memory type
        return self.registry.get_memory_type()

    def get_registry_name(self) -> str:
        """
        Get the registry name that registered this function.

        Returns:
            Registry name string (e.g., "openhcs", "skimage", "cupy", "pyclesperanto")
        """
        return self.registry.library_name




class LibraryRegistryBase(ABC):
    """
    Minimal ABC for all library registries.

    Provides only essential contracts that all registries must implement,
    regardless of whether they use runtime testing or explicit contracts.
    """

    # Common exclusions across all libraries
    COMMON_EXCLUSIONS = {
        'imread', 'imsave', 'load', 'save', 'read', 'write',
        'show', 'imshow', 'plot', 'display', 'view', 'visualize',
        'info', 'help', 'version', 'test', 'benchmark'
    }

    # Abstract class attributes - each implementation must define these
    MODULES_TO_SCAN: List[str]
    MEMORY_TYPE: str  # Memory type string value (e.g., "pyclesperanto", "cupy", "numpy")
    FLOAT_DTYPE: Any  # Library-specific float32 type (np.float32, cp.float32, etc.)

    def __init__(self, library_name: str):
        """
        Initialize registry for a specific library.

        Args:
            library_name: Name of the library (e.g., "pyclesperanto", "skimage")
        """
        self.library_name = library_name
        self._cache_path = get_cache_file_path(f"{library_name}_function_metadata.json")





    # ===== ESSENTIAL ABC METHODS =====

    # ===== LIBRARY IDENTIFICATION =====
    @abstractmethod
    def get_library_version(self) -> str:
        """Get library version for cache validation."""
        pass

    @abstractmethod
    def is_library_available(self) -> bool:
        """Check if the library is available for import."""
        pass

    # ===== FUNCTION DISCOVERY =====
    @abstractmethod
    def discover_functions(self) -> Dict[str, FunctionMetadata]:
        """Discover and return function metadata. Must be implemented by subclasses."""
        pass

    # ===== CONTRACT HANDLING =====
    def apply_contract_wrapper(self, func: Callable, contract: ProcessingContract) -> Callable:
        """Apply contract-specific wrapper for all contract types."""
        from functools import wraps
        import inspect

        if contract == ProcessingContract.FLEXIBLE:
            # Check if function already has slice_by_slice parameter
            original_sig = inspect.signature(func)
            param_names = [p.name for p in original_sig.parameters.values()]

            if 'slice_by_slice' in param_names:
                # Function already has slice_by_slice, just ensure type hint is correct
                if hasattr(func, '__annotations__'):
                    func.__annotations__['slice_by_slice'] = bool
                else:
                    func.__annotations__ = {'slice_by_slice': bool}
                return func

            # Add slice_by_slice parameter
            new_params = list(original_sig.parameters.values())
            slice_param = inspect.Parameter(
                'slice_by_slice',
                inspect.Parameter.KEYWORD_ONLY,
                default=False,
                annotation=bool  # Explicit bool type hint for UI
            )

            # Insert before any VAR_KEYWORD (**kwargs) parameter
            insert_index = len(new_params)
            for i, param in enumerate(new_params):
                if param.kind == inspect.Parameter.VAR_KEYWORD:
                    insert_index = i
                    break

            new_params.insert(insert_index, slice_param)

            # Create the wrapper function
            @wraps(func)
            def flexible_wrapper(image, *args, slice_by_slice: bool = False, **kwargs):
                func.slice_by_slice = slice_by_slice
                return contract.execute(self, func, image, *args, **kwargs)

            # Apply the modified signature AFTER @wraps
            new_sig = original_sig.replace(parameters=new_params)
            flexible_wrapper.__signature__ = new_sig

            # Preserve original annotations and add slice_by_slice
            if hasattr(func, '__annotations__'):
                flexible_wrapper.__annotations__ = func.__annotations__.copy()
            else:
                flexible_wrapper.__annotations__ = {}
            flexible_wrapper.__annotations__['slice_by_slice'] = bool

            flexible_wrapper.slice_by_slice = False
            return flexible_wrapper
        else:
            # For other contracts, wrap with contract execution
            @wraps(func)
            def contract_wrapper(image, *args, **kwargs):
                return contract.execute(self, func, image, *args, **kwargs)

            return contract_wrapper

    def _inject_optional_dataclass_params(self, func: Callable) -> Callable:
        """Inject optional lazy dataclass parameters into function signature.

        Can be disabled by setting ENABLE_CONFIG_INJECTION = False.
        """
        # Configuration flag to enable/disable config injection
        ENABLE_CONFIG_INJECTION = False  # Set to True to re-enable config injection

        if not ENABLE_CONFIG_INJECTION:
            return func  # Return function unchanged when disabled

        # Original injection logic (commented out for now but preserved)
        import inspect
        from functools import wraps
        from typing import Optional

        # Get original signature
        original_sig = inspect.signature(func)
        original_params = list(original_sig.parameters.values())

        # Import existing lazy config types
        from openhcs.core.config import LazyNapariStreamingConfig, LazyFijiStreamingConfig, LazyStepMaterializationConfig

        # Define common lazy dataclass parameters to inject
        dataclass_params = [
            ('napari_streaming_config', 'Optional[LazyNapariStreamingConfig]', LazyNapariStreamingConfig),
            ('fiji_streaming_config', 'Optional[LazyFijiStreamingConfig]', LazyFijiStreamingConfig),
            ('step_materialization_config', 'Optional[LazyStepMaterializationConfig]', LazyStepMaterializationConfig),
        ]

        # Check if any parameters need to be added
        existing_param_names = {p.name for p in original_params}
        params_to_add = [(name, type_hint, lazy_class) for name, type_hint, lazy_class in dataclass_params
                        if name not in existing_param_names]

        if not params_to_add:
            return func  # No parameters to add

        # Create new parameters
        new_params = original_params.copy()

        # Find insertion point (before **kwargs if it exists)
        insert_index = len(new_params)
        for i, param in enumerate(new_params):
            if param.kind == inspect.Parameter.VAR_KEYWORD:
                insert_index = i
                break

        # Add dataclass parameters
        for param_name, type_hint, lazy_class in params_to_add:
            new_param = inspect.Parameter(
                param_name,
                inspect.Parameter.KEYWORD_ONLY,
                default=None,
                annotation=Optional[lazy_class]  # Use actual type object, not string
            )
            new_params.insert(insert_index, new_param)
            insert_index += 1

        # Create enhanced wrapper function
        @wraps(func)
        def enhanced_wrapper(*args, **kwargs):
            # Extract dataclass parameters from kwargs (they're just ignored for now)
            regular_kwargs = {k: v for k, v in kwargs.items()
                            if k not in [name for name, _, _ in dataclass_params]}

            # Call original function with regular parameters only
            return func(*args, **regular_kwargs)

        # Apply the modified signature
        new_sig = original_sig.replace(parameters=new_params)
        enhanced_wrapper.__signature__ = new_sig

        # Enhance annotations
        if hasattr(func, '__annotations__'):
            enhanced_wrapper.__annotations__ = func.__annotations__.copy()
        else:
            enhanced_wrapper.__annotations__ = {}

        # Add type annotations for injected parameters
        from typing import Optional
        for param_name, type_hint, lazy_class in params_to_add:
            enhanced_wrapper.__annotations__[param_name] = Optional[lazy_class]

        return enhanced_wrapper

    def _get_function_by_name(self, module_path: str, func_name: str):
        """Get function object by module path and name."""
        module = importlib.import_module(module_path)
        return getattr(module, func_name)

    # ===== PROCESSING CONTRACT EXECUTION METHODS =====
    def _execute_slice_by_slice(self, func, image, *args, **kwargs):
        """Shared slice-by-slice execution logic."""
        if image.ndim == 3:
            from openhcs.core.memory.stack_utils import unstack_slices, stack_slices, _detect_memory_type
            mem = _detect_memory_type(image)
            slices = unstack_slices(image, mem, 0)
            results = [func(sl, *args, **kwargs) for sl in slices]
            return stack_slices(results, mem, 0)
        return func(image, *args, **kwargs)

    def _execute_pure_3d(self, func, image, *args, **kwargs):
        """Execute 3D→3D function directly (no change)."""
        return func(image, *args, **kwargs)

    def _execute_pure_2d(self, func, image, *args, **kwargs):
        """Execute 2D→2D function with unstack/restack wrapper."""
        # Get memory type from the decorated function
        memory_type = func.output_memory_type
        slices = unstack_slices(image, memory_type, 0)
        results = [func(sl, *args, **kwargs) for sl in slices]
        return stack_slices(results, memory_type, 0)

    def _execute_flexible(self, func, image, *args, **kwargs):
        """Execute function that handles both 3D→3D and 2D→2D with toggle."""
        # Check if slice_by_slice attribute is set on the function
        slice_by_slice = getattr(func, 'slice_by_slice', False)
        if slice_by_slice:
            # Reuse the 2D-only execution logic (unstack -> process -> restack)
            return self._execute_pure_2d(func, image, *args, **kwargs)
        else:
            # Use 3D-only execution logic (no modification)
            return self._execute_pure_3d(func, image, *args, **kwargs)

    def _execute_volumetric_to_slice(self, func, image, *args, **kwargs):
        """Execute 3D→2D function returning slice 3D array."""
        # Get memory type from the decorated function
        memory_type = func.output_memory_type
        result_2d = func(image, *args, **kwargs)
        return stack_slices([result_2d], memory_type, 0)

    # ===== CACHING METHODS =====
    def _load_or_discover_functions(self) -> Dict[str, FunctionMetadata]:
        """Load functions from cache or discover them if cache is invalid."""
        logger.info(f"🔄 _load_or_discover_functions called for {self.library_name}")

        cached_functions = self._load_from_cache()
        if cached_functions is not None:
            logger.info(f"✅ Loaded {len(cached_functions)} {self.library_name} functions from cache")
            return cached_functions

        logger.info(f"🔍 Cache miss for {self.library_name} - performing full discovery")
        functions = self.discover_functions()
        self._save_to_cache(functions)
        return functions

    def _load_from_cache(self) -> Optional[Dict[str, FunctionMetadata]]:
        """Load function metadata from cache with validation."""
        logger.debug(f"📂 LOAD FROM CACHE: Checking cache for {self.library_name}")

        if not self._cache_path.exists():
            logger.debug(f"📂 LOAD FROM CACHE: No cache file exists at {self._cache_path}")
            return None

        try:
            with open(self._cache_path, 'r') as f:
                cache_data = json.load(f)
        except json.JSONDecodeError:
            logger.warning(f"Corrupt cache file {self._cache_path}, rebuilding")
            self._cache_path.unlink(missing_ok=True)
            return None

        if 'functions' not in cache_data:
            return None

        cached_version = cache_data.get('library_version', 'unknown')
        current_version = self.get_library_version()
        if cached_version != current_version:
            logger.info(f"{self.library_name} version changed ({cached_version} → {current_version}) - cache invalid")
            return None

        cache_timestamp = cache_data.get('timestamp', 0)
        cache_age_days = (time.time() - cache_timestamp) / (24 * 3600)
        if cache_age_days > 7:
            logger.debug(f"Cache is {cache_age_days:.1f} days old - rebuilding")
            return None

        logger.debug(f"📂 LOAD FROM CACHE: Loading {len(cache_data['functions'])} functions for {self.library_name}")

        functions = {}
        for func_name, cached_data in cache_data['functions'].items():
            original_name = cached_data.get('original_name', func_name)
            func = self._get_function_by_name(cached_data['module'], original_name)
            contract = ProcessingContract[cached_data['contract']]

            # Apply the same wrappers as during discovery
            has_adapter = hasattr(self, 'create_library_adapter')
            logger.debug(f"📂 LOAD FROM CACHE: {func_name} - hasattr(create_library_adapter)={has_adapter}")

            if has_adapter:
                # External library - apply library adapter + contract wrapper + param injection
                adapted_func = self.create_library_adapter(func, contract)
                contract_wrapped_func = self.apply_contract_wrapper(adapted_func, contract)
                final_func = self._inject_optional_dataclass_params(contract_wrapped_func)
            else:
                # OpenHCS - apply contract wrapper + param injection
                contract_wrapped_func = self.apply_contract_wrapper(func, contract)
                final_func = self._inject_optional_dataclass_params(contract_wrapped_func)

            metadata = FunctionMetadata(
                name=func_name,
                func=final_func,
                contract=contract,
                registry=self,
                module=cached_data.get('module', ''),
                doc=cached_data.get('doc', ''),
                tags=cached_data.get('tags', []),
                original_name=cached_data.get('original_name', func_name)
            )
            functions[func_name] = metadata

        return functions

    def _save_to_cache(self, functions: Dict[str, FunctionMetadata]) -> None:
        """Save function metadata to cache."""
        cache_data = {
            'cache_version': '1.0',
            'library_version': self.get_library_version(),
            'timestamp': time.time(),
            'functions': {
                func_name: {
                    'name': metadata.name,
                    'original_name': metadata.original_name,
                    'module': metadata.module,
                    'contract': metadata.contract.name,
                    'doc': metadata.doc,
                    'tags': metadata.tags
                }
                for func_name, metadata in functions.items()
            }
        }

        self._cache_path.parent.mkdir(parents=True, exist_ok=True)
        with open(self._cache_path, 'w') as f:
            json.dump(cache_data, f, indent=2)

        logger.info(f"💾 Saved {len(functions)} {self.library_name} functions to cache")

    def get_memory_type(self) -> str:
        """Get the memory type string value for this library."""
        return self.MEMORY_TYPE

    def get_module_patterns(self) -> List[str]:
        """Get module patterns that identify this library (can be overridden by implementations)."""
        # Default: just the library name
        return [self.library_name.lower()]

    def get_display_name(self) -> str:
        """Get display name for this library (can be overridden by implementations)."""
        # Default: capitalize library name
        return self.library_name.title()

    # ===== FUNCTION DISCOVERY =====
    def get_modules_to_scan(self) -> List[Tuple[str, Any]]:
        """
        Get list of (module_name, module_object) tuples to scan for functions.
        Uses the MODULES_TO_SCAN class attribute and library object from get_library_object().

        Returns:
            List of (name, module) pairs where name is for identification
            and module is the actual module object to scan.
        """
        library = self.get_library_object()
        modules = []
        for module_name in self.MODULES_TO_SCAN:
            if module_name == "":
                # Empty string means scan the main library namespace
                module = library
                modules.append(("main", module))
            else:
                module = getattr(library, module_name)
                modules.append((module_name, module))
        return modules

    @abstractmethod
    def get_library_object(self):
        """Get the main library object to scan for modules. Library-specific implementation."""
        pass


class RuntimeTestingRegistryBase(LibraryRegistryBase):
    """
    Extended ABC for libraries that require runtime testing.

    Adds runtime testing methods for libraries that don't have explicit
    processing contracts and need behavioral classification through testing.
    """

    def create_test_arrays(self) -> Tuple[Any, Any]:
        """
        Create test arrays appropriate for this library.

        Returns:
            Tuple of (test_3d, test_2d) arrays for behavior testing
        """
        test_3d = self._create_array((3, 20, 20), self._get_float_dtype())
        test_2d = self._create_array((20, 20), self._get_float_dtype())
        return test_3d, test_2d

    @abstractmethod
    def _create_array(self, shape: Tuple[int, ...], dtype):
        """Create array with specified shape and dtype. Library-specific implementation."""
        pass

    def _get_float_dtype(self):
        """Get the appropriate float dtype for this library."""
        return self.FLOAT_DTYPE

    # ===== CORE BEHAVIOR CONTRACT =====
    def classify_function_behavior(self, func: Callable, declared_contract: Optional[ProcessingContract] = None) -> Tuple[ProcessingContract, bool]:
        """Classify function behavior by testing 3D and 2D inputs, or use declared contract if provided."""

        # Fast path: If explicit contract is declared, use it directly (skip runtime testing)
        if declared_contract is not None:
            return declared_contract, True
        test_3d, test_2d = self.create_test_arrays()

        def test_function(test_array):
            """Test function with array, return (success, result)."""
            try:
                result = func(test_array)
                return True, result
            except:
                return False, None

        works_3d, result_3d = test_function(test_3d)
        works_2d, _ = test_function(test_2d)

        # Classification lookup table
        classification_map = {
            (True, True): self._classify_dual_support(result_3d),
            (True, False): ProcessingContract.PURE_3D,
            (False, True): ProcessingContract.PURE_2D,
            (False, False): None  # Invalid function
        }

        contract = classification_map[(works_3d, works_2d)]
        is_valid = works_3d or works_2d

        return contract, is_valid

    def _classify_dual_support(self, result_3d):
        """Classify functions that work on both 3D and 2D inputs."""
        if result_3d is not None:
            # Handle tuple results (some functions return multiple arrays)
            if isinstance(result_3d, tuple):
                # Check the first element if it's a tuple
                first_result = result_3d[0] if len(result_3d) > 0 else None
                if hasattr(first_result, 'ndim') and first_result.ndim == 2:
                    return ProcessingContract.VOLUMETRIC_TO_SLICE
            # Handle single array results
            elif hasattr(result_3d, 'ndim') and result_3d.ndim == 2:
                return ProcessingContract.VOLUMETRIC_TO_SLICE
        return ProcessingContract.FLEXIBLE

    @abstractmethod
    def _stack_2d_results(self, func, test_3d):
        """Stack 2D results. Library-specific implementation required."""
        pass

    @abstractmethod
    def _arrays_close(self, arr1, arr2):
        """Compare arrays. Library-specific implementation required."""
        pass

    def create_library_adapter(self, original_func: Callable, contract: ProcessingContract) -> Callable:
        """Create adapter with library-specific processing only."""
        import inspect
        func_name = getattr(original_func, '__name__', 'unknown')

        logger.debug(f"🔧 CREATE LIBRARY ADAPTER: {func_name} from {getattr(original_func, '__module__', 'unknown')}")

        # Get original signature to preserve it
        original_sig = inspect.signature(original_func)

        def adapter(image, *args, **kwargs):
            processed_image = self._preprocess_input(image, func_name)
            result = contract.execute(self, original_func, processed_image, *args, **kwargs)
            return self._postprocess_output(result, image, func_name)

        # Apply wraps and preserve signature
        wrapped_adapter = wraps(original_func)(adapter)
        wrapped_adapter.__signature__ = original_sig

        # Preserve and enhance annotations
        if hasattr(original_func, '__annotations__'):
            wrapped_adapter.__annotations__ = original_func.__annotations__.copy()
        else:
            wrapped_adapter.__annotations__ = {}

        # Extract type hints from docstring if annotations are missing
        self._enhance_annotations_from_docstring(wrapped_adapter, original_func)

        # Set memory type attributes for contract execution compatibility
        # Only set if registry has a specific memory type (external libraries)
        if self.MEMORY_TYPE is not None:
            wrapped_adapter.input_memory_type = self.MEMORY_TYPE
            wrapped_adapter.output_memory_type = self.MEMORY_TYPE
        wrapped_adapter.stream_to_napari = False

        return wrapped_adapter

    def _enhance_annotations_from_docstring(self, wrapped_func: Callable, original_func: Callable):
        """Extract type hints from docstring using mathematical simplification approach."""
        try:
            # Import from shared UI utilities (no circular dependency)
            from openhcs.introspection.signature_analyzer import SignatureAnalyzer
            import numpy as np

            logger.debug(f"🔍 ENHANCE ANNOTATIONS: {original_func.__name__} from {original_func.__module__}")

            # Unified type extraction with compatibility validation (mathematical simplification)
            TYPE_PATTERNS = {'ndarray': np.ndarray, 'array': np.ndarray, 'array_like': np.ndarray,
                           'int': int, 'integer': int, 'float': float, 'scalar': float,
                           'bool': bool, 'boolean': bool, 'str': str, 'string': str,
                           'tuple': tuple, 'list': list, 'dict': dict, 'sequence': list}

            COMPATIBLE_DEFAULTS = {float: (int, float, range), int: (int, float),
                                 list: (list, tuple, range), tuple: (list, tuple, range)}

            param_info = SignatureAnalyzer.analyze(original_func, skip_first_param=False)

            # Inline type extraction and validation (single-use function inlining rule)
            enhanced_count = 0
            for param_name, info in param_info.items():
                if param_name not in wrapped_func.__annotations__ and info.description:
                    # Extract first line of description (NumPy/SciPy convention: type is always on first line)
                    # This avoids false matches from type keywords appearing later in the description
                    first_line = info.description.split('\n')[0].strip().lower()
                    # Remove optional markers and split on 'or' for union types
                    first_line = first_line.replace(', optional', '').replace(' optional', '').split(' or ')[0].strip()

                    # Type extraction with priority patterns
                    python_type = (str if first_line.startswith('{') and '}' in first_line
                                 else list if any(p in first_line for p in ['sequence', 'iterable', 'array of', 'list of'])
                                 else next((t for pattern, t in TYPE_PATTERNS.items() if pattern in first_line), None))

                    # Inline compatibility check (single-use function inlining rule)
                    if python_type and (info.default_value is None or
                                      type(info.default_value) in COMPATIBLE_DEFAULTS.get(python_type, (python_type,))):
                        logger.debug(f"  ✓ Enhanced {param_name}: {python_type} (from first_line='{first_line[:50]}')")
                        wrapped_func.__annotations__[param_name] = python_type
                        enhanced_count += 1
                    elif info.description:
                        logger.debug(f"  ✗ Could not enhance {param_name}: first_line='{first_line[:50]}', extracted_type={python_type}")

            if enhanced_count > 0:
                logger.debug(f"  📝 Enhanced {enhanced_count} annotations for {original_func.__name__}")
                logger.debug(f"  Final annotations: {wrapped_func.__annotations__}")
        except Exception as e:
            logger.error(f"  ❌ Error enhancing annotations for {original_func.__name__}: {e}", exc_info=True)

    @abstractmethod
    def _preprocess_input(self, image, func_name: str):
        """Preprocess input image. Library-specific implementation."""
        pass

    @abstractmethod
    def _postprocess_output(self, result, original_image, func_name: str):
        """Postprocess output result. Library-specific implementation."""
        pass

    # ===== BASIC FILTERING =====
    def should_include_function(self, func: Callable, func_name: str) -> bool:
        """Single method for all filtering logic (blacklist, signature, etc.)"""
        # Skip private functions
        if func_name.startswith('_'):
            return False

        # Skip exclusions (check both common and library-specific)
        exclusions = getattr(self.__class__, 'EXCLUSIONS', self.COMMON_EXCLUSIONS)
        if func_name.lower() in exclusions:
            return False

        # Skip classes and types
        if inspect.isclass(func) or isinstance(func, type):
            return False

        # Must be callable
        if not callable(func):
            return False

        # Pure functions must have at least one parameter
        sig = inspect.signature(func)
        params = list(sig.parameters.values())
        if not params:
            return False

        # Validate that type hints can be resolved (skip functions with missing dependencies)
        if not self._validate_type_hints(func, func_name):
            return False

        # Library-specific signature validation
        return self._check_first_parameter(params[0], func_name)


    def _validate_type_hints(self, func: Callable, func_name: str) -> bool:
        """
        Validate that function type hints can be resolved.

        Returns False if type hints reference missing dependencies (e.g., torch when not installed).
        This prevents functions with unresolvable type hints from being registered.
        """
        try:
            from typing import get_type_hints
            # Try to resolve type hints - this will fail if dependencies are missing
            get_type_hints(func)
            return True
        except NameError as e:
            # Type hint references a missing dependency (e.g., 'torch' not defined)
            logger.warning(f"Skipping function '{func_name}' due to unresolvable type hints: {e}")
            return False
        except Exception:
            # Other type hint resolution errors - be conservative and allow the function
            # (this handles edge cases where get_type_hints fails for other reasons)
            return True

    @abstractmethod
    def _check_first_parameter(self, first_param, func_name: str) -> bool:
        """Check if first parameter meets library-specific criteria. Library-specific implementation."""
        pass

    # ===== RUNTIME TESTING IMPLEMENTATION =====
    def discover_functions(self) -> Dict[str, FunctionMetadata]:
        """Discover and classify all library functions with runtime testing."""
        functions = {}
        modules = self.get_modules_to_scan()
        logger.info(f"🔍 Starting function discovery for {self.library_name}")
        logger.info(f"📦 Scanning {len(modules)} modules: {[name for name, _ in modules]}")

        total_tested = 0
        total_accepted = 0

        for module_name, module in modules:
            logger.info(f"  📦 Analyzing {module_name} ({module})...")
            module_tested = 0
            module_accepted = 0

            for name in dir(module):
                if name.startswith("_"):
                    continue

                func = getattr(module, name)
                full_path = self._get_full_function_path(module, name, module_name)

                if not self.should_include_function(func, name):
                    rejection_reason = self._get_rejection_reason(func, name)
                    if rejection_reason != "private":
                        logger.debug(f"    🚫 Skipping {full_path}: {rejection_reason}")
                    continue

                module_tested += 1
                total_tested += 1

                contract, is_valid = self.classify_function_behavior(func)
                logger.debug(f"    🧪 Testing {full_path}")
                logger.debug(f"       Classification: {contract.name if contract else contract}")

                if not is_valid:
                    logger.debug("       ❌ Rejected: Invalid classification")
                    continue

                doc_lines = (func.__doc__ or "").splitlines()
                first_line_doc = doc_lines[0] if doc_lines else ""
                func_name = self._generate_function_name(name, module_name)

                # Apply library adapter (preprocessing/postprocessing)
                adapted_func = self.create_library_adapter(func, contract)

                # Apply contract wrapper (slice_by_slice for FLEXIBLE)
                contract_wrapped_func = self.apply_contract_wrapper(adapted_func, contract)

                # Inject optional dataclass parameters
                final_func = self._inject_optional_dataclass_params(contract_wrapped_func)

                metadata = FunctionMetadata(
                    name=func_name,
                    func=final_func,
                    contract=contract,
                    registry=self,
                    module=func.__module__ or "",
                    doc=first_line_doc,
                    tags=self._generate_tags(name),
                    original_name=name
                )

                functions[func_name] = metadata
                module_accepted += 1
                total_accepted += 1
                logger.debug(f"       ✅ Accepted as '{func_name}'")

            logger.debug(f"  📊 Module {module_name}: {module_accepted}/{module_tested} functions accepted")

        logger.info(f"✅ Discovery complete: {total_accepted}/{total_tested} functions accepted")
        return functions



    def _get_full_function_path(self, module, func_name: str, module_name: str) -> str:
        """Generate full module path for logging."""
        if module_name == "main":
            return f"{self.library_name}.{func_name}"
        else:
            # Extract clean module path
            module_str = str(module)
            if "'" in module_str:
                clean_path = module_str.split("'")[1]
                return f"{clean_path}.{func_name}"
            else:
                return f"{module_name}.{func_name}"

    def _get_rejection_reason(self, func: Callable, func_name: str) -> str:
        """Get detailed reason why a function was rejected."""
        # Check each rejection criteria in order
        if func_name.startswith('_'):
            return "private"

        exclusions = getattr(self.__class__, 'EXCLUSIONS', self.COMMON_EXCLUSIONS)
        if func_name.lower() in exclusions:
            return "blacklisted"

        if inspect.isclass(func) or isinstance(func, type):
            return "is class/type"

        if not callable(func):
            return "not callable"

        try:
            sig = inspect.signature(func)
            params = list(sig.parameters.values())
            if not params:
                return "no parameters (not pure function)"
        except (ValueError, TypeError):
            return "invalid signature"

        return "unknown"



    # ===== CUSTOMIZATION HOOKS =====
    def _generate_function_name(self, name: str, module_name: str) -> str:
        """Generate function name. Override in subclasses for custom naming."""
        return name

    def _generate_tags(self, func_name: str) -> List[str]:
        """Generate tags using library name."""
        return [self.library_name]
