"""
Custom function manager for lifecycle operations.

Manages registration, persistence, loading, and deletion of custom functions.
All custom functions are stored in ~/.local/share/openhcs/custom_functions/
and automatically loaded on startup.

Architecture:
    - Uses exec() to execute user code in controlled namespace
    - Validates functions before and after execution
    - Registers valid functions via func_registry.register_function()
    - Persists to disk as .py files
    - Emits Qt signals for UI updates
"""

import logging
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, List

from openhcs.core.xdg_paths import get_data_file_path
from openhcs.processing.func_registry import register_function
from openhcs.processing.custom_functions.validation import (
    ValidationError,
    ValidationResult,
    validate_code,
    validate_function,
)
from openhcs.processing.custom_functions.signals import custom_function_signals

logger = logging.getLogger(__name__)


@dataclass(frozen=True)
class CustomFunctionInfo:
    """
    Metadata for a registered custom function.

    Attributes:
        name: Function name
        file_path: Path to source .py file
        memory_type: Memory type (numpy, cupy, etc.)
        doc: Function docstring
    """

    name: str
    file_path: Path
    memory_type: str
    doc: str


class CustomFunctionManager:
    """
    Manager for custom function lifecycle operations.

    Handles registration, persistence, loading, and deletion of user-defined
    custom functions. All operations emit signals to notify UI components.

    Attributes:
        storage_dir: Directory where custom functions are stored
    """

    def __init__(self):
        """Initialize manager and create storage directory if needed."""
        self.storage_dir: Path = get_data_file_path("custom_functions")
        if not self.storage_dir.exists():
            self.storage_dir.mkdir(parents=True, exist_ok=True)
            logger.info(f"Created custom functions directory: {self.storage_dir}")

    def register_from_code(
        self,
        code: str,
        persist: bool = True
    ) -> List[Callable]:
        """
        Execute code and register all decorated functions found.

        Validates code before execution, executes in controlled namespace,
        extracts decorated functions, validates them, and registers via
        func_registry.register_function().

        Args:
            code: Python code containing function definitions with decorators
            persist: If True, save code to storage directory

        Returns:
            List of successfully registered functions

        Raises:
            ValidationError: If code validation fails
            ValueError: If no valid functions found
            RuntimeError: If function registration fails
        """
        # Validate code before execution
        validation_result: ValidationResult = validate_code(code)
        if not validation_result.is_valid:
            error_messages = "\n".join(validation_result.errors)
            raise ValidationError(f"Code validation failed:\n{error_messages}")

        # Create controlled namespace with memory decorators
        namespace: Dict[str, Any] = self._create_execution_namespace()

        # Execute code
        try:
            exec(code, namespace)
        except Exception as e:
            raise ValidationError(f"Code execution failed: {str(e)}")

        # Extract decorated functions
        registered_functions: List[Callable] = []
        for name, obj in namespace.items():
            # Skip special names and imports
            if name.startswith('_') or not callable(obj):
                continue

            # Check if this is a function with memory type attributes
            if not hasattr(obj, 'input_memory_type'):
                continue

            # Validate function
            func_validation: ValidationResult = validate_function(obj)
            if not func_validation.is_valid:
                error_messages = "\n".join(func_validation.errors)
                raise ValidationError(
                    f"Function '{name}' validation failed:\n{error_messages}"
                )

            # Register function
            try:
                register_function(obj, backend='openhcs')
                registered_functions.append(obj)
                logger.info(
                    f"Registered custom function: {name} "
                    f"({obj.input_memory_type} -> {obj.output_memory_type})"
                )
            except ValueError as e:
                raise RuntimeError(f"Failed to register function '{name}': {str(e)}")

        # Ensure at least one function was registered
        if not registered_functions:
            raise ValueError(
                "No valid functions found in code. "
                "Functions must be decorated with @numpy, @cupy, etc."
            )

        # Persist to disk if requested
        if persist:
            for func in registered_functions:
                self._save_function_code(func.name, code)

        # Clear metadata caches to force refresh
        self._clear_caches()

        # Emit signal for UI updates
        custom_function_signals.functions_changed.emit()

        return registered_functions

    def load_all_custom_functions(self) -> int:
        """
        Load all .py files from storage directory.

        Scans storage directory for .py files and registers all valid functions.
        Errors are logged but don't stop processing of other files.

        Returns:
            Number of functions successfully loaded
        """
        if not self.storage_dir.exists():
            return 0

        loaded_count: int = 0

        for py_file in self.storage_dir.glob("*.py"):
            try:
                code: str = py_file.read_text(encoding='utf-8')
                functions: List[Callable] = self.register_from_code(
                    code,
                    persist=False  # Already persisted
                )
                loaded_count += len(functions)
                logger.info(
                    f"Loaded {len(functions)} custom function(s) from {py_file.name}"
                )
            except Exception as e:
                logger.error(f"Failed to load custom functions from {py_file.name}: {e}")
                continue

        if loaded_count > 0:
            # Clear caches after bulk load
            self._clear_caches()
            custom_function_signals.functions_changed.emit()

        return loaded_count

    def delete_custom_function(self, func_name: str) -> bool:
        """
        Remove function from registry and delete source file.

        Note: This removes the file but does not unregister the function from
        FUNC_REGISTRY (requires application restart for full removal).

        Args:
            func_name: Name of function to delete

        Returns:
            True if function file was deleted, False if not found
        """
        file_path: Path = self.storage_dir / f"{func_name}.py"

        if not file_path.exists():
            logger.warning(f"Custom function file not found: {file_path}")
            return False

        # Delete file
        file_path.unlink()
        logger.info(f"Deleted custom function file: {file_path}")

        # Clear caches
        self._clear_caches()

        # Emit signal
        custom_function_signals.functions_changed.emit()

        return True

    def list_custom_functions(self) -> List[CustomFunctionInfo]:
        """
        Return metadata for all custom functions in storage.

        Returns:
            List of CustomFunctionInfo objects
        """
        if not self.storage_dir.exists():
            return []

        functions: List[CustomFunctionInfo] = []

        for py_file in self.storage_dir.glob("*.py"):
            try:
                # Read file to extract metadata
                code: str = py_file.read_text(encoding='utf-8')

                # Create temporary namespace to extract function
                namespace: Dict[str, Any] = self._create_execution_namespace()
                exec(code, namespace)

                # Find first decorated function
                for name, obj in namespace.items():
                    if (
                        not name.startswith('_')
                        and callable(obj)
                        and hasattr(obj, 'input_memory_type')
                    ):
                        info = CustomFunctionInfo(
                            name=name,
                            file_path=py_file,
                            memory_type=obj.input_memory_type,
                            doc=obj.__doc__ or ""
                        )
                        functions.append(info)
                        break

            except Exception as e:
                logger.error(f"Failed to read metadata from {py_file.name}: {e}")
                continue

        return functions

    def _create_execution_namespace(self) -> Dict[str, Any]:
        """
        Create controlled namespace for exec().

        Includes all memory type decorators and common imports.
        Does not restrict builtins (custom functions need full Python).

        Returns:
            Namespace dict for exec()
        """
        from openhcs.core.memory import decorators

        # Import all memory type decorators
        namespace: Dict[str, Any] = {
            'numpy': decorators.numpy,
            'cupy': decorators.cupy,
            'torch': decorators.torch,
            'tensorflow': decorators.tensorflow,
            'jax': decorators.jax,
            'pyclesperanto': decorators.pyclesperanto,
        }

        return namespace

    def _save_function_code(self, func_name: str, code: str) -> None:
        """
        Save function code to storage directory.

        Args:
            func_name: Name of function (used as filename)
            code: Python source code
        """
        file_path: Path = self.storage_dir / f"{func_name}.py"
        file_path.write_text(code, encoding='utf-8')
        logger.info(f"Saved custom function to: {file_path}")

    def _clear_caches(self) -> None:
        """
        Clear function registry metadata caches.

        Required after registration to ensure UI sees new functions.
        """
        from openhcs.processing.backends.lib_registry.registry_service import RegistryService

        RegistryService.clear_metadata_cache()
        logger.debug("Cleared RegistryService metadata cache")

        # Also clear FunctionSelectorDialog cache if it exists
        try:
            from openhcs.pyqt_gui.dialogs.function_selector_dialog import FunctionSelectorDialog
            FunctionSelectorDialog.clear_metadata_cache()
            logger.debug("Cleared FunctionSelectorDialog metadata cache")
        except ImportError:
            # UI might not be imported yet (e.g., during startup)
            pass
