"""Code generation provider protocol for app-specific code emitters."""

from typing import Protocol, Any, Optional


class CodegenProvider(Protocol):
    """Protocol for code generators used by the simple code editor."""

    def generate_complete_orchestrator_code(
        self,
        plate_paths: list[str],
        pipeline_data: dict,
        global_config: Optional[Any] = None,
        per_plate_configs: Optional[dict] = None,
        pipeline_config: Optional[Any] = None,
        clean_mode: bool = True,
    ) -> str:
        ...

    def generate_complete_pipeline_steps_code(
        self,
        pipeline_steps: list[Any],
        clean_mode: bool = True,
    ) -> str:
        ...

    def generate_complete_function_pattern_code(
        self,
        func_obj: Any,
        clean_mode: bool = False,
    ) -> str:
        ...

    def generate_config_code(
        self,
        config_obj: Any,
        clean_mode: bool = True,
        config_class: Optional[type] = None,
    ) -> str:
        ...

    def generate_step_code(self, step_obj: Any, clean_mode: bool = True) -> str:
        ...


_codegen_provider: Optional[CodegenProvider] = None


def register_codegen_provider(provider: CodegenProvider) -> None:
    """Register a global code generation provider."""
    global _codegen_provider
    _codegen_provider = provider


def get_codegen_provider() -> Optional[CodegenProvider]:
    """Get the registered code generation provider."""
    return _codegen_provider
