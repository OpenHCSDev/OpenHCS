"""Code generation compatibility layer.

Delegates code generation to the registered CodegenProvider.
"""

from typing import Any, Optional

from pyqt_formgen.protocols import get_codegen_provider


def _require_provider():
    provider = get_codegen_provider()
    if provider is None:
        raise RuntimeError("No codegen provider registered. Call register_codegen_provider(...).")
    return provider


def generate_complete_orchestrator_code(
    plate_paths: list[str],
    pipeline_data: dict,
    global_config: Optional[Any] = None,
    per_plate_configs: Optional[dict] = None,
    pipeline_config: Optional[Any] = None,
    clean_mode: bool = True,
) -> str:
    provider = _require_provider()
    return provider.generate_complete_orchestrator_code(
        plate_paths=plate_paths,
        pipeline_data=pipeline_data,
        global_config=global_config,
        per_plate_configs=per_plate_configs,
        pipeline_config=pipeline_config,
        clean_mode=clean_mode,
    )


def generate_complete_pipeline_steps_code(
    pipeline_steps: list[Any],
    clean_mode: bool = True,
) -> str:
    provider = _require_provider()
    return provider.generate_complete_pipeline_steps_code(
        pipeline_steps=pipeline_steps,
        clean_mode=clean_mode,
    )


def generate_complete_function_pattern_code(
    func_obj: Any,
    indent: int = 0,
    clean_mode: bool = False,
) -> str:
    provider = _require_provider()
    return provider.generate_complete_function_pattern_code(
        func_obj=func_obj,
        clean_mode=clean_mode,
    )


def generate_step_code(step_obj: Any, clean_mode: bool = True) -> str:
    provider = _require_provider()
    return provider.generate_step_code(step_obj=step_obj, clean_mode=clean_mode)


def generate_config_code(
    config_obj: Any,
    config_class: Optional[type] = None,
    clean_mode: bool = True,
) -> str:
    provider = _require_provider()
    return provider.generate_config_code(
        config_obj=config_obj,
        clean_mode=clean_mode,
        config_class=config_class,
    )
