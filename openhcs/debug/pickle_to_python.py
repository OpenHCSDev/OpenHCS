#!/usr/bin/env python3
"""
Pickle to Python Converter - Convert OpenHCS debug pickle files to runnable Python scripts
"""

import sys
import dill as pickle
import inspect
from pathlib import Path
from datetime import datetime
from collections import defaultdict
from enum import Enum
from dataclasses import is_dataclass, fields

from openhcs.core.config import GlobalPipelineConfig, PathPlanningConfig, VFSConfig, ZarrConfig
from openhcs.core.steps.function_step import FunctionStep

def collect_imports_from_data(data_obj):
    """Extract function, enum, and dataclass imports by traversing data structure."""
    function_imports = defaultdict(set)
    enum_imports = defaultdict(set)

    # Import mappings for dynamically generated classes
    LAZY_MAPPINGS = {
        'LazyStepMaterializationConfig': 'openhcs.core.pipeline_config',
        'PipelineConfig': 'openhcs.core.pipeline_config',
    }

    def register_imports(obj):
        if isinstance(obj, Enum):
            enum_imports[obj.__class__.__module__].add(obj.__class__.__name__)
        elif is_dataclass(obj):
            name = obj.__class__.__name__
            module = LAZY_MAPPINGS.get(name, obj.__class__.__module__)
            function_imports[module].add(name)
            [register_imports(getattr(obj, f.name)) for f in fields(obj) if getattr(obj, f.name) is not None]
        elif callable(obj):
            function_imports[obj.__module__].add(obj.__name__)
        elif isinstance(obj, (list, tuple)):
            [register_imports(item) for item in obj]
        elif isinstance(obj, dict):
            [register_imports(value) for value in obj.values()]
        elif hasattr(obj, '__dict__') and obj.__dict__:
            [register_imports(value) for value in obj.__dict__.values()]

    register_imports(data_obj)
    return function_imports, enum_imports

def format_imports_as_strings(function_imports, enum_imports):
    """Convert import dictionaries to list of import strings with collision resolution."""
    # Merge imports
    all_imports = function_imports.copy()
    for module, names in enum_imports.items():
        all_imports.setdefault(module, set()).update(names)

    # Build collision map
    name_to_modules = defaultdict(list)
    for module, names in all_imports.items():
        for name in names:
            name_to_modules[name].append(module)

    import_lines, name_mappings = [], {}
    for module, names in sorted(all_imports.items()):
        if not module or module == 'builtins' or not names:
            continue

        imports = []
        for name in sorted(names):
            if len(name_to_modules[name]) > 1:
                qualified = f"{name}_{module.split('.')[-1]}"
                imports.append(f"{name} as {qualified}")
                name_mappings[(name, module)] = qualified
            else:
                imports.append(name)
                name_mappings[(name, module)] = name

        import_lines.append(f"from {module} import {', '.join(imports)}")

    return import_lines, name_mappings

def generate_complete_function_pattern_code(func_obj, indent=0, clean_mode=False):
    """Generate complete Python code for function pattern with imports."""
    # Generate pattern representation
    pattern_repr = generate_readable_function_repr(func_obj, indent, clean_mode)

    # Collect imports from this pattern
    function_imports, enum_imports = collect_imports_from_data(func_obj)
    import_lines, name_mappings = format_imports_as_strings(function_imports, enum_imports)

    # Build complete code
    code_lines = ["# Edit this function pattern and save to apply changes", ""]
    if import_lines:
        code_lines.append("# Dynamic imports")
        code_lines.extend(import_lines)
        code_lines.append("")
    code_lines.append(f"pattern = {pattern_repr}")

    return "\n".join(code_lines)

def _value_to_repr(value):
    """Converts a value to its Python representation string."""
    if isinstance(value, Enum):
        return f"{value.__class__.__name__}.{value.name}"
    elif isinstance(value, str):
        # Use repr() for strings to properly escape newlines and special characters
        return repr(value)
    elif isinstance(value, Path):
        return f'Path({repr(str(value))})'
    return repr(value)

def generate_clean_dataclass_repr(instance, indent_level=0, clean_mode=False):
    """
    Generates a clean, readable Python representation of a dataclass instance,
    omitting fields that are set to their default values if clean_mode is True.
    This function is recursive and handles nested dataclasses.
    """
    if not dataclasses.is_dataclass(instance):
        return _value_to_repr(instance)

    lines = []
    indent_str = "    " * indent_level
    child_indent_str = "    " * (indent_level + 1)

    # Get a default instance of the same class for comparison
    default_instance = instance.__class__()

    for field in dataclasses.fields(instance):
        field_name = field.name
        current_value = getattr(instance, field_name)
        default_value = getattr(default_instance, field_name)

        if clean_mode and current_value == default_value:
            continue

        if dataclasses.is_dataclass(current_value):
            # Recursively generate representation for nested dataclasses
            nested_repr = generate_clean_dataclass_repr(current_value, indent_level + 1, clean_mode)
            lines.append(f"{child_indent_str}{field_name}={current_value.__class__.__name__}(\n{nested_repr}\n{child_indent_str})")
        else:
            value_repr = _value_to_repr(current_value)
            lines.append(f"{child_indent_str}{field_name}={value_repr}")

    if not lines:
        return "" # Return empty string if all fields were default in clean_mode

    return ",\n".join(lines)


def convert_pickle_to_python(pickle_path, output_path=None, clean_mode=False):
    """Convert an OpenHCS debug pickle file to a runnable Python script."""
    
    pickle_file = Path(pickle_path)
    if not pickle_file.exists():
        print(f"Error: Pickle file not found: {pickle_path}")
        return
    
    if output_path is None:
        output_path = pickle_file.with_suffix('.py')
    
    print(f"Converting {pickle_file} to {output_path} (Clean Mode: {clean_mode})")
    
    try:
        with open(pickle_file, 'rb') as f:
            data = pickle.load(f)
        
        # Generate Python script
        with open(output_path, 'w') as f:
            f.write('#!/usr/bin/env python3\n')
            f.write('"""\n')
            f.write(f'OpenHCS Pipeline Script - Generated from {pickle_file.name}\n')
            f.write(f'Generated: {datetime.now()}\n')
            f.write('"""\n\n')
            
            # Imports
            f.write('import sys\n')
            f.write('import os\n')
            f.write('from pathlib import Path\n\n')
            f.write('# Add OpenHCS to path\n')
            f.write('sys.path.insert(0, "/home/ts/code/projects/openhcs")\n\n')
            
            f.write('from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator\n')
            f.write('from openhcs.core.steps.function_step import FunctionStep\n')
            f.write('from openhcs.core.config import (GlobalPipelineConfig, PathPlanningConfig, VFSConfig, ZarrConfig, \n'
                    '                         MaterializationBackend, ZarrCompressor, ZarrChunkStrategy)\n')
            f.write('from openhcs.constants.constants import VariableComponents, Backend, Microscope\n\n')
            
            # Use extracted function for orchestrator generation
            orchestrator_code = generate_complete_orchestrator_code(
                data["plate_paths"], data["pipeline_data"], data['global_config'], clean_mode
            )

            # Write orchestrator code (already includes dynamic imports)
            f.write(orchestrator_code)
            f.write('\n\n')
            
            # ... (rest of the file remains the same for now) ...
            f.write('def setup_signal_handlers():\n')
            f.write('    """Setup signal handlers to kill all child processes and threads on Ctrl+C."""\n')
            f.write('    import signal\n')
            f.write('    import os\n')
            f.write('    import sys\n\n')
            f.write('    def cleanup_and_exit(signum, frame):\n')
            f.write('        print(f"\\n🔥 Signal {signum} received! Cleaning up all processes and threads...")\n\n')
            f.write('        os._exit(1)\n\n')
            f.write('    signal.signal(signal.SIGINT, cleanup_and_exit)\n')
            f.write('    signal.signal(signal.SIGTERM, cleanup_and_exit)\n\n')

            f.write('def run_pipeline():\n')
            f.write('    os.environ["OPENHCS_SUBPROCESS_MODE"] = "1"\n')
            f.write('    plate_paths, pipeline_data, global_config = create_pipeline()\n')
            f.write('    from openhcs.core.orchestrator.gpu_scheduler import setup_global_gpu_registry\n')
            f.write('    setup_global_gpu_registry(global_config=global_config)\n')
            f.write('    for plate_path in plate_paths:\n')
            f.write('        orchestrator = PipelineOrchestrator(plate_path, global_config=global_config)\n')
            f.write('        orchestrator.initialize()\n')
            f.write('        compiled_contexts = orchestrator.compile_pipelines(pipeline_data[plate_path])\n')
            f.write('        orchestrator.execute_compiled_plate(\n')
            f.write('            pipeline_definition=pipeline_data[plate_path],\n')
            f.write('            compiled_contexts=compiled_contexts,\n')
            f.write('            max_workers=global_config.num_workers\n')
            f.write('        )\n\n')

            f.write('if __name__ == "__main__":\n')
            f.write('    setup_signal_handlers()\n')
            f.write('    run_pipeline()\n')

        
        print(f"✅ Successfully converted to {output_path}")
        print(f"You can now run: python {output_path}")
        
    except Exception as e:
        print(f"Error converting pickle file: {e}")
        import traceback
        traceback.print_exc()


def generate_readable_function_repr(func_obj, indent=0, clean_mode=False, name_mappings=None):
    """Generate readable Python representation with collision-resolved function names."""
    indent_str = "    " * indent
    next_indent_str = "    " * (indent + 1)
    name_mappings = name_mappings or {}

    # Get qualified function name for collisions
    get_name = lambda f: name_mappings.get((f.__name__, f.__module__), f.__name__) if callable(f) else str(f)

    if callable(func_obj):
        return get_name(func_obj)
    
    elif isinstance(func_obj, tuple) and len(func_obj) == 2 and callable(func_obj[0]):
        func, args = func_obj

        if not args and clean_mode:
            return get_name(func)

        # Filter out defaults in clean mode
        try:
            defaults = {k: v.default for k, v in inspect.signature(func).parameters.items()
                       if v.default is not inspect.Parameter.empty}
        except (ValueError, TypeError):
            defaults = {}

        final_args = {k: v for k, v in args.items()
                     if not clean_mode or k not in defaults or v != defaults[k]}

        if not final_args:
            return get_name(func) if clean_mode else f"({get_name(func)}, {{}})"

        args_items = [f"{next_indent_str}    '{k}': {generate_readable_function_repr(v, indent + 2, clean_mode, name_mappings)}"
                     for k, v in final_args.items()]
        args_str = "{\n" + ",\n".join(args_items) + f"\n{next_indent_str}}}"
        return f"({get_name(func)}, {args_str})"

    elif isinstance(func_obj, list):
        if clean_mode and len(func_obj) == 1:
            return generate_readable_function_repr(func_obj[0], indent, clean_mode, name_mappings)
        if not func_obj:
            return "[]"
        items = [generate_readable_function_repr(item, indent, clean_mode, name_mappings) for item in func_obj]
        return f"[\n{next_indent_str}{f',\n{next_indent_str}'.join(items)}\n{indent_str}]"

    elif isinstance(func_obj, dict):
        if not func_obj:
            return "{}"
        items = [f"{next_indent_str}'{k}': {generate_readable_function_repr(v, indent, clean_mode, name_mappings)}"
                for k, v in func_obj.items()]
        return f"{{{',\n'.join(items)}\n{indent_str}}}"
        
    else:
        return _value_to_repr(func_obj)


def _format_parameter_value(param_name, value):
    """Format parameter values with lazy dataclass preservation."""
    if isinstance(value, Enum):
        return f"{value.__class__.__name__}.{value.name}"
    elif isinstance(value, str):
        return f'"{value}"'
    elif isinstance(value, list) and value and isinstance(value[0], Enum):
        return f"[{', '.join(f'{item.__class__.__name__}.{item.name}' for item in value)}]"
    elif is_dataclass(value) and 'Lazy' in value.__class__.__name__:
        # Preserve lazy behavior by only including explicitly set fields
        class_name = value.__class__.__name__
        explicit_args = [
            f"{f.name}={_format_parameter_value(f.name, object.__getattribute__(value, f.name))}"
            for f in fields(value)
            if object.__getattribute__(value, f.name) is not None
        ]
        return f"{class_name}({', '.join(explicit_args)})" if explicit_args else f"{class_name}()"
    else:
        return repr(value)





def _collect_dataclass_classes_from_object(obj, visited=None):
    """Recursively collect dataclass classes that will be referenced in generated code."""
    if visited is None:
        visited = set()

    if id(obj) in visited:
        return set(), set()
    visited.add(id(obj))

    dataclass_classes = set()
    enum_classes = set()

    if is_dataclass(obj):
        dataclass_classes.add(obj.__class__)
        for field in fields(obj):
            nested_dataclasses, nested_enums = _collect_dataclass_classes_from_object(getattr(obj, field.name), visited)
            dataclass_classes.update(nested_dataclasses)
            enum_classes.update(nested_enums)
    elif isinstance(obj, Enum):
        enum_classes.add(obj.__class__)
    elif isinstance(obj, (list, tuple)):
        for item in obj:
            nested_dataclasses, nested_enums = _collect_dataclass_classes_from_object(item, visited)
            dataclass_classes.update(nested_dataclasses)
            enum_classes.update(nested_enums)
    elif isinstance(obj, dict):
        for value in obj.values():
            nested_dataclasses, nested_enums = _collect_dataclass_classes_from_object(value, visited)
            dataclass_classes.update(nested_dataclasses)
            enum_classes.update(nested_enums)

    return dataclass_classes, enum_classes


def _generate_step_parameters(step, default_step, clean_mode=False, name_mappings=None):
    """Generate FunctionStep constructor parameters using functional introspection."""
    from openhcs.core.steps.abstract import AbstractStep

    signatures = [(name, param) for name, param in inspect.signature(FunctionStep.__init__).parameters.items()
                  if name != 'self' and param.kind != inspect.Parameter.VAR_KEYWORD] + \
                 [(name, param) for name, param in inspect.signature(AbstractStep.__init__).parameters.items()
                  if name != 'self']

    return [f"{name}={generate_readable_function_repr(getattr(step, name, param.default), 1, clean_mode, name_mappings) if name == 'func' else _format_parameter_value(name, getattr(step, name, param.default))}"
            for name, param in signatures
            if not clean_mode or getattr(step, name, param.default) != getattr(default_step, name, param.default)]


def generate_complete_pipeline_steps_code(pipeline_steps, clean_mode=False):
    """Generate complete Python code for pipeline steps with imports."""
    # Build code with imports and steps
    code_lines = ["# Edit this pipeline and save to apply changes", ""]

    # Collect imports from ALL data in pipeline steps (functions AND parameters)
    all_function_imports = defaultdict(set)
    all_enum_imports = defaultdict(set)

    for step in pipeline_steps:
        # Collect all imports from step (functions, enums, dataclasses)
        func_imports, enum_imports = collect_imports_from_data(step.func)
        param_imports, param_enums = collect_imports_from_data(step)

        # Merge imports
        for module, names in func_imports.items():
            all_function_imports[module].update(names)
        for module, names in enum_imports.items():
            all_enum_imports[module].update(names)
        for module, names in param_imports.items():
            all_function_imports[module].update(names)
        for module, names in param_enums.items():
            all_enum_imports[module].update(names)

    # Add FunctionStep import (always needed for generated code)
    all_function_imports['openhcs.core.steps.function_step'].add('FunctionStep')

    # Format and add all collected imports
    import_lines, name_mappings = format_imports_as_strings(all_function_imports, all_enum_imports)
    if import_lines:
        code_lines.append("# Automatically collected imports")
        code_lines.extend(import_lines)
        code_lines.append("")

    # Generate pipeline steps (extract exact logic from lines 164-198)
    code_lines.append("# Pipeline steps")
    code_lines.append("pipeline_steps = []")
    code_lines.append("")

    default_step = FunctionStep(func=lambda: None)
    for i, step in enumerate(pipeline_steps):
        code_lines.append(f"# Step {i+1}: {step.name}")

        # Generate all FunctionStep parameters automatically using introspection
        step_args = _generate_step_parameters(step, default_step, clean_mode, name_mappings)

        args_str = ",\n    ".join(step_args)
        code_lines.append(f"step_{i+1} = FunctionStep(\n    {args_str}\n)")
        code_lines.append(f"pipeline_steps.append(step_{i+1})")
        code_lines.append("")

    return "\n".join(code_lines)


def generate_complete_orchestrator_code(plate_paths, pipeline_data, global_config, clean_mode=False):
    """Generate complete Python code for orchestrator config with imports."""
    # Build complete code (extract exact logic from lines 150-200)
    code_lines = ["# Edit this orchestrator configuration and save to apply changes", ""]

    # Collect imports from ALL data in orchestrator (functions, parameters, config)
    all_function_imports = defaultdict(set)
    all_enum_imports = defaultdict(set)

    # Collect from pipeline steps
    for plate_path, steps in pipeline_data.items():
        for step in steps:
            # Get imports from function patterns
            func_imports, enum_imports = collect_imports_from_data(step.func)
            # Get imports from step parameters
            param_imports, param_enums = collect_imports_from_data(step)

            # Get enum classes referenced in generated code
            enum_classes = _collect_enum_classes_from_step(step)
            for enum_class in enum_classes:
                module = enum_class.__module__
                name = enum_class.__name__
                if module and name:
                    all_enum_imports[module].add(name)

            # Merge all imports
            for module, names in func_imports.items():
                all_function_imports[module].update(names)
            for module, names in enum_imports.items():
                all_enum_imports[module].update(names)
            for module, names in param_imports.items():
                all_function_imports[module].update(names)
            for module, names in param_enums.items():
                all_enum_imports[module].update(names)

    # Collect from global config
    config_imports, config_enums = collect_imports_from_data(global_config)
    for module, names in config_imports.items():
        all_function_imports[module].update(names)
    for module, names in config_enums.items():
        all_enum_imports[module].update(names)

    # Collect dataclass and enum classes referenced in generated code (PathPlanningConfig, VFSConfig, Backend, etc.)
    dataclass_classes, config_enum_classes = _collect_dataclass_classes_from_object(global_config)
    for dataclass_class in dataclass_classes:
        module = dataclass_class.__module__
        name = dataclass_class.__name__
        if module and name:
            all_function_imports[module].add(name)

    for enum_class in config_enum_classes:
        module = enum_class.__module__
        name = enum_class.__name__
        if module and name:
            all_enum_imports[module].add(name)

    # Add always-needed imports for generated code structure
    all_function_imports['openhcs.core.steps.function_step'].add('FunctionStep')

    # Format and add all collected imports
    import_lines, name_mappings = format_imports_as_strings(all_function_imports, all_enum_imports)
    if import_lines:
        code_lines.append("# Automatically collected imports")
        code_lines.extend(import_lines)
        code_lines.append("")

    code_lines.extend([
        "# Plate paths",
        f"plate_paths = {repr(plate_paths)}",
        "",
        "# Global configuration",
    ])

    config_repr = generate_clean_dataclass_repr(global_config, indent_level=0, clean_mode=clean_mode)
    code_lines.append(f"global_config = GlobalPipelineConfig(\n{config_repr}\n)")
    code_lines.append("")

    # Generate pipeline data (exact logic from lines 164-198)
    code_lines.extend(["# Pipeline steps", "pipeline_data = {}", ""])

    default_step = FunctionStep(func=lambda: None)
    for plate_path, steps in pipeline_data.items():
        code_lines.append(f'# Steps for plate: {Path(plate_path).name}')
        code_lines.append("steps = []")
        code_lines.append("")

        for i, step in enumerate(steps):
            code_lines.append(f"# Step {i+1}: {step.name}")

            # Generate all FunctionStep parameters automatically using introspection
            step_args = _generate_step_parameters(step, default_step, clean_mode)

            args_str = ",\n    ".join(step_args)
            code_lines.append(f"step_{i+1} = FunctionStep(\n    {args_str}\n)")
            code_lines.append(f"steps.append(step_{i+1})")
            code_lines.append("")

        code_lines.append(f'pipeline_data["{plate_path}"] = steps')
        code_lines.append("")

    return "\n".join(code_lines)


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Convert OpenHCS debug pickle files to runnable Python scripts.")
    parser.add_argument("pickle_file", help="Path to the input pickle file.")
    parser.add_argument("output_file", nargs='?', default=None, help="Path to the output Python script file (optional).")
    parser.add_argument("--clean", action="store_true", help="Generate a clean script with only non-default parameters.")
    
    args = parser.parse_args()
    
    convert_pickle_to_python(args.pickle_file, args.output_file, clean_mode=args.clean)

if __name__ == "__main__":
    main()
