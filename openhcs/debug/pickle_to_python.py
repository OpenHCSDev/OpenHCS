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
import dataclasses
from dataclasses import is_dataclass, fields

from openhcs.core.steps.function_step import FunctionStep

def collect_imports_from_data(data_obj):
    """Extract function, enum, and dataclass imports by traversing data structure."""
    function_imports = defaultdict(set)
    enum_imports = defaultdict(set)
    decorated_functions = set()

    def register_imports(obj):
        if isinstance(obj, Enum):
            enum_imports[obj.__class__.__module__].add(obj.__class__.__name__)
        elif is_dataclass(obj):
            module = obj.__class__.__module__
            name = obj.__class__.__name__
            function_imports[module].add(name)
            [register_imports(getattr(obj, f.name)) for f in fields(obj) if getattr(obj, f.name) is not None]
        elif callable(obj):
            # Skip bound methods (like step.process) - only import standalone functions
            if inspect.ismethod(obj):
                return
            if _is_external_registered_function(obj):
                # Use the actual module path but under openhcs namespace
                original_module = obj.__module__
                # Convert original module to openhcs namespace: cucim.skimage.filters -> openhcs.cucim.skimage.filters
                virtual_module = f'openhcs.{original_module}'
                function_imports[virtual_module].add(obj.__name__)
                decorated_functions.add(obj.__name__)
            else:
                function_imports[obj.__module__].add(obj.__name__)
        elif isinstance(obj, (list, tuple)):
            [register_imports(item) for item in obj]
        elif isinstance(obj, dict):
            [register_imports(value) for value in obj.values()]
        elif hasattr(obj, '__dict__') and obj.__dict__:
            [register_imports(value) for value in obj.__dict__.values()]

    register_imports(data_obj)
    return function_imports, enum_imports, decorated_functions


def _is_external_registered_function(func):
    """Check if function is an external library function registered with OpenHCS."""
    # External functions have slice_by_slice but not full OpenHCS decorations
    return (hasattr(func, 'slice_by_slice') and
            not hasattr(func, '__processing_contract__') and
            not func.__module__.startswith('openhcs.'))


def _get_function_library_name(func):
    """Get the library name for an external registered function."""
    from openhcs.processing.backends.lib_registry.registry_service import RegistryService

    # Find the function in the registry to get its library name
    all_functions = RegistryService.get_all_functions_with_metadata()
    for func_name, metadata in all_functions.items():
        if metadata.func is func:
            return metadata.registry.library_name

    return None


def _create_openhcs_library_modules():
    """Create virtual modules that mirror external library structure under openhcs namespace."""
    import types
    from openhcs.processing.backends.lib_registry.registry_service import RegistryService

    # Get all registered functions
    all_functions = RegistryService.get_all_functions_with_metadata()

    # Group functions by their full module path
    functions_by_module = {}
    for func_name, metadata in all_functions.items():
        if _is_external_registered_function(metadata.func):
            original_module = metadata.func.__module__
            virtual_module = f'openhcs.{original_module}'
            if virtual_module not in functions_by_module:
                functions_by_module[virtual_module] = {}
            functions_by_module[virtual_module][metadata.func.__name__] = metadata.func

    # Create virtual modules for each module path
    created_modules = []
    for virtual_module, functions in functions_by_module.items():
        if virtual_module not in sys.modules:
            module = types.ModuleType(virtual_module)
            module.__doc__ = f"Virtual module mirroring {virtual_module.replace('openhcs.', '')} with OpenHCS decorations"
            sys.modules[virtual_module] = module

            # Add all functions from this module
            for func_name, func in functions.items():
                setattr(module, func_name, func)

            created_modules.append(virtual_module)

    return created_modules

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
    # Collect imports from this pattern first to get name mappings
    function_imports, enum_imports, decorated_functions = collect_imports_from_data(func_obj)

    # Create containers for additional imports discovered during repr generation
    additional_function_imports = defaultdict(set)
    additional_enum_imports = defaultdict(set)

    # Merge initial imports with containers for additional imports
    for module, names in function_imports.items():
        additional_function_imports[module].update(names)
    for module, names in enum_imports.items():
        additional_enum_imports[module].update(names)

    # First pass: Generate pattern representation to collect all imports (including from expanded defaults)
    # Use temporary name mappings for this pass
    temp_import_lines, temp_name_mappings = format_imports_as_strings(additional_function_imports, additional_enum_imports)
    pattern_repr = generate_readable_function_repr(
        func_obj, indent, clean_mode, temp_name_mappings,
        required_function_imports=additional_function_imports,
        required_enum_imports=additional_enum_imports
    )

    # Second pass: Now that we have ALL imports (including from expanded defaults),
    # regenerate name mappings to handle any new collisions, then regenerate pattern repr
    import_lines, final_name_mappings = format_imports_as_strings(additional_function_imports, additional_enum_imports)

    # If name mappings changed (new collisions detected), regenerate pattern repr with correct aliases
    if final_name_mappings != temp_name_mappings:
        pattern_repr = generate_readable_function_repr(
            func_obj, indent, clean_mode, final_name_mappings,
            required_function_imports=additional_function_imports,
            required_enum_imports=additional_enum_imports
        )

    # Build complete code
    code_lines = ["# Edit this function pattern and save to apply changes", ""]
    if import_lines:
        code_lines.append("# Dynamic imports")
        code_lines.extend(import_lines)
        code_lines.append("")
    code_lines.append(f"pattern = {pattern_repr}")

    return "\n".join(code_lines)

def _value_to_repr(value, required_imports=None, name_mappings=None):
    """Converts a value to its Python representation string and tracks required imports."""
    if isinstance(value, Enum):
        enum_class_name = value.__class__.__name__
        enum_module = value.__class__.__module__

        # Collect import for the enum class
        if required_imports is not None and enum_module and enum_class_name:
            required_imports[enum_module].add(enum_class_name)

        # Use name mapping if available to handle collisions
        if name_mappings and (enum_class_name, enum_module) in name_mappings:
            mapped_name = name_mappings[(enum_class_name, enum_module)]
            return f"{mapped_name}.{value.name}"
        else:
            return f"{enum_class_name}.{value.name}"
    elif isinstance(value, str):
        # Use repr() for strings to properly escape newlines and special characters
        return repr(value)
    elif isinstance(value, Path):
        # Track that we need Path import
        if required_imports is not None:
            required_imports['pathlib'].add('Path')

        # Use name mapping if available
        path_name = 'Path'
        if name_mappings and ('Path', 'pathlib') in name_mappings:
            path_name = name_mappings[('Path', 'pathlib')]

        return f'{path_name}({repr(str(value))})'
    return repr(value)

def generate_clean_dataclass_repr(instance, indent_level=0, clean_mode=False, required_imports=None, name_mappings=None):
    """
    Generates a clean, readable Python representation of a dataclass instance,
    omitting fields that are set to their default values if clean_mode is True.
    This function is recursive and handles nested dataclasses.
    """
    if not dataclasses.is_dataclass(instance):
        return _value_to_repr(instance, required_imports, name_mappings)

    lines = []
    indent_str = "    " * indent_level
    child_indent_str = "    " * (indent_level + 1)

    # Get a default instance of the same class for comparison
    # CRITICAL FIX: For lazy dataclasses, create instance with raw values to preserve None vs concrete distinction
    if hasattr(instance, '_resolve_field_value'):
        # This is a lazy dataclass - create empty instance without triggering resolution
        default_instance = object.__new__(instance.__class__)

        # Set all fields to None (their raw default state) using object.__setattr__
        for field in dataclasses.fields(instance):
            object.__setattr__(default_instance, field.name, None)

        # Initialize any required lazy dataclass attributes
        if hasattr(instance.__class__, '_is_lazy_dataclass'):
            object.__setattr__(default_instance, '_is_lazy_dataclass', True)
    else:
        # Regular dataclass - use normal constructor
        default_instance = instance.__class__()

    for field in dataclasses.fields(instance):
        field_name = field.name

        # CRITICAL FIX: For lazy dataclasses, use raw stored value to avoid triggering resolution
        # This ensures tier 3 code generation only shows explicitly set pipeline config fields
        if hasattr(instance, '_resolve_field_value'):
            # This is a lazy dataclass - get raw stored value without triggering lazy resolution
            current_value = object.__getattribute__(instance, field_name)
            default_value = object.__getattribute__(default_instance, field_name)
        else:
            # Regular dataclass - use normal getattr
            current_value = getattr(instance, field_name)
            default_value = getattr(default_instance, field_name)

        if clean_mode and current_value == default_value:
            continue

        if dataclasses.is_dataclass(current_value):
            # Recursively generate representation for nested dataclasses
            nested_repr = generate_clean_dataclass_repr(current_value, indent_level + 1, clean_mode, required_imports, name_mappings)

            # Only include nested dataclass if it has non-default content
            if nested_repr.strip():  # Has actual content
                # Collect import for the nested dataclass
                if required_imports is not None:
                    class_module = current_value.__class__.__module__
                    class_name = current_value.__class__.__name__
                    if class_module and class_name:
                        required_imports[class_module].add(class_name)

                lines.append(f"{child_indent_str}{field_name}={current_value.__class__.__name__}(\n{nested_repr}\n{child_indent_str})")
            elif not clean_mode:
                # In non-clean mode, still include empty nested dataclasses
                if required_imports is not None:
                    class_module = current_value.__class__.__module__
                    class_name = current_value.__class__.__name__
                    if class_module and class_name:
                        required_imports[class_module].add(class_name)

                lines.append(f"{child_indent_str}{field_name}={current_value.__class__.__name__}()")
        else:
            value_repr = _value_to_repr(current_value, required_imports, name_mappings)
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
            f.write('        orchestrator = PipelineOrchestrator(plate_path)\n')
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


def generate_readable_function_repr(func_obj, indent=0, clean_mode=False, name_mappings=None,
                                   required_function_imports=None, required_enum_imports=None):
    """Generate readable Python representation with collision-resolved function names."""
    indent_str = "    " * indent
    next_indent_str = "    " * (indent + 1)
    name_mappings = name_mappings or {}

    # Get qualified function name for collisions (handle both original and virtual modules)
    def get_name(f):
        if not callable(f):
            return str(f)
        # Try virtual module first (for external functions), then original module
        virtual_module = f'openhcs.{f.__module__}'
        return (name_mappings.get((f.__name__, virtual_module), None) or
                name_mappings.get((f.__name__, f.__module__), f.__name__))

    if callable(func_obj):
        return get_name(func_obj)
    
    elif isinstance(func_obj, tuple) and len(func_obj) == 2 and callable(func_obj[0]):
        func, args = func_obj

        if not args and clean_mode:
            return get_name(func)

        # Get function signature defaults
        try:
            defaults = {k: v.default for k, v in inspect.signature(func).parameters.items()
                       if v.default is not inspect.Parameter.empty}
        except (ValueError, TypeError):
            defaults = {}

        if clean_mode:
            # Clean mode: only show non-default values
            final_args = {k: v for k, v in args.items()
                         if k not in defaults or v != defaults[k]}
        else:
            # Explicit mode: show ALL parameters (merge provided args with defaults)
            # Start with all defaults, then override with provided args
            final_args = {**defaults, **args}

            # Collect imports from default values that weren't in original args
            if required_function_imports is not None or required_enum_imports is not None:
                for param_name, default_value in defaults.items():
                    if param_name not in args:  # Only collect for newly added defaults
                        # Collect imports from this default value
                        if isinstance(default_value, Enum):
                            if required_enum_imports is not None:
                                enum_module = default_value.__class__.__module__
                                enum_class = default_value.__class__.__name__
                                required_enum_imports[enum_module].add(enum_class)
                        elif is_dataclass(default_value):
                            if required_function_imports is not None:
                                dc_module = default_value.__class__.__module__
                                dc_class = default_value.__class__.__name__
                                required_function_imports[dc_module].add(dc_class)

        if not final_args:
            return get_name(func) if clean_mode else f"({get_name(func)}, {{}})"

        args_items = [f"{next_indent_str}    '{k}': {generate_readable_function_repr(v, indent + 2, clean_mode, name_mappings, required_function_imports, required_enum_imports)}"
                     for k, v in final_args.items()]
        args_str = "{\n" + ",\n".join(args_items) + f"\n{next_indent_str}}}"
        return f"({get_name(func)}, {args_str})"

    elif isinstance(func_obj, list):
        if clean_mode and len(func_obj) == 1:
            return generate_readable_function_repr(func_obj[0], indent, clean_mode, name_mappings, required_function_imports, required_enum_imports)
        if not func_obj:
            return "[]"
        items = [generate_readable_function_repr(item, indent, clean_mode, name_mappings, required_function_imports, required_enum_imports) for item in func_obj]
        separator = f',\n{next_indent_str}'
        return f"[\n{next_indent_str}{separator.join(items)}\n{indent_str}]"

    elif isinstance(func_obj, dict):
        if not func_obj:
            return "{}"
        items = [f"{next_indent_str}'{k}': {generate_readable_function_repr(v, indent, clean_mode, name_mappings, required_function_imports, required_enum_imports)}"
                for k, v in func_obj.items()]
        separator = ',\n'
        return f"{{{separator.join(items)}\n{indent_str}}}"

    else:
        return _value_to_repr(func_obj, required_imports=required_enum_imports, name_mappings=name_mappings)


def _format_parameter_value(param_name, value, name_mappings=None):
    """Format parameter values with lazy dataclass preservation."""
    if isinstance(value, Enum):
        enum_class_name = value.__class__.__name__
        enum_module = value.__class__.__module__

        # Use name mapping if available to handle collisions
        if name_mappings and (enum_class_name, enum_module) in name_mappings:
            mapped_name = name_mappings[(enum_class_name, enum_module)]
            return f"{mapped_name}.{value.name}"
        else:
            return f"{enum_class_name}.{value.name}"
    elif isinstance(value, str):
        return f'"{value}"'
    elif isinstance(value, list) and value and isinstance(value[0], Enum):
        formatted_items = []
        for item in value:
            enum_class_name = item.__class__.__name__
            enum_module = item.__class__.__module__

            # Use name mapping if available to handle collisions
            if name_mappings and (enum_class_name, enum_module) in name_mappings:
                mapped_name = name_mappings[(enum_class_name, enum_module)]
                formatted_items.append(f"{mapped_name}.{item.name}")
            else:
                formatted_items.append(f"{enum_class_name}.{item.name}")

        return f"[{', '.join(formatted_items)}]"
    elif is_dataclass(value) and 'Lazy' in value.__class__.__name__:
        # Preserve lazy behavior by only including explicitly set fields
        class_name = value.__class__.__name__
        explicit_args = [
            f"{f.name}={_format_parameter_value(f.name, object.__getattribute__(value, f.name), name_mappings)}"
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


def _collect_enum_classes_from_step(step):
    """Collect enum classes referenced in step parameters for import generation."""
    from openhcs.core.steps.function_step import FunctionStep
    import inspect
    from enum import Enum

    enum_classes = set()
    sig = inspect.signature(FunctionStep.__init__)

    for param_name, param in sig.parameters.items():
        # Skip constructor-specific parameters and **kwargs
        if param_name in ['self', 'func'] or param.kind == inspect.Parameter.VAR_KEYWORD:
            continue

        value = getattr(step, param_name, param.default)
        if isinstance(value, Enum):
            enum_classes.add(type(value))
        elif isinstance(value, (list, tuple)):
            # Check for lists/tuples of enums
            for item in value:
                if isinstance(item, Enum):
                    enum_classes.add(type(item))

    return enum_classes


def _generate_step_parameters(step, default_step, clean_mode=False, name_mappings=None,
                             required_function_imports=None, required_enum_imports=None):
    """Generate FunctionStep constructor parameters using functional introspection."""
    from openhcs.core.steps.abstract import AbstractStep

    signatures = [(name, param) for name, param in inspect.signature(FunctionStep.__init__).parameters.items()
                  if name != 'self' and param.kind != inspect.Parameter.VAR_KEYWORD] + \
                 [(name, param) for name, param in inspect.signature(AbstractStep.__init__).parameters.items()
                  if name != 'self']

    return [f"{name}={generate_readable_function_repr(getattr(step, name, param.default), 1, clean_mode, name_mappings, required_function_imports, required_enum_imports) if name == 'func' else _format_parameter_value(name, getattr(step, name, param.default), name_mappings)}"
            for name, param in signatures
            if not clean_mode or getattr(step, name, param.default) != getattr(default_step, name, param.default)]


def generate_complete_pipeline_steps_code(pipeline_steps, clean_mode=False):
    """Generate complete Python code for pipeline steps with imports."""
    # Build code with imports and steps
    code_lines = ["# Edit this pipeline and save to apply changes", ""]

    # Collect imports from ALL data in pipeline steps (functions AND parameters)
    all_function_imports = defaultdict(set)
    all_enum_imports = defaultdict(set)
    all_decorated_functions = set()

    for step in pipeline_steps:
        # Collect all imports from step (functions, enums, dataclasses)
        func_imports, enum_imports, func_decorated = collect_imports_from_data(step.func)
        param_imports, param_enums, param_decorated = collect_imports_from_data(step)

        # Merge imports
        for module, names in func_imports.items():
            all_function_imports[module].update(names)
        for module, names in enum_imports.items():
            all_enum_imports[module].update(names)
        for module, names in param_imports.items():
            all_function_imports[module].update(names)
        for module, names in param_enums.items():
            all_enum_imports[module].update(names)
        all_decorated_functions.update(func_decorated)
        all_decorated_functions.update(param_decorated)

    # Add FunctionStep import (always needed for generated code)
    all_function_imports['openhcs.core.steps.function_step'].add('FunctionStep')

    # Virtual modules are now automatically created during OpenHCS import
    # No need to generate runtime virtual module creation code

    # First pass: Generate step code to collect all imports (including from expanded defaults)
    # Use temporary name mappings for this pass
    temp_import_lines, temp_name_mappings = format_imports_as_strings(all_function_imports, all_enum_imports)

    step_code_lines = []
    step_code_lines.append("# Pipeline steps")
    step_code_lines.append("pipeline_steps = []")
    step_code_lines.append("")

    default_step = FunctionStep(func=lambda: None)
    for i, step in enumerate(pipeline_steps):
        step_code_lines.append(f"# Step {i+1}: {step.name}")

        # Generate all FunctionStep parameters automatically using introspection
        # Pass import containers to collect additional imports from expanded defaults
        step_args = _generate_step_parameters(step, default_step, clean_mode, temp_name_mappings,
                                             all_function_imports, all_enum_imports)

        args_str = ",\n    ".join(step_args)
        step_code_lines.append(f"step_{i+1} = FunctionStep(\n    {args_str}\n)")
        step_code_lines.append(f"pipeline_steps.append(step_{i+1})")
        step_code_lines.append("")

    # Second pass: Now that we have ALL imports (including from expanded defaults),
    # regenerate name mappings to handle any new collisions, then regenerate step code if needed
    import_lines, final_name_mappings = format_imports_as_strings(all_function_imports, all_enum_imports)

    # If name mappings changed (new collisions detected), regenerate step code with correct aliases
    if final_name_mappings != temp_name_mappings:
        step_code_lines = []
        step_code_lines.append("# Pipeline steps")
        step_code_lines.append("pipeline_steps = []")
        step_code_lines.append("")

        for i, step in enumerate(pipeline_steps):
            step_code_lines.append(f"# Step {i+1}: {step.name}")
            step_args = _generate_step_parameters(step, default_step, clean_mode, final_name_mappings,
                                                 all_function_imports, all_enum_imports)
            args_str = ",\n    ".join(step_args)
            step_code_lines.append(f"step_{i+1} = FunctionStep(\n    {args_str}\n)")
            step_code_lines.append(f"pipeline_steps.append(step_{i+1})")
            step_code_lines.append("")

    # Add imports to output
    if import_lines:
        code_lines.append("# Automatically collected imports")
        code_lines.extend(import_lines)
        code_lines.append("")

    # Add step code
    code_lines.extend(step_code_lines)

    return "\n".join(code_lines)


def generate_complete_orchestrator_code(plate_paths, pipeline_data, global_config, clean_mode=False, pipeline_config=None, per_plate_configs=None):
    """
    Generate complete Python code for orchestrator config with imports.

    Args:
        plate_paths: List of plate paths
        pipeline_data: Dict mapping plate_path to list of steps
        global_config: GlobalPipelineConfig instance
        clean_mode: If True, only show non-default values
        pipeline_config: Single PipelineConfig to apply to all plates (legacy, deprecated)
        per_plate_configs: Dict mapping plate_path to PipelineConfig (preferred)
    """
    # Build complete code (extract exact logic from lines 150-200)
    code_lines = ["# Edit this orchestrator configuration and save to apply changes", ""]

    # Collect imports from ALL data in orchestrator (functions, parameters, config)
    all_function_imports = defaultdict(set)
    all_enum_imports = defaultdict(set)
    all_decorated_functions = set()

    # Collect from pipeline steps
    for plate_path, steps in pipeline_data.items():
        for step in steps:
            # Get imports from function patterns
            func_imports, enum_imports, func_decorated = collect_imports_from_data(step.func)
            # Get imports from step parameters
            param_imports, param_enums, param_decorated = collect_imports_from_data(step)

            # Merge all imports
            for module, names in func_imports.items():
                all_function_imports[module].update(names)
            for module, names in enum_imports.items():
                all_enum_imports[module].update(names)
            for module, names in param_imports.items():
                all_function_imports[module].update(names)
            for module, names in param_enums.items():
                all_enum_imports[module].update(names)
            all_decorated_functions.update(func_decorated)
            all_decorated_functions.update(param_decorated)

    # Don't collect imports from entire global config upfront - only collect what's actually used
    # This prevents importing unused classes and keeps the generated code clean

    # First pass: Collect imports needed for config representation (e.g., Path) BEFORE formatting imports
    config_repr_imports = defaultdict(set)
    temp_config_repr = generate_clean_dataclass_repr(global_config, indent_level=0, clean_mode=clean_mode, required_imports=config_repr_imports)

    # Merge config representation imports with main imports
    for module, names in config_repr_imports.items():
        all_function_imports[module].update(names)

    # Don't collect imports from entire pipeline config upfront - let representation generation handle it
    # This ensures only actually used imports are collected

    # Add always-needed imports for generated code structure
    all_function_imports['openhcs.core.steps.function_step'].add('FunctionStep')
    all_function_imports['openhcs.core.config'].add('PipelineConfig')
    all_function_imports['openhcs.core.orchestrator.orchestrator'].add('PipelineOrchestrator')
    all_function_imports['openhcs.core.config'].add('GlobalPipelineConfig')  # Always needed for global_config constructor

    # Virtual modules are now automatically created during OpenHCS import
    # No need for runtime virtual module creation

    # First pass: Generate name mappings for collision resolution (don't add imports yet)
    import_lines, name_mappings = format_imports_as_strings(all_function_imports, all_enum_imports)

    # Generate config representation and collect only the imports it actually needs
    config_repr_imports = defaultdict(set)
    config_repr = generate_clean_dataclass_repr(global_config, indent_level=0, clean_mode=clean_mode, required_imports=config_repr_imports, name_mappings=name_mappings)

    # Add only the imports that are actually used in the config representation
    for module, names in config_repr_imports.items():
        all_function_imports[module].update(names)

    # Generate readable plate path variables
    plate_path_vars = {}
    for i, plate_path in enumerate(plate_paths, 1):
        # Extract a readable name from the path
        path_str = str(plate_path)
        plate_name = path_str.split('/')[-1] if '/' in path_str else path_str
        var_name = f"plate_{i}_{plate_name.replace('-', '_').replace('.', '_')}"
        plate_path_vars[plate_path] = var_name

    code_lines.extend([
        "# Plate paths",
        ""
    ])

    # Generate individual plate path variables for readability
    for plate_path, var_name in plate_path_vars.items():
        code_lines.append(f'{var_name} = "{plate_path}"')

    code_lines.extend([
        "",
        "# Collect all plate paths",
        f"plate_paths = [{', '.join(plate_path_vars.values())}]",
        "",
        "# Global configuration",
    ])

    code_lines.append(f"global_config = GlobalPipelineConfig(\n{config_repr}\n)")
    code_lines.append("")

    # Handle per-plate configs (preferred) or single pipeline_config (legacy)
    if per_plate_configs:
        # NEW APPROACH: Group each plate's config and steps together
        code_lines.extend([
            "# Per-plate configurations and pipeline steps",
            "per_plate_configs = {}",
            "pipeline_data = {}",
            ""
        ])

        default_step = FunctionStep(func=lambda: None)

        # Iterate through plates in order, generating config + steps for each
        for plate_path in plate_paths:
            plate_name = str(plate_path).split('/')[-1] if '/' in str(plate_path) else str(plate_path)
            var_name = plate_path_vars[plate_path]

            code_lines.append(f"# ========== Plate: {plate_name} ==========")
            code_lines.append("")

            # Generate config for this plate
            if plate_path in per_plate_configs:
                config = per_plate_configs[plate_path]

                # Collect imports needed for this pipeline config
                pipeline_config_imports = defaultdict(set)
                pipeline_config_repr = generate_clean_dataclass_repr(
                    config,
                    indent_level=0,
                    clean_mode=clean_mode,
                    required_imports=pipeline_config_imports,
                    name_mappings=name_mappings
                )

                # Add the collected imports to the main import collection
                for module, names in pipeline_config_imports.items():
                    all_function_imports[module].update(names)

                code_lines.append(f'# Pipeline config for {plate_name}')
                code_lines.append(f'per_plate_configs[{var_name}] = PipelineConfig(\n{pipeline_config_repr}\n)')
                code_lines.append("")

            # Generate steps for this plate
            if plate_path in pipeline_data:
                steps = pipeline_data[plate_path]

                code_lines.append(f'# Pipeline steps for {plate_name}')
                code_lines.append("steps = []")
                code_lines.append("")

                for i, step in enumerate(steps):
                    code_lines.append(f"# Step {i+1}: {step.name}")

                    # Generate all FunctionStep parameters automatically using introspection with name mappings
                    step_args = _generate_step_parameters(step, default_step, clean_mode, name_mappings)

                    args_str = ",\n    ".join(step_args)
                    code_lines.append(f"step_{i+1} = FunctionStep(\n    {args_str}\n)")
                    code_lines.append(f"steps.append(step_{i+1})")
                    code_lines.append("")

                code_lines.append(f'pipeline_data[{var_name}] = steps')
                code_lines.append("")
    elif pipeline_config is not None:
        # Legacy single pipeline_config for all plates
        # Collect imports needed for pipeline config representation
        pipeline_config_imports = defaultdict(set)
        pipeline_config_repr = generate_clean_dataclass_repr(
            pipeline_config,
            indent_level=0,
            clean_mode=clean_mode,
            required_imports=pipeline_config_imports,
            name_mappings=name_mappings
        )

        # Add the collected imports to the main import collection
        for module, names in pipeline_config_imports.items():
            all_function_imports[module].update(names)

        # Regenerate import lines with the new imports
        import_lines, name_mappings = format_imports_as_strings(all_function_imports, all_enum_imports)

        code_lines.extend([
            "# Pipeline configuration (lazy GlobalPipelineConfig)",
            f"pipeline_config = PipelineConfig(\n{pipeline_config_repr}\n)",
            ""
        ])

        # Generate pipeline data
        code_lines.extend(["# Pipeline steps", "pipeline_data = {}", ""])

        default_step = FunctionStep(func=lambda: None)
        for plate_path, steps in pipeline_data.items():
            # Extract plate name without using Path in generated code
            plate_name = str(plate_path).split('/')[-1] if '/' in str(plate_path) else str(plate_path)
            var_name = plate_path_vars[plate_path]

            code_lines.append(f'# Steps for plate: {plate_name}')
            code_lines.append("steps = []")
            code_lines.append("")

            for i, step in enumerate(steps):
                code_lines.append(f"# Step {i+1}: {step.name}")

                # Generate all FunctionStep parameters automatically using introspection with name mappings
                step_args = _generate_step_parameters(step, default_step, clean_mode, name_mappings)

                args_str = ",\n    ".join(step_args)
                code_lines.append(f"step_{i+1} = FunctionStep(\n    {args_str}\n)")
                code_lines.append(f"steps.append(step_{i+1})")
                code_lines.append("")

            # Use variable name instead of full path string
            code_lines.append(f'pipeline_data[{var_name}] = steps')
            code_lines.append("")
    else:
        # No pipeline config overrides
        code_lines.extend([
            "# Pipeline configuration (lazy GlobalPipelineConfig)",
            "pipeline_config = PipelineConfig()",
            ""
        ])

        # Generate pipeline data
        code_lines.extend(["# Pipeline steps", "pipeline_data = {}", ""])

        default_step = FunctionStep(func=lambda: None)
        for plate_path, steps in pipeline_data.items():
            # Extract plate name without using Path in generated code
            plate_name = str(plate_path).split('/')[-1] if '/' in str(plate_path) else str(plate_path)
            var_name = plate_path_vars[plate_path]

            code_lines.append(f'# Steps for plate: {plate_name}')
            code_lines.append("steps = []")
            code_lines.append("")

            for i, step in enumerate(steps):
                code_lines.append(f"# Step {i+1}: {step.name}")

                # Generate all FunctionStep parameters automatically using introspection with name mappings
                step_args = _generate_step_parameters(step, default_step, clean_mode, name_mappings)

                args_str = ",\n    ".join(step_args)
                code_lines.append(f"step_{i+1} = FunctionStep(\n    {args_str}\n)")
                code_lines.append(f"steps.append(step_{i+1})")
                code_lines.append("")

            # Use variable name instead of full path string
            code_lines.append(f'pipeline_data[{var_name}] = steps')
            code_lines.append("")

    # Add orchestrator creation example with per-plate configs
    if per_plate_configs:
        code_lines.extend([
            "# Example: Create orchestrators with per-plate PipelineConfigs",
            "# orchestrators = {}",
            "# for plate_path in plate_paths:",
            "#     config = per_plate_configs.get(plate_path, PipelineConfig())",
            "#     orchestrator = PipelineOrchestrator(",
            "#         plate_path=plate_path,",
            "#         pipeline_config=config",
            "#     )",
            "#     orchestrators[plate_path] = orchestrator",
            ""
        ])
    else:
        code_lines.extend([
            "# Example: Create orchestrators with PipelineConfig",
            "# orchestrators = {}",
            "# for plate_path in plate_paths:",
            "#     orchestrator = PipelineOrchestrator(",
            "#         plate_path=plate_path,",
            "#         pipeline_config=pipeline_config",
            "#     )",
            "#     orchestrators[plate_path] = orchestrator",
            ""
        ])

    # Final pass: Generate all imports and prepend to code
    final_import_lines, final_name_mappings = format_imports_as_strings(all_function_imports, all_enum_imports)
    if final_import_lines:
        # Prepend imports to the beginning of the code
        final_code_lines = ["# Edit this orchestrator configuration and save to apply changes", ""]
        final_code_lines.append("# Automatically collected imports")
        final_code_lines.extend(final_import_lines)
        final_code_lines.append("")



        # Add the rest of the code (skip the first two lines which are the header)
        final_code_lines.extend(code_lines[2:])
        return "\n".join(final_code_lines)
    else:
        return "\n".join(code_lines)


def generate_config_code(config, config_class, clean_mode=True):
    """
    Generate Python code representation of a config object.

    Args:
        config: Config instance (PipelineConfig, GlobalPipelineConfig, etc.)
        config_class: The class of the config
        clean_mode: If True, only show non-default values

    Returns:
        str: Complete Python code with imports
    """
    # Collect imports needed for config representation
    required_imports = defaultdict(set)
    config_repr = generate_clean_dataclass_repr(
        config,
        indent_level=0,
        clean_mode=clean_mode,
        required_imports=required_imports
    )

    # Add the config class itself to imports
    required_imports[config_class.__module__].add(config_class.__name__)

    # Build complete code with imports
    code_lines = ["# Configuration Code", ""]

    # Add imports
    for module, names in sorted(required_imports.items()):
        names_str = ", ".join(sorted(names))
        code_lines.append(f"from {module} import {names_str}")

    code_lines.extend(["", f"config = {config_class.__name__}(", config_repr, ")"])

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
