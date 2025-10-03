#!/usr/bin/env python3
"""
Export OpenHCS Pipeline to Python Script

Generates a standalone Python script from a Pipeline object that can be imported
into the GUI code editor.
"""

from pathlib import Path
from datetime import datetime
from typing import List, Dict, Any
from collections import defaultdict
from enum import Enum
from dataclasses import is_dataclass, fields

from openhcs.core.pipeline import Pipeline
from openhcs.core.steps.function_step import FunctionStep


def collect_imports_from_pipeline(pipeline: Pipeline) -> tuple:
    """
    Extract function and enum imports from pipeline steps.
    
    Returns:
        Tuple of (function_imports, enum_imports) where each is a dict mapping module -> set of names
    """
    function_imports = defaultdict(set)
    enum_imports = defaultdict(set)
    
    def register_imports(obj):
        """Recursively register imports from an object."""
        if isinstance(obj, Enum):
            enum_imports[obj.__class__.__module__].add(obj.__class__.__name__)
        elif is_dataclass(obj):
            module = obj.__class__.__module__
            name = obj.__class__.__name__
            function_imports[module].add(name)
            # Recursively process dataclass fields
            for f in fields(obj):
                field_value = getattr(obj, f.name, None)
                if field_value is not None:
                    register_imports(field_value)
        elif callable(obj):
            function_imports[obj.__module__].add(obj.__name__)
        elif isinstance(obj, (list, tuple)):
            for item in obj:
                register_imports(item)
        elif isinstance(obj, dict):
            for value in obj.values():
                register_imports(value)
    
    # Process all steps
    for step in pipeline.steps:
        # Process func pattern
        register_imports(step.func)
        
        # Process all step attributes
        for attr_name in dir(step):
            if not attr_name.startswith('_'):
                attr_value = getattr(step, attr_name, None)
                if attr_value is not None:
                    register_imports(attr_value)
    
    return function_imports, enum_imports


def generate_import_section(function_imports: Dict, enum_imports: Dict) -> List[str]:
    """Generate import statements from collected imports."""
    lines = []
    
    # Standard library imports
    lines.append("from pathlib import Path")
    lines.append("")
    
    # OpenHCS core imports
    lines.append("from openhcs.core.pipeline import Pipeline")
    lines.append("from openhcs.core.steps.function_step import FunctionStep")
    lines.append("")
    
    # Collect all unique modules
    all_modules = set(function_imports.keys()) | set(enum_imports.keys())
    
    # Group imports by top-level module
    openhcs_imports = defaultdict(set)
    for module in sorted(all_modules):
        names = function_imports.get(module, set()) | enum_imports.get(module, set())
        if names:
            openhcs_imports[module].update(names)
    
    # Generate import statements
    for module in sorted(openhcs_imports.keys()):
        names = sorted(openhcs_imports[module])
        if len(names) == 1:
            lines.append(f"from {module} import {names[0]}")
        else:
            lines.append(f"from {module} import (")
            for name in names[:-1]:
                lines.append(f"    {name},")
            lines.append(f"    {names[-1]}")
            lines.append(")")
    
    lines.append("")
    return lines


def serialize_value(value: Any) -> str:
    """Serialize a Python value to its string representation."""
    if value is None:
        return "None"
    elif isinstance(value, bool):
        return str(value)
    elif isinstance(value, (int, float)):
        return str(value)
    elif isinstance(value, str):
        return repr(value)
    elif isinstance(value, Enum):
        return f"{value.__class__.__name__}.{value.name}"
    elif isinstance(value, (list, tuple)):
        items = [serialize_value(item) for item in value]
        bracket = "[" if isinstance(value, list) else "("
        close = "]" if isinstance(value, list) else ")"
        return f"{bracket}{', '.join(items)}{close}"
    elif isinstance(value, dict):
        items = [f"{serialize_value(k)}: {serialize_value(v)}" for k, v in value.items()]
        return f"{{{', '.join(items)}}}"
    elif callable(value):
        return value.__name__
    elif is_dataclass(value):
        # Serialize dataclass as constructor call
        class_name = value.__class__.__name__
        field_values = []
        for f in fields(value):
            field_val = getattr(value, f.name)
            if field_val is not None:
                field_values.append(f"{f.name}={serialize_value(field_val)}")
        return f"{class_name}({', '.join(field_values)})"
    else:
        return repr(value)


def serialize_func_pattern(func_pattern: Any) -> str:
    """Serialize a function pattern (func, (func, params), [chain], or {dict})."""
    if callable(func_pattern):
        return func_pattern.__name__
    elif isinstance(func_pattern, tuple) and len(func_pattern) == 2:
        func, params = func_pattern
        func_name = func.__name__ if callable(func) else str(func)
        params_str = serialize_value(params)
        return f"({func_name}, {params_str})"
    elif isinstance(func_pattern, list):
        items = [serialize_func_pattern(item) for item in func_pattern]
        return f"[{', '.join(items)}]"
    elif isinstance(func_pattern, dict):
        items = [f"{serialize_value(k)}: {serialize_func_pattern(v)}" for k, v in func_pattern.items()]
        return f"{{{', '.join(items)}}}"
    else:
        return serialize_value(func_pattern)


def generate_step_code(step: FunctionStep, step_num: int) -> List[str]:
    """Generate code for a single pipeline step."""
    lines = []
    
    # Step comment
    lines.append(f"# Step {step_num}: {step.name}")
    
    # Collect non-default parameters
    default_step = FunctionStep(func=lambda: None)
    params = []
    
    # Always include func
    params.append(f"func={serialize_func_pattern(step.func)}")
    
    # Check other attributes
    for attr_name in ['name', 'variable_components', 'group_by', 'input_source', 
                      'step_well_filter_config', 'step_materialization_config', 
                      'napari_streaming_config', 'force_disk_output']:
        step_value = getattr(step, attr_name, None)
        default_value = getattr(default_step, attr_name, None)
        
        if step_value != default_value and step_value is not None:
            params.append(f"{attr_name}={serialize_value(step_value)}")
    
    # Generate FunctionStep constructor
    if len(params) <= 2:
        # Single line
        params_str = ", ".join(params)
        lines.append(f"step_{step_num} = FunctionStep({params_str})")
    else:
        # Multi-line
        lines.append(f"step_{step_num} = FunctionStep(")
        for param in params[:-1]:
            lines.append(f"    {param},")
        lines.append(f"    {params[-1]}")
        lines.append(")")
    
    lines.append(f"pipeline_steps.append(step_{step_num})")
    lines.append("")
    
    return lines


def export_pipeline_to_python(pipeline: Pipeline, output_path: Path) -> None:
    """
    Export a Pipeline object to a standalone Python script.
    
    Args:
        pipeline: Pipeline object to export
        output_path: Path where the .py file should be saved
    """
    lines = []
    
    # Header
    lines.append('#!/usr/bin/env python3')
    lines.append('"""')
    lines.append(f'OpenHCS Pipeline Script - {pipeline.name}')
    lines.append(f'Generated: {datetime.now()}')
    lines.append('"""')
    lines.append('')
    
    # Collect imports
    function_imports, enum_imports = collect_imports_from_pipeline(pipeline)
    
    # Generate import section
    lines.extend(generate_import_section(function_imports, enum_imports))
    
    # Generate pipeline creation function
    lines.append('def create_pipeline():')
    lines.append('    """Create and return the pipeline."""')
    lines.append('    pipeline_steps = []')
    lines.append('    ')
    
    # Generate steps
    for i, step in enumerate(pipeline.steps, 1):
        step_lines = generate_step_code(step, i)
        # Indent all lines
        for line in step_lines:
            lines.append(f'    {line}')
    
    # Return pipeline
    lines.append(f'    return Pipeline(')
    lines.append(f'        steps=pipeline_steps,')
    lines.append(f'        name={serialize_value(pipeline.name)}')
    lines.append(f'    )')
    lines.append('')
    
    # Main block
    lines.append('')
    lines.append('if __name__ == "__main__":')
    lines.append('    pipeline = create_pipeline()')
    lines.append('    print(f"Pipeline created: {pipeline.name}")')
    lines.append('    print(f"Steps: {len(pipeline.steps)}")')
    
    # Write to file
    output_path = Path(output_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    
    with open(output_path, 'w') as f:
        f.write('\n'.join(lines))
    
    print(f"✅ Pipeline exported to: {output_path}")

