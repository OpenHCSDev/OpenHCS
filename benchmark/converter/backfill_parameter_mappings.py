"""
Backfill parameter mappings for already-absorbed functions.

Uses a cheap LLM (Gemini Flash) to generate parameter mappings for all 88 absorbed functions
without re-running the expensive absorption process.
"""

import json
import logging
import os
import re
import requests
from pathlib import Path
from typing import Dict, List, Optional

logging.basicConfig(level=logging.INFO, format='%(message)s')
logger = logging.getLogger(__name__)

OPENROUTER_ENDPOINT = "https://openrouter.ai/api/v1/chat/completions"
# Try Gemini 3.0 Flash first, fall back to 2.0 if not available
CHEAP_MODEL = "google/gemini-3-flash-preview"  # Gemini 3.0 Flash (experimental)


class ParameterMappingBackfiller:
    """Backfill parameter mappings for absorbed functions."""
    
    def __init__(self):
        self.library_root = Path("benchmark/cellprofiler_library")
        self.functions_dir = self.library_root / "functions"
        self.contracts_file = self.library_root / "contracts.json"
        self.cp_source_root = Path("benchmark/cellprofiler_source")

        # Load contracts to get module names
        with open(self.contracts_file) as f:
            self.contracts = json.load(f)
    
    def backfill_all(self):
        """Backfill parameter mappings for all absorbed functions."""
        logger.info(f"Backfilling parameter mappings for {len(self.contracts)} functions...")
        
        success_count = 0
        fail_count = 0
        
        for module_name, contract_info in self.contracts.items():
            function_name = contract_info['function_name']
            try:
                self.backfill_function(module_name, function_name)
                success_count += 1
            except Exception as e:
                logger.error(f"  ❌ Failed {module_name} ({function_name}): {e}")
                fail_count += 1
        
        logger.info(f"\n✅ Backfilled {success_count} functions")
        if fail_count > 0:
            logger.warning(f"❌ Failed {fail_count} functions")
    
    def backfill_function(self, module_name: str, function_name: str):
        """Backfill parameter mapping for a single function."""
        # Find the converted OpenHCS function file
        file_name = function_name.replace('_', '')
        func_file = self.functions_dir / f"{file_name}.py"

        if not func_file.exists():
            raise FileNotFoundError(f"Function file not found: {func_file}")

        # Read the converted function code
        converted_code = func_file.read_text()

        # Try to find the original CellProfiler source file
        original_file = self._find_original_source(module_name)
        original_code = original_file.read_text() if original_file else None

        # Get CellProfiler settings from a .cppipe file that uses this module
        cp_settings = self._find_cellprofiler_settings(module_name)
        if not cp_settings:
            logger.info(f"  ⚠️  No .cppipe examples found for {module_name}, skipping")
            return

        # Ask LLM to generate mapping (with or without original source)
        mapping = self._generate_mapping_with_llm(
            module_name,
            original_code,
            converted_code,
            cp_settings
        )

        # Inject mapping into docstring
        updated_code = self._inject_mapping(converted_code, mapping)

        # Write back
        func_file.write_text(updated_code)
        logger.info(f"  ✅ {function_name}")
    
    def _find_original_source(self, module_name: str) -> Optional[Path]:
        """
        Find the original CellProfiler source file for a module.

        Uses same logic as LibraryAbsorber:
        1. Check library/modules/_*.py first (pure algorithms - preferred)
        2. Check modules/*.py second (full classes)
        """
        module_lower = module_name.lower()

        # 1. Try library modules first (preferred source)
        library_dir = self.cp_source_root / "library" / "modules"
        if library_dir.exists():
            # Try with leading underscore
            candidate = library_dir / f"_{module_lower}.py"
            if candidate.exists():
                return candidate

            # Try searching for partial matches
            for file in library_dir.glob("_*.py"):
                if module_lower in file.stem.lower():
                    return file

        # 2. Try full modules directory
        modules_dir = self.cp_source_root / "modules"
        if modules_dir.exists():
            # Try exact match
            candidate = modules_dir / f"{module_lower}.py"
            if candidate.exists():
                return candidate

            # Try searching for partial matches
            for file in modules_dir.glob("*.py"):
                if file.name.startswith("_") or file.name == "__init__.py":
                    continue
                if module_lower in file.stem.lower():
                    return file

        return None
    
    def _find_cellprofiler_settings(self, module_name: str) -> Optional[List[str]]:
        """Find CellProfiler settings from .cppipe files."""
        cppipe_dir = Path("benchmark/cellprofiler_pipelines")
        
        for cppipe_file in cppipe_dir.glob("*.cppipe"):
            content = cppipe_file.read_text()
            
            # Find module blocks
            pattern = rf'{module_name}:\[module_num:\d+\|svn_version.*?\n\n'
            matches = re.findall(pattern, content, re.DOTALL)
            
            if matches:
                # Extract setting names from first match
                settings = []
                for line in matches[0].split('\n'):
                    if ':' in line and not line.strip().startswith(module_name):
                        setting_name = line.split(':')[0].strip()
                        if setting_name and not setting_name.startswith('    '):
                            settings.append(setting_name)
                
                return settings[:15]  # Limit to first 15
        
        return None

    def _generate_mapping_with_llm(
        self,
        module_name: str,
        original_code: str,
        converted_code: str,
        cp_settings: List[str]
    ) -> Dict[str, any]:
        """Use LLM to generate parameter mapping by comparing before/after code."""
        api_key = os.environ.get("OPENROUTER_API_KEY")
        if not api_key:
            raise ValueError("OPENROUTER_API_KEY not set")

        # Truncate code if too long (keep first 3000 chars of each)
        original_snippet = original_code[:3000] + ("..." if len(original_code) > 3000 else "") if original_code else "Not available"
        converted_snippet = converted_code[:3000] + ("..." if len(converted_code) > 3000 else "")

        prompt = f"""You are creating a parameter mapping for a CellProfiler → OpenHCS conversion.

CONVERTED OpenHCS Function:
```python
{converted_snippet}
```

ORIGINAL CellProfiler Code ({module_name}):
```python
{original_snippet}
```

CellProfiler Settings (from .cppipe files):
{chr(10).join(f"  - {s}" for s in cp_settings)}

Task: Map each CellProfiler setting to its corresponding Python parameter(s) in the converted function.

IMPORTANT:
- Study the converted function signature carefully
- "Typical diameter (Min,Max)" likely maps to ["min_diameter", "max_diameter"]
- "Discard objects outside diameter" likely maps to "exclude_size"
- "Discard objects touching border" likely maps to "exclude_border_objects"
- "Method to distinguish clumped objects" likely maps to "unclump_method"
- "Size of smoothing filter" likely maps to "smoothing_filter_size"
- "Suppress local maxima" likely maps to "maxima_suppression_size"
- "Speed up by using lower-resolution" likely maps to "low_res_maxima"
- "Maximum number of objects" likely maps to "maximum_object_count"
- Settings about input/output image names map to null (handled by pipeline)

Output ONLY valid JSON (no markdown, no explanation):
{{
  "CellProfiler Setting Name": "python_parameter_name",
  "Another Setting": ["param1", "param2"],
  "Image Selection Setting": null
}}

Be thorough - map ALL settings that correspond to function parameters."""

        headers = {
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
        }

        payload = {
            "model": CHEAP_MODEL,
            "messages": [{"role": "user", "content": prompt}],
            "temperature": 0.1,
        }

        response = requests.post(OPENROUTER_ENDPOINT, headers=headers, json=payload, timeout=60)
        response.raise_for_status()

        result = response.json()
        content = result["choices"][0]["message"]["content"]

        # Parse JSON from response
        # Remove markdown code blocks if present
        content = re.sub(r'```json\s*', '', content)
        content = re.sub(r'```\s*', '', content)

        return json.loads(content.strip())

    def _inject_mapping(self, code: str, mapping: Dict[str, any]) -> str:
        # Inject parameter mapping into docstring
        if not mapping:
            return code

        lines = code.split('\n')

        # Find the function definition line first
        func_def_line = None
        for i, line in enumerate(lines):
            if line.strip().startswith('def '):
                func_def_line = i
                break

        if func_def_line is None:
            return code

        # Find the function's docstring (first docstring after def)
        docstring_start = None
        docstring_end = None
        in_docstring = False

        triple_quote = '"' * 3
        for i in range(func_def_line, len(lines)):
            line = lines[i]
            if triple_quote in line and not in_docstring:
                docstring_start = i
                in_docstring = True
                if line.count(triple_quote) == 2:
                    docstring_end = i
                    break
            elif triple_quote in line and in_docstring:
                docstring_end = i
                break

        if docstring_start is None or docstring_end is None:
            return code

        # Build mapping section
        mapping_lines = [
            "    CellProfiler Parameter Mapping:",
            "    (CellProfiler setting -> Python parameter)",
        ]

        for cp_setting, py_param in mapping.items():
            if py_param is None:
                mapping_lines.append(f"        '{cp_setting}' -> (pipeline-handled)")
            elif isinstance(py_param, list):
                params_str = ', '.join(py_param)
                mapping_lines.append(f"        '{cp_setting}' -> [{params_str}]")
            else:
                mapping_lines.append(f"        '{cp_setting}' -> {py_param}")

        mapping_lines.append("")  # Blank line after mapping

        # Insert right after opening docstring (after the """ line)
        lines.insert(docstring_start + 1, '\n'.join(mapping_lines))

        return '\n'.join(lines)


if __name__ == "__main__":
    backfiller = ParameterMappingBackfiller()
    backfiller.backfill_all()


