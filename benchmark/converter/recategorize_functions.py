"""
Recategorize absorbed CellProfiler functions with correct variable_components semantics.

Uses LLM to analyze function signatures and determine the correct category:
- image_operation: Process each site independently, channels stacked → VariableComponents.SITE
- z_projection: Process z-stacks, expects (Z, H, W) → VariableComponents.Z_INDEX  
- channel_operation: Process each channel independently → VariableComponents.CHANNEL

This fixes the semantic correctness issue where all functions were categorized as
"image_operation" during absorption, leading to incorrect iteration semantics.
"""

import json
import logging
import os
from pathlib import Path
from typing import Dict, Any
import inspect
import importlib

logging.basicConfig(level=logging.INFO, format='%(asctime)s [%(levelname)s] %(name)s: %(message)s')
logger = logging.getLogger(__name__)

# OpenRouter API configuration
OPENROUTER_API_KEY = os.environ.get("OPENROUTER_API_KEY")
OPENROUTER_API_URL = "https://openrouter.ai/api/v1/chat/completions"
MODEL = "google/gemini-3-flash-preview"  # Cheap and fast


CATEGORIZATION_PROMPT = """You are analyzing a CellProfiler function that has been absorbed into OpenHCS.

Your task: Determine the correct category based on what the function NEEDS to receive.

CRITICAL SEMANTICS:
- variable_components controls what dimension 0 of the 3D array represents
- The orchestrator groups files and stacks them based on variable_components

Categories:
1. **image_operation** (default for most functions)
   - variable_components=[VariableComponents.SITE]
   - Orchestrator groups by (well, channel, z) → stacks SITES → (S, H, W)
   - With PURE_2D contract: unstacks and processes each site independently
   - Use for: Single-channel operations (segmentation, filtering, thresholding, etc.)
   - Example: IdentifyPrimaryObjects processes DAPI channel across all sites

2. **z_projection** (for 3D volumetric operations)
   - variable_components=[VariableComponents.Z_INDEX]
   - Orchestrator groups by (well, site, channel) → stacks Z-SLICES → (Z, H, W)
   - Function receives full z-stack and processes it (e.g., max projection)
   - Use for: Functions that NEED z-stacks (max projection, 3D segmentation)
   - Example: MakeProjection receives (Z, H, W) and projects to (H, W)
   - NOT for time-lapse! Time-lapse uses sequential_components, not variable_components

3. **channel_operation** (for inherently multichannel operations)
   - variable_components=[VariableComponents.CHANNEL]
   - Orchestrator groups by (well, site, z) → stacks CHANNELS → (C, H, W)
   - Function receives ALL channels together (e.g., RGB composite, colocalization)
   - Use for: Functions that NEED multiple channels simultaneously
   - Example: MeasureColocalization needs 2+ channels, GrayToColorRgb needs 3 channels
   - NOT for single-channel operations!

Function to categorize:
```python
{function_code}
```

Analyze the function:
1. Does it NEED z-stacks? (z_projection)
2. Does it NEED multiple channels simultaneously? (channel_operation)
3. Otherwise: image_operation (default)

Key indicators:
- z_projection: Docstring mentions "(Z, H, W)", "z-stack", "projection", "3D volumetric"
- channel_operation: Docstring mentions "RGB", "composite", "colocalization", "multiple channels", function expects (C, H, W) with C > 1
- image_operation: Everything else (single-channel operations, per-site processing)

IMPORTANT:
- Time-lapse tracking (TrackObjects) is NOT z_projection - it's image_operation with sequential_components
- Single-channel operations are image_operation, NOT channel_operation

Respond with ONLY a JSON object:
{{
    "category": "image_operation" | "z_projection" | "channel_operation",
    "confidence": 0.0-1.0,
    "reasoning": "Brief explanation of why this category was chosen"
}}
"""


class FunctionRecategorizer:
    """Recategorize absorbed functions using LLM analysis."""
    
    def __init__(self, api_key: str):
        self.api_key = api_key
        self.contracts_path = Path(__file__).parent.parent / "cellprofiler_library" / "contracts.json"
        self.functions_dir = Path(__file__).parent.parent / "cellprofiler_library" / "functions"
        
    def load_contracts(self) -> Dict[str, Any]:
        """Load existing contracts.json."""
        return json.loads(self.contracts_path.read_text())
    
    def save_contracts(self, contracts: Dict[str, Any]):
        """Save updated contracts.json."""
        self.contracts_path.write_text(json.dumps(contracts, indent=2))
        logger.info(f"Saved updated contracts to {self.contracts_path}")
    
    def get_function_code(self, function_name: str) -> str:
        """Get the source code of a function."""
        # Convert function_name to module name (e.g., identify_primary_objects -> identifyprimaryobjects)
        module_name = function_name.replace('_', '')
        module_path = self.functions_dir / f"{module_name}.py"
        
        if not module_path.exists():
            logger.warning(f"Module not found: {module_path}")
            return ""
        
        # Read the file and extract the main function
        content = module_path.read_text()
        
        # Find the main function definition (decorated with @numpy or starting with def {function_name})
        lines = content.split('\n')
        function_lines = []
        in_function = False
        indent_level = None
        
        for i, line in enumerate(lines):
            # Look for function definition
            if f"def {function_name}(" in line:
                in_function = True
                indent_level = len(line) - len(line.lstrip())
                function_lines.append(line)
                continue
            
            if in_function:
                # Check if we've left the function (dedent or new def)
                if line.strip() and not line.startswith(' ' * (indent_level + 1)):
                    if line.strip().startswith('def ') or (len(line) - len(line.lstrip())) <= indent_level:
                        break
                
                function_lines.append(line)
                
                # Stop after docstring and first ~30 lines of function body
                if len(function_lines) > 50:
                    break
        
        return '\n'.join(function_lines)

    def categorize_function(self, function_name: str) -> Dict[str, Any]:
        """Use LLM to categorize a single function."""
        import requests

        # Get function source code
        function_code = self.get_function_code(function_name)
        if not function_code:
            return {
                "category": "image_operation",
                "confidence": 0.0,
                "reasoning": "Could not load function source code"
            }

        # Build prompt
        prompt = CATEGORIZATION_PROMPT.format(function_code=function_code)

        # Call OpenRouter API
        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
        }

        payload = {
            "model": MODEL,
            "messages": [
                {"role": "user", "content": prompt}
            ],
            "temperature": 0.0,  # Deterministic
        }

        try:
            response = requests.post(OPENROUTER_API_URL, headers=headers, json=payload, timeout=30)
            response.raise_for_status()

            result = response.json()
            content = result["choices"][0]["message"]["content"]

            # Parse JSON response
            # Remove markdown code blocks if present
            if "```json" in content:
                content = content.split("```json")[1].split("```")[0].strip()
            elif "```" in content:
                content = content.split("```")[1].split("```")[0].strip()

            categorization = json.loads(content)
            return categorization

        except Exception as e:
            logger.error(f"Error categorizing {function_name}: {e}")
            return {
                "category": "image_operation",
                "confidence": 0.0,
                "reasoning": f"Error: {str(e)}"
            }

    def recategorize_all(self):
        """Recategorize all functions in contracts.json."""
        contracts = self.load_contracts()

        total = len(contracts)
        logger.info(f"Recategorizing {total} functions...")

        updated = 0
        changed = 0

        for i, (module_name, meta) in enumerate(contracts.items(), 1):
            function_name = meta["function_name"]
            old_category = meta.get("category", "image_operation")

            logger.info(f"[{i}/{total}] Categorizing {module_name} ({function_name})...")

            # Get new categorization from LLM
            result = self.categorize_function(function_name)
            new_category = result["category"]
            confidence = result["confidence"]
            reasoning = result["reasoning"]

            # Update contracts
            meta["category"] = new_category
            meta["confidence"] = confidence
            meta["reasoning"] = reasoning

            updated += 1

            if new_category != old_category:
                changed += 1
                logger.info(f"  ✓ Changed: {old_category} → {new_category} (confidence: {confidence})")
                logger.info(f"    Reasoning: {reasoning}")
            else:
                logger.info(f"  ✓ Unchanged: {new_category} (confidence: {confidence})")

        # Save updated contracts
        self.save_contracts(contracts)

        logger.info("=" * 60)
        logger.info(f"Recategorization complete!")
        logger.info(f"  Total functions: {total}")
        logger.info(f"  Updated: {updated}")
        logger.info(f"  Changed: {changed}")
        logger.info(f"  Unchanged: {updated - changed}")


def main():
    """Main entry point."""
    if not OPENROUTER_API_KEY:
        logger.error("OPENROUTER_API_KEY environment variable not set")
        return

    recategorizer = FunctionRecategorizer(OPENROUTER_API_KEY)
    recategorizer.recategorize_all()


if __name__ == "__main__":
    main()

