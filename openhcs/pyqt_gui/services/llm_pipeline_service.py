"""
LLM Pipeline Generation Service

Handles communication with LLM endpoints to generate OpenHCS pipeline code
from natural language descriptions.
"""

import logging
import requests
from typing import Optional, Dict, Any
from pathlib import Path

logger = logging.getLogger(__name__)


class LLMPipelineService:
    """
    Service for generating OpenHCS pipelines using LLM.

    Sends user requests to LLM endpoint with comprehensive system prompt
    containing OpenHCS API documentation and examples.
    """

    def __init__(self, api_endpoint: str = "http://localhost:11434/api/generate",
                 model: str = "qwen2.5-coder:32b"):
        """
        Initialize LLM service.

        Args:
            api_endpoint: LLM API endpoint URL (default: Ollama local endpoint)
            model: Model name to use for generation
        """
        self.api_endpoint = api_endpoint
        self.model = model
        self.system_prompt = self._build_system_prompt()

    def _build_system_prompt(self) -> str:
        """
        Build comprehensive system prompt with OpenHCS documentation.

        Returns:
            Complete system prompt string
        """
        # Read example pipeline from basic_pipeline.py
        basic_pipeline_path = Path(__file__).parent.parent.parent / "tests" / "basic_pipeline.py"
        try:
            with open(basic_pipeline_path, 'r') as f:
                example_pipeline = f.read()
        except Exception as e:
            logger.warning(f"Could not load example pipeline: {e}")
            example_pipeline = "# Example pipeline not available"

        prompt = f"""You are an expert OpenHCS pipeline generator. Generate complete, runnable OpenHCS pipeline code based on user descriptions.

# OpenHCS Architecture Principles

1. **Stateless Functions**: All processing functions must be pure input/output with no side effects
2. **Enum-Driven Patterns**: Use enums for configuration, not magic strings
3. **Fail-Loud Behavior**: No defensive programming, no hasattr checks, no silent error handling
4. **Dataclass Patterns**: Use dataclasses for structured configuration
5. **No Duck Typing**: Explicit interfaces and ABCs only

# OpenHCS Pipeline API

## Core Imports

```python
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.config import (
    LazyProcessingConfig, LazyStepWellFilterConfig, LazyStepMaterializationConfig,
    LazyNapariStreamingConfig, LazyFijiStreamingConfig
)
from openhcs.constants.constants import VariableComponents, InputSource, GroupBy
```

## FunctionStep Structure

FunctionStep is the core building block. It accepts:

- `func`: Single function, tuple (func, kwargs), list of functions, or dict for channel/well-specific routing
- `name`: Human-readable step name
- `processing_config`: LazyProcessingConfig for variable_components, group_by, input_source
- `step_well_filter_config`: LazyStepWellFilterConfig for well filtering
- `step_materialization_config`: LazyStepMaterializationConfig for saving outputs
- `napari_streaming_config`: LazyNapariStreamingConfig for Napari visualization
- `fiji_streaming_config`: LazyFijiStreamingConfig for Fiji/ImageJ visualization

## Function Pattern Examples

### Single Function
```python
FunctionStep(func=normalize_images, name="normalize")
```

### Function with Parameters
```python
FunctionStep(
    func=(stack_percentile_normalize, {{
        'low_percentile': 1.0,
        'high_percentile': 99.0
    }}),
    name="normalize"
)
```

### Function Chain (Sequential)
```python
FunctionStep(
    func=[
        (gaussian_blur, {{'sigma': 2.0}}),
        threshold_otsu,
        binary_opening
    ],
    name="segment"
)
```

### Channel-Specific Routing (Dictionary)
```python
FunctionStep(
    func={{
        "DAPI": [(gaussian_blur, {{'sigma': 1.0}}), threshold_otsu],
        "GFP": [(enhance_contrast, {{}}), detect_cells],
        "RFP": [normalize_illumination, segment]
    }},
    processing_config=LazyProcessingConfig(group_by=GroupBy.CHANNEL),
    name="channel_processing"
)
```

## Available Processing Functions

### NumPy/CPU Functions
```python
from openhcs.processing.backends.processors.numpy_processor import (
    stack_percentile_normalize,
    create_projection,
    create_composite
)
```

### CuPy/GPU Functions
```python
from openhcs.processing.backends.processors.cupy_processor import (
    stack_percentile_normalize,  # GPU version
    tophat,
    gaussian_filter
)
```

### PyTorch/GPU Functions
```python
from openhcs.processing.backends.processors.torch_processor import (
    stack_percentile_normalize,  # PyTorch version
    gaussian_filter_torch
)
```

### Analysis Functions
```python
from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_single_channel
from openhcs.processing.backends.pos_gen.ashlar_main_cpu import ashlar_compute_tile_positions_cpu
from openhcs.processing.backends.assemblers.assemble_stack_cpu import assemble_stack_cpu
```

### pyclesperanto (GPU OpenCL)
```python
from openhcs.pyclesperanto import gaussian_blur, threshold_otsu, binary_opening
```

## Configuration Options

### VariableComponents
Controls which dimensions vary during processing:
- `VariableComponents.SITE`: Process each site/field separately
- `VariableComponents.CHANNEL`: Process each channel separately
- `VariableComponents.Z_INDEX`: Process each Z-slice separately
- `VariableComponents.TIMEPOINT`: Process each timepoint separately
- `VariableComponents.WELL`: Process each well separately

### InputSource
- `InputSource.PREVIOUS_STEP`: Read from previous step output (default)
- `InputSource.PIPELINE_START`: Read from original input (for position computation, QC)

### GroupBy
- `GroupBy.CHANNEL`: Route functions by channel
- `GroupBy.WELL`: Route functions by well
- `GroupBy.ANALYSIS_TYPE`: Route by analysis type

## Example Pipeline

{example_pipeline}

# Your Task

Generate complete OpenHCS pipeline code based on user descriptions. Always:

1. Start with proper imports
2. Create empty `pipeline_steps = []` list
3. Define each step with FunctionStep
4. Append each step to pipeline_steps
5. Use appropriate variable_components for the task
6. Include helpful step names
7. Add comments explaining each step

Output ONLY the Python code, no explanations."""

        return prompt

    def generate_code(self, user_request: str, code_type: str = 'pipeline') -> str:
        """
        Generate code from user request based on context.

        Args:
            user_request: Natural language description of desired code
            code_type: Type of code to generate ('pipeline', 'step', 'config', 'function', 'orchestrator')

        Returns:
            Generated Python code as string

        Raises:
            Exception: If LLM request fails
        """
        try:
            # Build context-specific prompt suffix
            context_suffix = {
                'pipeline': "Generate complete pipeline_steps list with FunctionStep objects.",
                'step': "Generate a single FunctionStep object.",
                'config': "Generate a configuration object (LazyProcessingConfig, LazyStepWellFilterConfig, etc.).",
                'function': "Generate a function pattern (single function, list, or dict).",
                'orchestrator': "Generate complete orchestrator code with plate_paths, pipeline_data, and configs."
            }.get(code_type, "Generate OpenHCS code.")

            # Construct request payload (Ollama format)
            payload = {
                "model": self.model,
                "prompt": f"{self.system_prompt}\n\nContext: {context_suffix}\n\nUser Request:\n{user_request}\n\nGenerated Code:",
                "stream": False,
                "options": {
                    "temperature": 0.2,  # Low temperature for more deterministic code generation
                    "top_p": 0.9,
                }
            }

            logger.info(f"Sending request to LLM: {self.api_endpoint} (code_type={code_type})")
            response = requests.post(self.api_endpoint, json=payload, timeout=60)
            response.raise_for_status()

            result = response.json()
            generated_code = result.get('response', '')

            # Clean up code (remove markdown code blocks if present)
            generated_code = self._clean_generated_code(generated_code)

            logger.info(f"Successfully generated {code_type} code")
            return generated_code

        except requests.exceptions.RequestException as e:
            logger.error(f"LLM request failed: {e}")
            raise Exception(f"Failed to connect to LLM service: {e}")
        except Exception as e:
            logger.error(f"Code generation failed: {e}")
            raise

    def _clean_generated_code(self, code: str) -> str:
        """
        Clean generated code by removing markdown formatting.

        Args:
            code: Raw generated code

        Returns:
            Cleaned Python code
        """
        # Remove markdown code blocks
        if code.startswith("```python"):
            code = code[len("```python"):].lstrip()
        if code.startswith("```"):
            code = code[3:].lstrip()
        if code.endswith("```"):
            code = code[:-3].rstrip()

        return code.strip()
