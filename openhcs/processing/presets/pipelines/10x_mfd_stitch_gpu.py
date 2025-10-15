# Edit this pipeline and save to apply changes

# Automatically collected imports
from openhcs.constants.constants import VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.assemblers.assemble_stack_cupy import assemble_stack_cupy
from openhcs.processing.backends.pos_gen.ashlar_main_gpu import ashlar_compute_tile_positions_gpu
from openhcs.processing.backends.processors.cupy_processor import create_composite, sobel, stack_percentile_normalize, tophat

# Pipeline steps
pipeline_steps = []

# Step 1: process
step_1 = FunctionStep(
    func={        '1': [
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        }),
        (sobel, {
            'slice_by_slice': True
        }),
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        })
    ],
        '2': [
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        }),
        tophat,
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        })
    ],
        '3': [
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        }),
        tophat,
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        })
    ]
    },
    name="process"
)
pipeline_steps.append(step_1)

# Step 2: composite
step_2 = FunctionStep(
    func=create_composite,
    name="composite",
    variable_components=[VariableComponents.CHANNEL]
)
pipeline_steps.append(step_2)

# Step 3: gpu_stitch
step_3 = FunctionStep(
    func=(ashlar_compute_tile_positions_gpu, {
            'stitch_alpha': 0.2
        }),
    name="gpu_stitch"
)
pipeline_steps.append(step_3)

# Step 4: process_2
step_4 = FunctionStep(
    func={        '1': [
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        }),
        (sobel, {
            'slice_by_slice': True
        }),
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        })
    ],
        '2': [
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        }),
        tophat,
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        })
    ],
        '3': [
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        }),
        tophat,
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        })
    ],
        '4': [
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        }),
        tophat,
        (stack_percentile_normalize, {
            'low_percentile': 0.1,
            'high_percentile': 99.9
        })
    ]
    },
    name="process_2",
    input_source=InputSource.PIPELINE_START
)
pipeline_steps.append(step_4)

# Step 5: assemble
step_5 = FunctionStep(
    func=assemble_stack_cupy,
    name="assemble"
)
pipeline_steps.append(step_5)
