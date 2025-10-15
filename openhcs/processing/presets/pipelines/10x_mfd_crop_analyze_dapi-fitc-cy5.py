# Edit this pipeline and save to apply changes

# Automatically collected imports
from openhcs.constants.constants import VariableComponents
from openhcs.core.memory.decorators import DtypeConversion
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.analysis.cell_counting_cpu import DetectionMethod, count_cells_single_channel
from openhcs.processing.backends.analysis.multi_template_matching import multi_template_crop_reference_channel
from openhcs.processing.backends.analysis.skan_axon_analysis import AnalysisDimension, OutputMode, skan_axon_skeletonize_and_analyze
from openhcs.processing.backends.processors.cupy_processor import crop, tophat

# Pipeline steps
pipeline_steps = []

# Step 1: crop_device
step_1 = FunctionStep(
    func=(multi_template_crop_reference_channel, {
            'score_threshold': 0.1,
            'method': 1,
            'template_path': '/home/ts/nvme_usb/configs/templates/mfd_96_sobel_10x_whole_device.tif',
            'rotate_result': False
        }),
    name="crop_device",
    variable_components=[VariableComponents.CHANNEL]
)
pipeline_steps.append(step_1)

# Step 2: crop_compartments
step_2 = FunctionStep(
    func={        '1': (crop, {
            'width': 5046,
            'height': 3694
        }),
        '2': (crop, {
            'width': 5046,
            'height': 3694
        }),
        '3': (crop, {
            'width': 5046,
            'height': 3694,
            'start_x': 5253,
            'dtype_conversion': DtypeConversion.UINT16
        }),
        '4': [
        (crop, {
            'width': 5046,
            'height': 3694
        }),
        tophat
    ]
    },
    name="crop_compartments"
)
pipeline_steps.append(step_2)

# Step 3: analysis
step_3 = FunctionStep(
    func={        '1': [],
        '2': (count_cells_single_channel, {
            'min_cell_area': 40,
            'max_cell_area': 200,
            'enable_preprocessing': False,
            'return_segmentation_mask': True,
            'detection_method': DetectionMethod.WATERSHED,
            'dtype_conversion': DtypeConversion.UINT8
        }),
        '3': (skan_axon_skeletonize_and_analyze, {
            'analysis_dimension': AnalysisDimension.TWO_D,
            'return_skeleton_visualizations': True,
            'skeleton_visualization_mode': OutputMode.SKELETON,
            'min_branch_length': 20.0,
            'dtype_conversion': DtypeConversion.UINT8
        }),
         '4': (count_cells_single_channel, {
            'min_cell_area': 100,
            'max_cell_area': 1000,
            'enable_preprocessing': False,
            'return_segmentation_mask': True,
            'detection_method': DetectionMethod.WATERSHED,
            'dtype_conversion': DtypeConversion.UINT8
        }),
    },
    name="analysis"
)
pipeline_steps.append(step_3)
