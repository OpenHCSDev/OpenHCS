"""
Converted from CellProfiler: MatchTemplate
Original: MatchTemplate.run

Uses normalized cross-correlation to match a template to an image.
The output is a correlation coefficient image where each pixel represents
the Pearson correlation between the image region and the template.
"""

import numpy as np
from typing import Optional
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract


@numpy(contract=ProcessingContract.FLEXIBLE)
def match_template(
    image: np.ndarray,
    template: Optional[np.ndarray] = None,
    pad_input: bool = True,
) -> np.ndarray:
    """
    Match a template to an image using normalized cross-correlation.
    
    The output image contains Pearson product-moment correlation coefficients
    between the image and the template at each position. This is useful for
    finding objects similar to a cropped reference object.
    
    Note: This is not rotation invariant, so it works best when objects are
    approximately round or oriented in a similar direction.
    
    Args:
        image: Input image with shape (D, H, W) where D is the batch dimension.
               For multi-input mode, image[0] is the input image and image[1] is the template.
        template: Template image to match. If None, assumes template is stacked
                  in image as image[1]. Shape should be (H_t, W_t) or (1, H_t, W_t).
        pad_input: If True, pad the input image so output has same shape as input.
                   If False, output will be smaller by (template_size - 1).
    
    Returns:
        Correlation coefficient image with shape (D, H, W) where values range
        from -1 (anti-correlation) to 1 (perfect correlation).
    """
    from skimage.feature import match_template as skimage_match_template
    
    # Handle multi-input case: image and template stacked along dim 0
    if template is None:
        if image.shape[0] < 2:
            raise ValueError(
                "When template is not provided, image must have at least 2 slices "
                "in dimension 0: [input_image, template]"
            )
        input_image = image[0]  # (H, W)
        template_2d = image[1]  # (H_t, W_t)
        
        # Perform template matching
        output = skimage_match_template(
            image=input_image,
            template=template_2d,
            pad_input=pad_input
        )
        
        # Return with batch dimension
        return output[np.newaxis, ...].astype(np.float32)
    
    else:
        # Template provided separately - process each slice in dim 0
        # Ensure template is 2D
        if template.ndim == 3:
            template_2d = template[0]
        else:
            template_2d = template
        
        results = []
        for i in range(image.shape[0]):
            input_slice = image[i]  # (H, W)
            
            output = skimage_match_template(
                image=input_slice,
                template=template_2d,
                pad_input=pad_input
            )
            results.append(output)
        
        return np.stack(results, axis=0).astype(np.float32)