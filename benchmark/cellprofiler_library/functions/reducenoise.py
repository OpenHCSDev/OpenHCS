"""
Converted from CellProfiler: Reducenoise
Original: reducenoise
"""

import numpy as np
from openhcs.core.memory.decorators import numpy
from openhcs.processing.backends.lib_registry.unified_registry import ProcessingContract

@numpy(contract=ProcessingContract.PURE_2D)
def reduce_noise(
    image: np.ndarray,
    patch_size: int = 7,
    patch_distance: int = 11,
    cutoff_distance: float = 0.1,
) -> np.ndarray:
    """
    Reduces noise in an image using Non-Local Means (NLM) denoising.
    
    Args:
        image: Input 2D image slice (H, W).
        patch_size: Size of patches used for denoising.
        patch_distance: Maximal distance in pixels where to search patches used for denoising.
        cutoff_distance: Cut-off distance (h parameter in NLM). Higher values result in 
            a smoother image.
            
    Returns:
        Denoised image of shape (H, W).
    """
    from skimage.restoration import denoise_nl_means, estimate_sigma

    # Estimate noise standard deviation if not provided
    # NLM works best when sigma is known or estimated
    sigma_est = np.mean(estimate_sigma(image, channel_axis=None))
    
    # Perform Non-Local Means denoising
    # Note: skimage denoise_nl_means expects h to be related to sigma
    # We use cutoff_distance as the h parameter
    denoised = denoise_nl_means(
        image,
        h=cutoff_distance * sigma_est if sigma_est > 0 else cutoff_distance,
        patch_size=patch_size,
        patch_distance=patch_distance,
        fast_mode=True,
        channel_axis=None
    )
    
    return denoised.astype(image.dtype)