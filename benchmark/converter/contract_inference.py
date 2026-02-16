"""
Contract Inference - Runtime testing to determine ProcessingContract.

Instead of fragile static analysis, we run the converted function with
2D and 3D test data and observe actual behavior to infer the correct contract.
"""

import logging
import numpy as np
from dataclasses import dataclass
from enum import Enum
from typing import Callable, Optional, Tuple, Any

logger = logging.getLogger(__name__)


class InferredContract(Enum):
    """Inferred ProcessingContract from runtime behavior."""
    PURE_2D = "pure_2d"
    PURE_3D = "pure_3d"
    FLEXIBLE = "flexible"
    VOLUMETRIC_TO_SLICE = "volumetric_to_slice"
    UNKNOWN = "unknown"
    ERROR = "error"


@dataclass
class ContractInferenceResult:
    """Result of contract inference."""
    contract: InferredContract
    confidence: float  # 0.0 - 1.0
    
    # Test results
    handles_2d: bool = False
    handles_3d: bool = False
    output_2d_shape: Optional[Tuple[int, ...]] = None
    output_3d_shape: Optional[Tuple[int, ...]] = None
    
    # Errors if any
    error_2d: Optional[str] = None
    error_3d: Optional[str] = None
    
    # Additional notes
    notes: str = ""


class ContractInference:
    """
    Runtime contract inference for converted functions.
    
    Tests function with 2D and 3D inputs to determine:
    - PURE_2D: Only handles 2D, fails or wrong output on 3D
    - PURE_3D: Only handles 3D natively
    - FLEXIBLE: Handles both 2D and 3D correctly
    - VOLUMETRIC_TO_SLICE: Reduces 3D → 2D (projection)
    """
    
    def __init__(
        self,
        test_size_2d: Tuple[int, int] = (64, 64),
        test_size_3d: Tuple[int, int, int] = (8, 64, 64),
        seed: int = 42,
    ):
        self.test_size_2d = test_size_2d
        self.test_size_3d = test_size_3d
        self.seed = seed
    
    def _create_test_data(self) -> Tuple[np.ndarray, np.ndarray]:
        """Create reproducible test data."""
        np.random.seed(self.seed)
        
        # Create test images with some structure (not just noise)
        # This helps functions that expect real image-like data
        test_2d = np.random.rand(*self.test_size_2d).astype(np.float32)
        test_3d = np.random.rand(*self.test_size_3d).astype(np.float32)
        
        # Add some blob-like structures for segmentation functions
        y, x = np.ogrid[:self.test_size_2d[0], :self.test_size_2d[1]]
        center_y, center_x = self.test_size_2d[0] // 2, self.test_size_2d[1] // 2
        mask = ((y - center_y) ** 2 + (x - center_x) ** 2) < (min(self.test_size_2d) // 4) ** 2
        test_2d[mask] += 0.5
        test_2d = np.clip(test_2d, 0, 1)
        
        # Apply same to each slice of 3D
        for z in range(self.test_size_3d[0]):
            test_3d[z][mask] += 0.5
        test_3d = np.clip(test_3d, 0, 1)
        
        return test_2d, test_3d
    
    def infer(self, func: Callable, **kwargs) -> ContractInferenceResult:
        """
        Infer ProcessingContract by running function with test data.
        
        Args:
            func: The function to test
            **kwargs: Additional kwargs to pass to function
            
        Returns:
            ContractInferenceResult with inferred contract
        """
        test_2d, test_3d = self._create_test_data()
        
        result = ContractInferenceResult(
            contract=InferredContract.UNKNOWN,
            confidence=0.0,
        )
        
        # Test 2D
        try:
            out_2d = func(test_2d, **kwargs)
            if isinstance(out_2d, tuple):
                out_2d = out_2d[0]  # Extract main output
            result.handles_2d = True
            result.output_2d_shape = out_2d.shape if hasattr(out_2d, 'shape') else None
        except Exception as e:
            result.handles_2d = False
            result.error_2d = str(e)
            logger.debug(f"2D test failed: {e}")
        
        # Test 3D
        try:
            out_3d = func(test_3d, **kwargs)
            if isinstance(out_3d, tuple):
                out_3d = out_3d[0]  # Extract main output
            result.handles_3d = True
            result.output_3d_shape = out_3d.shape if hasattr(out_3d, 'shape') else None
        except Exception as e:
            result.handles_3d = False
            result.error_3d = str(e)
            logger.debug(f"3D test failed: {e}")
        
        # Infer contract from behavior
        result.contract, result.confidence, result.notes = self._infer_from_behavior(
            result, test_2d.shape, test_3d.shape
        )
        
        return result
    
    def _infer_from_behavior(
        self,
        result: ContractInferenceResult,
        input_2d_shape: Tuple[int, ...],
        input_3d_shape: Tuple[int, ...],
    ) -> Tuple[InferredContract, float, str]:
        """Infer contract from test behavior."""
        
        # Case 1: Only handles 2D
        if result.handles_2d and not result.handles_3d:
            return (
                InferredContract.PURE_2D,
                0.95,
                "Handles 2D, fails on 3D input"
            )
        
        # Case 2: Only handles 3D
        if result.handles_3d and not result.handles_2d:
            return (
                InferredContract.PURE_3D,
                0.95,
                "Handles 3D, fails on 2D input"
            )
        
        # Case 3: Handles neither
        if not result.handles_2d and not result.handles_3d:
            return (
                InferredContract.ERROR,
                1.0,
                f"Fails on both: 2D={result.error_2d}, 3D={result.error_3d}"
            )
        
        # Case 4: Handles both - need to check output shapes
        out_2d = result.output_2d_shape
        out_3d = result.output_3d_shape
        
        if out_2d is None or out_3d is None:
            return (
                InferredContract.FLEXIBLE,
                0.5,
                "Handles both but output shape unknown"
            )
        
        # Check for dimension reduction (volumetric → slice)
        if len(out_3d) < len(input_3d_shape):
            return (
                InferredContract.VOLUMETRIC_TO_SLICE,
                0.9,
                f"Reduces dimensions: {input_3d_shape} → {out_3d}"
            )
        
        # Check if 3D output preserves Z dimension
        if len(out_3d) == 3 and out_3d[0] == input_3d_shape[0]:
            # Preserves Z - could be FLEXIBLE or PURE_3D
            # If 2D output matches 2D input shape, it's FLEXIBLE
            if len(out_2d) == 2:
                return (
                    InferredContract.FLEXIBLE,
                    0.85,
                    "Handles both 2D and 3D with correct output shapes"
                )
            else:
                return (
                    InferredContract.PURE_3D,
                    0.7,
                    "3D output correct, 2D output has unexpected dimensions"
                )
        
        # Default: FLEXIBLE with lower confidence
        return (
            InferredContract.FLEXIBLE,
            0.6,
            f"Handles both: 2D {input_2d_shape}→{out_2d}, 3D {input_3d_shape}→{out_3d}"
        )


def infer_contract(func: Callable, **kwargs) -> ContractInferenceResult:
    """Convenience function for contract inference."""
    return ContractInference().infer(func, **kwargs)

