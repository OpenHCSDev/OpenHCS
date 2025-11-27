==========================================
Pyclesperanto Simple Implementation
==========================================

*Module: openhcs.processing.backends.analysis.cell_counting_pyclesperanto_simple*  
*Status: STABLE*

---

Overview
========

The simplified pyclesperanto cell counting implementation provides a direct, 334-line implementation of the Voronoi-Otsu labeling workflow with full OpenHCS materialization compatibility. This represents a 5x reduction in complexity compared to the original 1,578-line implementation.

Quick Reference
===============

.. code-block:: python

    from openhcs.processing.backends.analysis.cell_counting_pyclesperanto_simple import (
        count_cells_single_channel, count_cells_simple, DetectionMethod
    )
    
    # Full function (compatible with existing system)
    output_stack, results, masks = count_cells_single_channel(
        image_stack,
        detection_method=DetectionMethod.VORONOI_OTSU,
        gaussian_sigma=1.0,
        min_cell_area=50,
        max_cell_area=5000,
        return_segmentation_mask=True
    )
    
    # Quick function (minimal parameters)
    cell_count, positions = count_cells_simple(
        image,
        gaussian_sigma=1.0,
        min_cell_area=50,
        max_cell_area=5000
    )

Voronoi-Otsu Workflow
=====================

The implementation follows the exact pyclesperanto reference workflow:

.. code-block:: python

    import pyclesperanto_prototype as cle
    
    def voronoi_otsu_labeling(gpu_image):
        """Direct implementation of pyclesperanto reference workflow."""
        
        # 1. Gaussian blur for noise reduction
        blurred = cle.gaussian_blur(gpu_image, sigma_x=1.0, sigma_y=1.0)
        
        # 2. Detect spots (cell centers)
        spots = cle.detect_spots(blurred, radius_x=1, radius_y=1)
        
        # 3. Otsu threshold for cell boundaries
        binary = cle.threshold_otsu(blurred)
        
        # 4. Masked Voronoi labeling (cell segmentation)
        voronoi_labels = cle.masked_voronoi_labeling(spots, binary)
        
        return voronoi_labels

**Key insight**: This workflow combines spot detection (cell centers) with Voronoi tessellation (cell boundaries) for robust cell segmentation.

Detection Methods
=================

VORONOI_OTSU (Recommended)
---------------------------

.. code-block:: python

    output_stack, results, masks = count_cells_single_channel(
        image_stack,
        detection_method=DetectionMethod.VORONOI_OTSU,
        gaussian_sigma=1.0,
        min_cell_area=50,
        max_cell_area=5000
    )

**Best for**:

- Round cells with clear boundaries
- Fluorescence microscopy images
- Cells with varying intensities

**How it works**:

1. Gaussian blur reduces noise
2. Spot detection finds cell centers
3. Otsu threshold identifies cell regions
4. Voronoi tessellation separates touching cells

THRESHOLD (Fallback)
---------------------

.. code-block:: python

    output_stack, results, masks = count_cells_single_channel(
        image_stack,
        detection_method=DetectionMethod.THRESHOLD,
        gaussian_sigma=1.0,
        min_cell_area=50,
        max_cell_area=5000
    )

**Best for**:

- High-contrast images
- Well-separated cells
- Quick testing and debugging

**How it works**:

1. Gaussian blur reduces noise
2. Otsu threshold creates binary mask
3. Connected components labels cells
4. Area filtering removes noise

Materialization Compatibility
==============================

The simplified implementation maintains full compatibility with OpenHCS materialization:

.. code-block:: python

    # Results are CellCountResult objects
    result = results[0]
    
    # Access cell count
    print(f"Cell count: {result.cell_count}")
    
    # Access cell positions (N x 2 array)
    print(f"Positions: {result.cell_positions}")
    
    # Access cell areas (N-element array)
    print(f"Areas: {result.cell_areas}")
    
    # Segmentation masks (labeled image)
    mask = masks[0]  # Each cell has unique label

**Materialization outputs**:

- **JSON summary**: Cell counts per image
- **CSV details**: Cell positions and areas
- **ROI extraction**: Segmentation masks for all backends
- **Backend support**: Disk, OMERO, Napari, Fiji streaming

Pipeline Integration
====================

The simplified implementation integrates seamlessly with OpenHCS pipelines:

.. code-block:: python

    from openhcs.core.pipeline import Pipeline
    from openhcs.core.steps import FunctionStep
    
    # Create pipeline with cell counting step
    pipeline = Pipeline(
        steps=[
            FunctionStep(
                function='count_cells_single_channel',
                parameters={
                    'detection_method': DetectionMethod.VORONOI_OTSU,
                    'gaussian_sigma': 1.0,
                    'min_cell_area': 50,
                    'max_cell_area': 5000,
                    'return_segmentation_mask': True
                }
            )
        ]
    )
    
    # Execute pipeline
    pipeline.execute(plate_path)

**Key insight**: The simplified implementation uses the same materialization system as the original, ensuring backward compatibility.

Testing the Implementation
==========================

Run the test script to verify the implementation:

.. code-block:: bash

    cd openhcs/processing/backends/analysis/
    python test_simple_implementation.py

Test Coverage
-------------

.. code-block:: python

    # Test script covers:
    # 1. Synthetic cell image generation
    # 2. Full function testing
    # 3. Simple function testing
    # 4. Method comparison (VORONOI_OTSU vs THRESHOLD)
    # 5. Memory efficiency testing
    # 6. Visualization generation
    
    def test_simple_implementation():
        """Test simplified cell counting implementation."""
        
        # Create synthetic cell image
        image = create_synthetic_cells(
            num_cells=50,
            image_size=(512, 512),
            cell_radius=10
        )
        
        # Test full function
        output, results, masks = count_cells_single_channel(
            image[np.newaxis, ...],  # Add Z dimension
            detection_method=DetectionMethod.VORONOI_OTSU
        )
        
        # Verify results
        assert results[0].cell_count > 0
        assert len(results[0].cell_positions) == results[0].cell_count
        
        # Test simple function
        count, positions = count_cells_simple(image)
        assert count > 0
        assert len(positions) == count

**Test outputs**:

- Console summary of detected cells
- Comparison plots (VORONOI_OTSU vs THRESHOLD)
- Memory usage statistics
- Visualization of segmentation masks

Common Patterns
===============

Basic Cell Counting
-------------------

.. code-block:: python

    from openhcs.processing.backends.analysis.cell_counting_pyclesperanto_simple import (
        count_cells_single_channel, DetectionMethod
    )
    
    # Load image stack (Z, Y, X format)
    image_stack = load_image_stack('path/to/images')
    
    # Count cells
    output_stack, results, masks = count_cells_single_channel(
        image_stack,
        detection_method=DetectionMethod.VORONOI_OTSU,
        gaussian_sigma=1.0,
        min_cell_area=50,
        max_cell_area=5000,
        return_segmentation_mask=True
    )
    
    # Process results
    for i, result in enumerate(results):
        print(f"Image {i}: {result.cell_count} cells")

Quick Analysis
--------------

.. code-block:: python

    from openhcs.processing.backends.analysis.cell_counting_pyclesperanto_simple import count_cells_simple
    
    # For 2D images - quick one-liner
    cell_count, positions = count_cells_simple(
        your_2d_image,
        gaussian_sigma=1.0,
        min_cell_area=50,
        max_cell_area=5000
    )
    
    print(f"Detected {cell_count} cells")
    print(f"Positions:\n{positions}")

Parameter Tuning
----------------

.. code-block:: python

    # Adjust gaussian_sigma for noise level
    # - Higher sigma: More smoothing, fewer false positives
    # - Lower sigma: Less smoothing, more sensitivity
    
    # Low noise images
    output, results, masks = count_cells_single_channel(
        image_stack,
        gaussian_sigma=0.5  # Less smoothing
    )
    
    # High noise images
    output, results, masks = count_cells_single_channel(
        image_stack,
        gaussian_sigma=2.0  # More smoothing
    )
    
    # Adjust area filters for cell size
    # - min_cell_area: Remove small noise
    # - max_cell_area: Remove large artifacts
    
    # Small cells (e.g., bacteria)
    output, results, masks = count_cells_single_channel(
        image_stack,
        min_cell_area=10,
        max_cell_area=500
    )
    
    # Large cells (e.g., neurons)
    output, results, masks = count_cells_single_channel(
        image_stack,
        min_cell_area=200,
        max_cell_area=10000
    )

Migration from Original Implementation
=======================================

The simplified implementation provides a straightforward migration path:

.. code-block:: python

    # Old approach (complex, 50+ parameters)
    from openhcs.processing.backends.analysis.cell_counting_pyclesperanto import (
        count_cells_single_channel
    )
    
    output_stack, results, masks = count_cells_single_channel(
        image_stack,
        detection_method=DetectionMethod.BLOB_LOG,
        min_sigma=1.0,
        max_sigma=10.0,
        num_sigma=10,
        threshold=0.1,
        overlap=0.5,
        # ... 45+ more parameters
    )
    
    # New approach (simple, 5 core parameters)
    from openhcs.processing.backends.analysis.cell_counting_pyclesperanto_simple import (
        count_cells_single_channel, DetectionMethod
    )
    
    output_stack, results, masks = count_cells_single_channel(
        image_stack,
        detection_method=DetectionMethod.VORONOI_OTSU,
        gaussian_sigma=1.0,
        min_cell_area=50,
        max_cell_area=5000,
        return_segmentation_mask=True
    )

**Migration benefits**:

- 5x reduction in code complexity
- Fewer parameters to tune
- Better performance (less overhead)
- Same materialization outputs
- Full backward compatibility

Implementation Notes
====================

**🔬 Source Code**: 

- Implementation: ``openhcs/processing/backends/analysis/cell_counting_pyclesperanto_simple.py`` (line 1)
- Tests: ``openhcs/processing/backends/analysis/test_simple_implementation.py`` (line 1)
- README: ``openhcs/processing/backends/analysis/README_SIMPLE_IMPLEMENTATION.md`` (line 1)

**🏗️ Architecture**: 

- :doc:`../architecture/analysis_consolidation_system` - Materialization system
- :doc:`../user_guide/custom_functions` - Custom function integration

**📊 Performance**: 

- **Code size**: 334 lines (vs 1,578 lines original)
- **Memory usage**: Automatic GPU cleanup (no manual management)
- **Processing speed**: Faster (simplified workflow)
- **Parameter count**: 5 core parameters (vs 50+ original)

Key Design Decisions
====================

**Why Voronoi-Otsu instead of blob detection?**

Voronoi-Otsu is the pyclesperanto reference workflow, providing robust cell segmentation with minimal parameters. Blob detection requires extensive parameter tuning.

**Why two functions (full vs simple)?**

The full function maintains compatibility with existing pipelines. The simple function provides a quick API for interactive analysis.

**Why automatic GPU memory management?**

Pyclesperanto handles GPU memory automatically. Manual cleanup adds complexity without benefit.

Common Gotchas
==============

- **Image format must be (Z, Y, X)**: Single 2D images need ``image[np.newaxis, ...]`` to add Z dimension
- **GPU memory required**: Pyclesperanto requires CUDA-capable GPU
- **Area filters are in pixels**: Adjust based on image resolution and cell size
- **Gaussian sigma affects sensitivity**: Higher sigma reduces false positives but may miss small cells

Debugging Cell Counting Issues
===============================

Symptom: Too Many False Positives
----------------------------------

**Cause**: Noise or low gaussian_sigma

**Diagnosis**: Visualize segmentation masks

**Fix**: Increase gaussian_sigma or min_cell_area

.. code-block:: python

    # Increase smoothing
    output, results, masks = count_cells_single_channel(
        image_stack,
        gaussian_sigma=2.0  # Increased from 1.0
    )
    
    # Or increase minimum area
    output, results, masks = count_cells_single_channel(
        image_stack,
        min_cell_area=100  # Increased from 50
    )

Symptom: Missing Cells
-----------------------

**Cause**: Over-smoothing or high min_cell_area

**Diagnosis**: Check cell sizes in original image

**Fix**: Decrease gaussian_sigma or min_cell_area

.. code-block:: python

    # Reduce smoothing
    output, results, masks = count_cells_single_channel(
        image_stack,
        gaussian_sigma=0.5  # Decreased from 1.0
    )
    
    # Or decrease minimum area
    output, results, masks = count_cells_single_channel(
        image_stack,
        min_cell_area=20  # Decreased from 50
    )

Symptom: Touching Cells Not Separated
--------------------------------------

**Cause**: THRESHOLD method doesn't separate touching cells

**Diagnosis**: Switch to VORONOI_OTSU

**Fix**: Use Voronoi-Otsu method

.. code-block:: python

    # Use Voronoi-Otsu for cell separation
    output, results, masks = count_cells_single_channel(
        image_stack,
        detection_method=DetectionMethod.VORONOI_OTSU  # Changed from THRESHOLD
    )

