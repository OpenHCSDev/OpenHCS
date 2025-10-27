What is OpenHCS?
============================

OpenHCS is a bioimage analysis platform designed for biologists who work with large amounts of microscopy images from high-content screening experiments. If you find yourself spending too much time stitching images together, running repetitive analyses, or struggling to keep your results organized and reproducible, OpenHCS can help.

When should I use OpenHCS?
--------------------------
You should use OpenHCS if you have any of the following needs:

1. **Stitch images from different microscopes:**
   OpenHCS can automatically combine (stitch) images from different types of High Content Screening microscopes (e.g., ImageXpress, Opera Phenix), making it easy to create complete views of your samples—even if your lab uses different imaging systems. The platform automatically detects your microscope format and handles the technical details.

2. **Run analysis on your images:**
   You can use OpenHCS to run common image analysis tasks like cell counting, intensity measurement, segmentation, and more—all on your stitched images in one place. The platform provides access to over 570+ processing functions from established libraries, so you don't need to learn multiple software packages.

3. **Build custom analysis workflows:**
   OpenHCS works like CellProfiler but with expanded capabilities. You can visually design multi-step analysis pipelines by dragging and dropping processing functions, then save and reuse these workflows across experiments. No programming knowledge is required for basic use, but advanced users can export pipelines as Python code for customization.

4. **Handle large-scale datasets:**
   OpenHCS is built to manage experiments with hundreds or thousands of images. It automatically compresses and organizes your data, uses GPU acceleration when available for faster processing, and can run on multiple CPU cores simultaneously. The platform keeps track of every step in your analysis, so you can easily repeat your work, share it with colleagues, or apply the same process to new data.

5. **Ensure reproducible results:**
   Every pipeline you create is automatically saved and can be exported as executable code. This means you can share your exact analysis methods with reviewers, run the same analysis on new datasets, or modify workflows without starting from scratch.

Supported Microscopes:
 - ImageXpress (Molecular Devices)
 - Opera Phenix (PerkinElmer)
 - Other microscopes with standard image formats (e.g., TIFF, PNG, JPEG)
 - Extensible framework for adding new microscope types

Supported Image Analysis Libraries:
  - pyclesperanto (GPU-accelerated processing)
  - scikit-image (comprehensive analysis toolkit)
  - CuPy, PyTorch, JAX, TensorFlow (GPU computing)
  - NumPy (array processing)
  - Custom OpenHCS functions

Key Features:
  - **Visual Pipeline Editor**: Drag-and-drop interface for creating analysis workflows
  - **GPU Acceleration**: Faster processing when compatible hardware is available
  - **Automatic Compression**: Efficient storage of large datasets
  - **Real-time Visualization**: Preview results as you build your pipeline
  - **Export to Code**: Convert visual pipelines to Python scripts for advanced users