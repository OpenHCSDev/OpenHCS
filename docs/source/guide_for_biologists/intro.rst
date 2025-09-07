What is OpenHCS?
============================

OpenHCS is designed for biologists who work with large amounts of microscopy images and need a reliable, automated way to process and analyze their data. If you find yourself spending too much time stitching images together, running repetitive analyses, or struggling to keep your results organized and reproducible, OpenHCS can help.

When should I use OpenHCS?
-----------
You should use OpenHCS if you have any of the following needs:

1. **Stitch images from different microscopes:**
  OpenHCS can automatically combine (stitch) images from a different types of High Content Screening microscopes (e.g ImageXpress, Opera phenix), making it easy to create complete views of your samples—even if your lab uses different imaging systems.

2. **Run analysis on your images:**
  You can use OpenHCS to run common image analysis tasks (like cell counting, intensity measurement, segmentation, etc.) on your stitched images, all in one place.

3. **Handle large-scale datasets and reproducible pipelines:**
  OpenHCS is built to manage experiments with hundreds or thousands of images. It keeps track of every step in your analysis pipeline, so you can easily repeat your work, share it with colleagues, or apply the same process to new data.

Supported Microscopes:
 - ImageXpress (Molecular Devices)
 - Opera Phenix (PerkinElmer)
 - Other microscopes with standard image formats (e.g. TIFF, PNG, JPEG)

Supported Image Analysis libraries:
  - scikit-image
  - CuCIM
  - pyclesperanto
  - NumPy
  - Custom OpenHCS functions