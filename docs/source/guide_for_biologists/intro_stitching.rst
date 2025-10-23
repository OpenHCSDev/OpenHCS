Introdutory workflow
===============================

This guide will walk you through a basic image stitching and analysis workflow in OpenHCS. By the end, you'll understand how to set up a plate, create a stitching pipeline, and visualize results.

Step 1: Adding a Plate
----------------------

**What is a plate?**

A plate (like a 96-well plate) contains multiple wells, each with multiple images ("fields") at different positions. OpenHCS organizes images by this structure.

**Supported formats:** ImageXpress, Opera Phenix, OpenHCS ZARR (example dataset format)

** Adding a plate:**

For now, we will use a synthetic dataset included with OpenHCS. Under "View" in the main menu, click "Generate Synthetic plate", or click Ctrl+Shift+G. Click confirm in the dialog that appears.

<!-- IMAGE: Screenshot guide of above-->

This creates a synthetic plate with random data, and creates a sample stitching + analysis pipeline. Hit "Init" to initialize the plate. 

.. dropdown:: Uploading your own data

  For reference, if you'd rather upload your own dataset, follow these steps:

  1. Open Plate Manager (Windows menu)
  2. Click "Add" → navigate to your dataset folder → "Choose"
  3. OpenHCS will auto-detect the format and load it
  4. Click "Init" to initialize
  5. Open the pipeline editor

Step 2: Exploring the Image Browser & Metadata Viewer
----------------------------

**Image Browser**
The Image Browser lets you view and explore images in your plate. Click on "Meta" in the plate manager to open it.

.. figure:: ../_static/image_browser.png
   :alt: Image Browser

   *In the Image Browser, you can navigate through the different wells and fields of your plate, and view the images associated with each one.*

This table in the middle shows all images in the plate. You can filter images by well, field, channel, timepoint, etc. using the filters on the left. On the right, the configuration for either the Napari or Fiji streaming viewer can be adjusted. For details on each configuration option, refer to :doc:`configuration_reference`, or hover over the (?) button next to each option for a tooltip.

**Metadata Viewer**
If you switch to the "Metadata" tab at the top, you can view metadata associated with your images, such as acquisition settings, experimental conditions, and annotations, as well as edit it.

.. figure:: ../_static/metadata_viewer.png
   :alt: Metadata Viewer

   *In the Metadata tab, you can view and edit metadata associated with your images, such as acquisition settings, experimental conditions, and annotations.*



Now, let's look at how to do things with these images. Open the Pipeline editor.

Step 3: Setting up a Stitching Pipeline
---------------------------------------

**Understanding Pipelines**

A pipeline is a sequence of steps that process your images in a specific order. Think of it like a laboratory protocol.

Each pipeline is made of multiple steps. A step in OpenHCS is a single operation. This doesn't mean they only do one thing, however. Many steps perform multiple operations. 

<!-- IMAGE: Screenshot of Pipeline Editor with steps visible -->

.. dropdown:: Sharing/Importing Pipelines

   You can share pipelines by clicking the "Code" button and copying the generated code. Anyone else can paste it into their own code viewer and load your pipeline, and vice versa.


**Steps and the Step Editor**
```````````````````````````````
Lets take a look at a individual step by opening the Step Editor. Double-click on the first step in the pipeline (named "Image Enhancement Processing") to open it.

<!-- IMAGE: Screenshot of Pipeline Editor with arrow pointing at step editor-->


There are 2 tabs in the Step Editor: "Step Settings" and "Function Pattern". Lets look at step settings for now.


<!-- IMAGE: Screenshot of Step Editor with "Step Settings" tab highlighted, and each section numbered --> 

1. **Step Name**: This is the name of the step. You can change it to something more descriptive if you want.
2. **Step Description**: A brief description of what this step does.
3. **Variable Components**:

   - These tell OpenHCS how to split up images before processing.

   - Typical image microscopy plates have many "dimensions", such like which well they came from, which site in the well, which channel (DAPI, FITC, TL-20), which timepoint (for live imaging), or which z dimension it was on (for 3D image, commonly reffered to as a "z-slice   ").
  
   - OpenHCS groups images into "piles" based on the variable components you select. Each pile is processed separately. 
   
   - The variable component you choose determines which variable changes within a pile. All other dimensions (not selected as variable components) remain the same within that pile.

   - OpenHCS will create a separate pile for every unique combination of the non-variable dimensions.

   - In this example, the variable component is the site. The other dimensions are well and channel. This means that for each well and channel combination, there will be a seperate pile, and within each pile, the only difference between images is the site. So, for well A1 and channel 'Wavelength 1', there will be a pile with an image for each site. There will be another pile for well A1 and channel 'Wavelength 2', again with images for each site, and so on.
    .. dropdown:: Extra help

      If that doesn't make sense, think about it this way: Imagine you're a teacher with exam papers from multiple classes (Class A, B, C), 
      multiple sections (Math, Science, English), multiple time periods (Morning, Evening), and multiple seat numbers (1-30) in each class.
      
      If you select "Time period" as your Variable Component:
      
      - You'd create separate piles for each class, section and seat number combination
      - Within each pile, all papers will have the same class, subject, and seat number — only the time period will differ.
      - For example: One pile might have all papers from Class A, Seat #1, across all sessions
      - Another pile would have Science papers from Class B, seat #15, and so on.
      
      
      In our microscopy example where "site" is the Variable Component:

      - We create separate processing groups where only the site varies
      - Each group contains images from all sites of a specific channel of a specific well
      - This is done because sometimes the processing we want to do (like stitching) needs to consider all sites together for each well and channel. Or, we might want to have our variable component be channel so that we can compare how different fluorescence markers look in the same well and site.
   
4. **Group By**
  
   - This tells OpenHCS how to treat variations inside each group.
  
   - In other words, after the images have been split into groups (using Variable Components), Group By decides what differences still matter inside those groups. 
  
   - For example, in this example we want to process each channel differently: our Wavelength 1 channel need different filtering than our Wavelength 2 channel. So we “Group By” channel.
  
   
 .. dropdown:: Extra help

      If that doesn't make sense, think about it this way: 
      
      Imagine you're a teacher with exam papers from multiple classes (Class A, B, C), multiple sections (Math, Science, English), multiple time periods (Morning, Evening) , and multiple seat numbers (1-30) in each class.
      
      You want to process each subject individually because the grading rules differ. So, you “Group By” subject within each class pile, and use a different answer key to mark each test. 
      
      Similarly, in OpenHCS, you might want to vary your analysis based on which fluorescence markers you stained with.


5. **Input Source**: Which images are being used (previous step output or original plate images);

6. **Step Well Filter**: Process only specific wells (e.g., A1 and B1). Leave blank to process all wells.

7. **Materialization Config**: Save intermediate results to disk (inherits from global config unless changed).

8. **Napari/Fiji Streaming Config**: Visualize step results in Napari or Fiji (inherits from global config as well).

For more details on each configuration option, refer to :doc:`configuration_reference`, or hover over the (?) button next to each option for a tooltip.
why does the above :doc: thingy not work 
**Function Pattern Tab**

Click "Function Pattern" at top. A step's function pattern is its series of operations.

- Add/remove/edit functions as needed
- This step applies filters to prepare images for stitching
- Use arrows (top-left) to cycle through channels and see channel-specific processing
- Example: (need new example for synthetic data)

**Pipeline Overview**
Now that we've explored one step, let's look at the overall pipeline. This pipeline is designed for stitching and analyzing images. It processes images, stitches them together, and then analyzes the stitched images to extract useful information (in this case, it runs a simple cell-counting analysis on the stitched images).

(In progress)