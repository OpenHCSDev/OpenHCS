Basic Workflow: Stitching Images
===============================

This guide demonstrates stitching microscope images using OpenHCS with sample data from a neurite outgrowth assay.

The dataset uses a 96-well plate with a custom microfluidic design, so images may look different from standard formats. The workflow applies to any plate format and HCS imaging setup.

**Sample data:** <!placeholder for link to sample data>

Step 1: Adding a Plate
----------------------

**What is a plate?**

A plate (like a 96-well plate) contains multiple wells, each with multiple images ("fields") at different positions. OpenHCS organizes images by this structure.

**Supported formats:** ImageXpress, Opera Phenix, OpenHCS ZARR (example dataset format)

**Adding your plate:**

1. Open Plate Manager (Windows menu)
2. Click "Add" → navigate to "basic_example_data" → "Choose"
3. OpenHCS auto-detects the format and loads it
4. Click "Init" to initialize
5. Open the pipeline editor

Step 2: Setting up a Stitching Pipeline
---------------------------------------

**Loading a Pipeline:**

1. In Pipeline Editor, click "Load"
2. Select "basic_image_stitching.pipeline" from example data folder
3. Pipeline loads with all steps and settings

**Understanding Pipelines**

A pipeline is a sequence of steps that process your images in a specific order. Think of it like a laboratory protocol.

Each pipeline is made of multiple steps. A step in OpenHCS is a single operation. This doesn't mean they only do one thing, however. Many steps perform multiple operations. Select the "Initial Processing" by clicking on it, and then click on "Edit" so we can take a deeper look.

**Steps and the Step Editor**
```````````````````````````````

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

   - In this example, the variable component is the site. The other dimensions are well and channel. This means that for each well and channel combination, there will be a seperate pile, and within each pile, the only difference between images is the site. So, for well A1 and channel DAPI, there will be a pile with an image for each site. There will be another pile for well A1 and channel FITC, again with images for each site, and so on.
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
  
   - For example, in this example we want to process each channel differently: our DAPI and FITC fluorescence channels need different filtering than our TL-20 channel. So we “Group By” channel.
  
   
 .. dropdown:: Extra help

      If that doesn't make sense, think about it this way: 
      
      Imagine you're a teacher with exam papers from multiple classes (Class A, B, C), multiple sections (Math, Science, English), multiple time periods (Morning, Evening) , and multiple seat numbers (1-30) in each class.
      
      You want to process each subject individually because the grading rules differ. So, you “Group By” subject within each class pile, and use a different answer key to mark each test. 
      
      Similarly, in OpenHCS, you might want to vary your analysis based on which fluorescence markers you stained with.


5. **Input Source**: Which images are being used (previous step output or original plate images);

6. **Step Well Filter**: Process only specific wells (e.g., A1 and B1). Leave blank to process all wells.

7. **Materialization Config**: Save intermediate results to disk (inherits from global config unless changed).

8. **Napari/Fiji Streaming Config**: Visualize step results in Napari or Fiji (inherits from global config as well).

**Function Pattern Tab**

Click "Function Pattern" at top. A step's function pattern is its series of operations.

- Add/remove/edit functions as needed
- This step applies filters to prepare images for stitching
- Use arrows (top-left) to cycle through channels and see channel-specific processing
- Example: DAPI/FITC use "TopHat" filter; TL-20 uses "Sobel" filter

**Pipeline Overview**

Close the editor. This pipeline creates one composite image per well from all sites through five steps:

**Step 1: Pre-processing**
- Improves image quality before stitching
- May include background removal or contrast enhancement
- Runs on each individual image tile before they're stitched

**Step 2: Compositing**
- This "flattens" our piles of images into single images for each site
- It uses channel as its variable component, so the piles just have 3 images, one for each channel, and there is a seperate pile for each site
- It finds the average intensity for each pixel across all channels, and creates a single image using that.
- This is because the stitching algorithm only takes one image per site to find overlaps, and using a composite image with information from all channels helps it find overlaps better.

**Step 3: Position Generation (ASHLAR Algorithm)**
- This is where the actual stitching calculation happens
- The algorithm finds how your image tiles overlap
- It calculates the exact position where each tile should be placeholder
- It has its variable component set to site, so it looks at each well and finds the positions for all sites in that well. (The channel component doesn't matter here since we are using the composite images from step 2, and so the channels have been "flattened" into one image).
- Whats important to note is that this step doesn't output any images. It only outputs the positions of each tile, which are used in the next step.

**Step 4: Re-processing**
- Prepares original images for assembly
- Adjusts brightness/contrast
- Uses original images (not Step 1 output)

**Step 5: Assembling**
- Takes the positions from Step 3 and the images from Step 4
- Places each image in its correct position
- Blends the edges where images overlap
- Creates the final stitched image for each well (combining all sites in the well)




