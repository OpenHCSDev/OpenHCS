Basic Workflow: Stitching Images
===============================

This guide walks you through the process of stitching microscope images using OpenHCS. We'll use a practical example with sample data to demonstrate each step, from adding your plate to viewing the final stitched image.

----------------------------

In this guide, we will use sample microscope data from a neurite outgrowth assay. The data is available for download from this link: <!placeholder for link to sample data>.

The dataset comes from a 96-well plate assay performed with a custom microfluidic plate developed in our lab, so the images may look different from standard cell culture formats. This tutorial is intended only to demonstrate the basics of OpenHCS—the same workflow applies to any plate format, and OpenHCS can be used across a wide range of HCS imaging experiments.

Step 1: Adding a Plate
----------------------

**What is a plate?**
````````````````````

In microscopy, a "plate" refers to a sample holder containing multiple wells (like a 96-well plate used in experiments). Each well may contain multiple images (or "fields") taken at different positions. OpenHCS organizes your images based on this plate structure.

***Supported plate formats:***

OpenHCS currently supports:
- ImageXpress plate format
- Opera Phenix plate format
- OpenHCS's native ZARR format - a flexible format for storing large image datasets, that can be generated using OpenHCS

The plate provided in the example dataset is a ZARR plate. The steps remain the same for other supported formats.

**How to add a plate**
````````````````````

1. Open the Plate Manager window from the Windows menu.

2. Click the "Add" button.

   <!-- IMAGE: Screenshot of Plate Manager with "Add Plate" button highlighted -->

3. Navigate to the folder containing your microscope images and hit "choose". In the example data, this is the "basic_example_data" folder

4. OpenHCS will detect the microscope format automatically and load it into the plate manager.

5. Click "Init" to initialize the plate for processing.

   <!-- IMAGE: Screenshot showing plate initialization dialog -->

6. If the Compile button is no longer greyed out (it wont be in this case), the plate is ready for processing.


Step 2: Setting up a Stitching Pipeline
---------------------------------------

Once you learn more about OpenHCS pipelines, you can create your own stitching pipelines. For now, we'll use a pipeline with values tuned for this experiment.


**Loading a Pipeline from Disk**
````````````````````````````````````

If you already have a stitching pipeline:

1. In the Pipeline Editor, click "Load".

2. Navigate to your saved pipeline file and select it. In the example data, this file is called "basic_image_stitching.pipeline".

3. The pipeline will load with all its steps and settings.

**Understanding Pipelines, Steps, and Functions**
```````````````````````````````

**What is a pipeline?**
----------------------

A pipeline is a sequence of steps that process your images in a specific order. Think of it like a laboratory protocol:

- **Laboratory protocol example:** Fix cells → Permeabilize → Block → Add antibodies → Wash → Image
- **Stitching pipeline example:** Load images → Find overlaps → Align tiles → Blend edges → Create final image

A step in OpenHCS is a single operation. This doesn't mean they only do one thing, however. Many steps perform multiple operations. Open the "Initial Processing" by clicking on it, and then clicking on "Edit" so we can take a deeper look.

**Steps and the Step Editor**
-----------------------------

There are 2 tabs in the Step Editor: "Step Settings" and "Function Pattern". Lets look at step settings for now.

<!-- IMAGE: Screenshot of Step Editor with "Step Settings" tab highlighted, and each section numbered --> 

1. **Step Name**: This is the name of the step. You can change it to something more descriptive if you want.
2. **Variable Components**:

   - These tell OpenHCS how to split up images before processing.

   - Typical image microscopy plates have many "dimensions", such like which well they came from, which site in the well, which channel (DAPI, FITC, TL-20), which timepoint (for live imaging), or which z dimension it was on (for 3D image, commonly reffered to as a "z-slice   ").
  
   - Variable components let you choose which of these dimensions should define separate groups of images. Each group is then processed independently.
  
   - In this example, the variable component is the site. This means that each site in the well will be processed separately.


   If that doesn't make sense, think about it this way: Imagine you have a stack of exam papers from multiple classes, and each paper is labeled with both the class and the student’s seat number. If you group the papers by class, all the papers from Class A go into one pile, Class B into another, and so on — this is similar to setting Well as the variable component in OpenHCS. On the other hand, if you group the papers by seat number, all students who sat in Seat 1 — whether in Class A, B, or C — go into a single pile, all students in Seat 2 go into another pile, and so on. This is analogous to setting Site as the variable component, where all images from the same site number, across all wells, are grouped together. In both cases, the grouping determines how the data are split before any further processing. It might seem unusual to group the tests by seat number, but in some scenarios, it makes sense to analyze data based on a specific variable rather than the more obvious one. For our image processing, we want to handle each site individally because stitching requires spatial continuity - you don’t want to mix tiles from different wells or experimental conditions. So setting Site as the variable component ensures that each site’s tiles are processed as their own unit, rather than combining unrelated fields.

3. **Group By**
  
   - This tells OpenHCS how to treat variations inside each group.
  
   - In other words, after the images have been split into groups (using Variable Components), Group By decides what differences still matter inside those groups. 
  
   - For example, in this example we want to process each channel differently: our DAPI and FITC fluorescence channels need different filtering than our TL-20 channel. So we “Group By” channel.
  
   - Important: Group By must be different from Variable Components. That’s because once you split images into groups by a certain dimension, there’s only one value of that dimension in each group, so it doesn’t make sense to vary it again.


   If that doesnt make sense, think about it this way: Imagine you have the aforementioned exam papers, but you decided to be extra mean this year and have multiple sections in the exam paper, testing multiple subjects. Each paper has scores for Math, Science, and English. You want to process each subject individually because the grading rules differ. So, you “Group By” subject within each class pile, and use a different answer key to mark each test. Similarily, in OpenHCS, you might want to vary your analysis based on which fluorescence markers you stained with.
   
   Whats important is that you cannot Group By the same thing you used for Variable Components. If you already set your variable component so that you seperated the papers by class, each class pile only contains papers from that one class — there’s no variation left in class within the pile. So trying to "vary" your grading - i.e. group by class again would make no sense; there’s only one class in each pile, just like in OpenHCS, where you can’t vary a dimension that has already been used to define the groups.

Variable components and group by settings are used to process the entire plate but dynamically adjust to the different variables in the dataset. This is especially useful for large datasets with many variables. You should consider your experimental setup and your analysis goal in order to determine how to group your data.

4. **Input Source**

   - This is the source of the images for this step. Typically, this will be the output of the previous step. It can also be the original images from the plate if you so choose. Pipelines are dynamic and can have multiple branches. Since this is the first step, the input source is the original images from the plate.


5. **Step Well Filter config**

   - This allows you to filter which wells are processed in this step. For example, if you only want to process wells A1 and B1, you can set that here. In this case, we want to process all wells, so we leave it blank. You can also change the mode to "exclude" if you want to exclude certain wells instead of including them.


6. **Step Materialization Config**

   - Materialization allows you to save the results of a single step to disk, so you can see intermediary results. Typically, the only files that are saved are the final outputs of the last step in the pipeline, but this allows you to save outputs from any step, if you so choose. We won't worry about that for now. The settings in materialization config are pretty self-explanatory, so we won't go into detail here. What is something you should note is that the materializaation config "inherits" from the global configuration, so it will have the same settings as the global config unless you change them here.


7. **Napari/Fiji Streaming Config**

   - This allows you to visualize the results of this step in Napari or Fiji. We won't go into detail here, but you can set it up if you want to visualize the results of this step.


Now, click on the "Function Pattern" tab at the top of the window.

**Functions and Function patterns**
-----------------------------------

A step consists of a "Function pattern" which is a series of operations each step will do. Each function is a specific operation that will be performed on the images. 

<!-- IMAGE: Screenshot of Step Editor with "Function Pattern" tab highlighted, and the different parts of the windows explained briefly   -->

You can add, remove, or edit functions as needed. For now, we won't change anything here, but this step is just processing the images by running certain filters on them to prepare them for the image stitching algorithm. However, at the left of the top bar, you can see that you can change the selected channels, and hit the arrows to cycle through the channels. This is because we set our "Group By" to channel, so we can see how this step will process each channel differently.


**Basic Stitching Pipeline Overview**
`````````````````````````````````````

Hit save and close the step editor. Now, lets take a look at the entire pipeline. The overall goal of this pipeline is to create 1 composite image for each well, using all the sites of that well. It consists of 5 steps:

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
- Whats important to note is that this step doesn't output any images. It only outputs the positions of each tile, which are used in the next step.

**Step 4: Re-processing**
- Prepares your original images for final assembly
- Can adjust brightness, contrast, or other properties
- Uses the original images (not the pre-processed ones made from step 1)

**Step 5: Assembling**
- Takes the positions from Step 3 and the images from Step 4
- Places each image in its correct position
- Blends the edges where images overlap
- Creates the final stitched image for each well (combining all sites in the well)




