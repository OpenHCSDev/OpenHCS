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

### Supported plate formats

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

---------------------------------------
Step 2: Setting up a Stitching Pipeline
---------------------------------------

Once you learn more about OpenHCS pipelines, you can create your own stitching pipelines. For now, we'll use a pipeline with values tuned for this experiment.


**2a: Loading a Pipeline from Disk**
````````````````````````````````````

If you already have a stitching pipeline:

1. In the Pipeline Editor, click "Load".

2. Navigate to your saved pipeline file and select it. In the example data, this file is called "basic_image_stitching.pipeline".

3. The pipeline will load with all its steps and settings.

**2b: Understanding Pipelines**
```````````````````````````````

**What is a pipeline?**

A pipeline is a sequence of steps that process your images in a specific order. Think of it like a laboratory protocol:

- **Laboratory protocol example:** Fix cells → Permeabilize → Block → Add antibodies → Wash → Image
- **Stitching pipeline example:** Load images → Find overlaps → Align tiles → Blend edges → Create final image

A step in OpenHCS is a single operation. This doesn't mean they only do one thing, however. Many steps perform multiple operations. Open the "Initial Processing" by clicking on it, and then clicking on "Edit" so we can take a deeper look.

**Steps and the Step Editor**

There are 2 tabs in the Step Editor: "Step Settings" and "Function Pattern". Lets look at step settings for now.
<!-- IMAGE: Screenshot of Step Editor with "Step Settings" tab highlighted, and each section numbered --> 

1. **Step Name**: This is the name of the step. You can change it to something more descriptive if you want.
2. **Variable Components**:

   - These tell OpenHCS how to split up images before processing.

   - Typical image microscopy plates have many "dimensions", such like which well they came from, which site in the well, which channel (DAPI, FITC, TL-20), which timepoint, or which z dimension it was on (z-slice).
  
   - Variable components let you choose which of these dimensions should define separate groups of images. Each group is then processed independently.
  
   - In this example, the variable component is the site. This means that each site in the well will be processed separately.


   If that doesn't make sense, think about it this way: Imagine you have a stack of exam papers from multiple classes, and each paper is labeled with both the class and the student’s seat number. If you group the papers by class, all the papers from Class A go into one pile, Class B into another, and so on — this is similar to setting Well as the variable component in OpenHCS. On the other hand, if you group the papers by seat number, all students who sat in Seat 1 — whether in Class A, B, or C — go into a single pile, all students in Seat 2 go into another pile, and so on. This is analogous to setting Site as the variable component, where all images from the same site number, across all wells, are grouped together. In both cases, the grouping determines how the data are split before any further processing, allowing each group to be handled independently.

3. **Group By**
  
   - This tells OpenHCS how to treat variations inside each group.
  
   - In other words, after the images have been split into groups (using Variable Components), Group By decides what differences still matter inside those groups. 
  
   - For example, in this example we want to process each channel differently: our DAPI and FITC fluorescence channels need different filtering than our TL-20 channel. So we “Group By” channel.
  
   - Important: Group By must be different from Variable Components. That’s because once you split images into groups by a certain dimension, there’s only one value of that dimension in each group, so it doesn’t make sense to vary it again.


   If that doesnt make sense, think about it this way: Imagine you have the aforementioned exam papers, but you decided to be extra mean this year and have multiple sections in the exam paper, testing multiple subjects. Each paper has scores for Math, Science, and English. You want to process each subject individually because the grading rules differ. So, you “Group By” subject within each class pile.
   Whats important is that you cannot Group By the same thing you used for Variable Components. If you already grouped the papers by class, each class pile only contains papers from that one class — there’s no variation left in class within the pile. So trying to "vary" your grading by class again would make no sense; there’s only one class in each pile, just like in OpenHCS, where you can’t vary a dimension that has already been used to define the groups.
Variable components and group by settings are used to process the entire plate but dynamically adjust to the different variables in the dataset. This is especially useful for large datasets with many variables.

4. **Materialization Config**

   - Materialization allows you to save the results of a single step to disk, so you can see intermediary results. Typically, the only files that are saved are the final outputs of the last step in the pipeline, but this allows you to save outputs from any step, if you so choose. We won't worry about that for now. The settings in materialization config are pretty self-explanatory, so we won't go into detail here. What is something you should note is that the materializaation config "inherits" from the global configuration, so it will have the same settings as the global config unless you change them here.

5. **Napari s