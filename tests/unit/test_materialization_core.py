import json

import numpy as np
import pytest

from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend

from openhcs.processing.materialization import materialize, MaterializationSpec, RegionPropsOptions
from openhcs.processing.materialization.core import _generate_output_path


@pytest.mark.unit
def test_generate_output_path_strips_roi_zip_compound_suffix() -> None:
    base = "/tmp/A01_s001_w1_z001_t001_segmentation_masks_step7.roi.zip"
    assert _generate_output_path(base, ".csv", ".csv") == "/tmp/A01_s001_w1_z001_t001_segmentation_masks_step7.csv"


@pytest.mark.unit
def test_regionprops_materialization_spec_writes_roi_csv_json_with_intensity() -> None:
    fm = FileManager({"memory": MemoryStorageBackend()})

    labels = np.zeros((10, 10), dtype=np.int32)
    labels[1:5, 1:5] = 1  # area 16 (kept)
    labels[6:9, 6:9] = 2  # area 9 (filtered out by min_area=10)

    intensity = np.arange(100, dtype=np.float32).reshape(10, 10)

    spec = MaterializationSpec("regionprops", RegionPropsOptions(intensity_source=None))

    out = materialize(
        spec,
        data=[labels],
        path="/tmp/test_regionprops.roi.zip",
        filemanager=fm,
        backends=["memory"],
        backend_kwargs={},
        extra_inputs={"intensity": [intensity]},
    )

    assert out == "/tmp/test_regionprops.json"

    # JSON summary
    summary = json.loads(fm.load("/tmp/test_regionprops.json", "memory"))
    assert summary["total_regions"] == 1
    assert summary["total_slices"] == 1

    # CSV details should include intensity metrics
    csv_content = fm.load("/tmp/test_regionprops_details.csv", "memory")
    assert "mean_intensity" in csv_content

    # ROI archive stored as list of ROI objects (memory backend stores raw objects)
    rois = fm.load("/tmp/test_regionprops_rois.roi.zip", "memory")
    assert isinstance(rois, list)
    assert len(rois) == 1
    assert rois[0].metadata["label"] == 1
    assert rois[0].metadata["slice_index"] == 0
    assert "mean_intensity" in rois[0].metadata

