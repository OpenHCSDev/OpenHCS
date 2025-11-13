import numpy as np
from skimage import measure

from openhcs.core.roi import extract_rois_from_labeled_mask, PolygonShape


def test_extract_rois_from_labeled_mask_matches_full_image_contour():
    """Ensure cropped contour extraction matches full-image contours for circular masks."""
    size = 64
    labeled_mask = np.zeros((size, size), dtype=np.int32)

    # Create a filled circle that sits comfortably inside the image
    cy, cx, radius = 32, 24, 10
    y, x = np.ogrid[:size, :size]
    circle = ((y - cy) ** 2 + (x - cx) ** 2) <= radius ** 2
    labeled_mask[circle] = 1

    rois = extract_rois_from_labeled_mask(
        labeled_mask,
        min_area=0,
        extract_contours=True,
    )

    assert len(rois) == 1
    polygon = rois[0].shapes[0]
    assert isinstance(polygon, PolygonShape)

    expected_contours = measure.find_contours(labeled_mask == 1, level=0.5)
    assert len(expected_contours) == 1
    expected = expected_contours[0]

    expected_pts = {tuple(np.round(pt, 3)) for pt in expected}
    actual_pts = {tuple(np.round(pt, 3)) for pt in polygon.coordinates}

    assert actual_pts == expected_pts
