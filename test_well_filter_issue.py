"""
Test to reproduce well_filter_mode resolution issue.
"""
import sys
sys.path.insert(0, '/home/ts/code/projects/openhcs-sequential')

from openhcs.core.config import GlobalPipelineConfig, WellFilterConfig, WellFilterMode
from openhcs.config_framework import config_context
import logging

logging.basicConfig(level=logging.DEBUG, format='%(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

def test_well_filter_mode_resolution():
    """Test that well_filter_mode set to EXCLUDE in GlobalPipelineConfig is correctly resolved."""

    print("\n" + "="*80)
    print("TEST: well_filter_mode resolution")
    print("="*80)

    # Create GlobalPipelineConfig with well_filter_mode set to EXCLUDE
    global_config = GlobalPipelineConfig(
        well_filter_config=WellFilterConfig(well_filter_mode=WellFilterMode.EXCLUDE)
    )

    print(f"\n1. GlobalPipelineConfig.well_filter_config.well_filter_mode = {global_config.well_filter_config.well_filter_mode}")
    print(f"   Expected: {WellFilterMode.EXCLUDE}")
    assert global_config.well_filter_config.well_filter_mode == WellFilterMode.EXCLUDE, "GlobalPipelineConfig should have EXCLUDE"

    # Now create a PipelineConfig (lazy version) and resolve it in context
    from openhcs.core.config import PipelineConfig

    pipeline_config = PipelineConfig()

    print(f"\n2. PipelineConfig (before context): {type(pipeline_config)}")
    print(f"   pipeline_config.well_filter_config = {pipeline_config.well_filter_config}")

    # Resolve in context
    with config_context(global_config):
        print(f"\n3. Inside context with GlobalPipelineConfig...")
        resolved_well_filter_config = pipeline_config.well_filter_config
        print(f"   pipeline_config.well_filter_config = {resolved_well_filter_config}")
        print(f"   pipeline_config.well_filter_config.well_filter_mode = {resolved_well_filter_config.well_filter_mode}")
        print(f"   Expected: {WellFilterMode.EXCLUDE}")

        if resolved_well_filter_config.well_filter_mode != WellFilterMode.EXCLUDE:
            print(f"\n❌ BUG: Got {resolved_well_filter_config.well_filter_mode} instead of {WellFilterMode.EXCLUDE}")
            return False
        else:
            print(f"\n✓ PASS: Correctly resolved to {WellFilterMode.EXCLUDE}")
            return True

if __name__ == "__main__":
    success = test_well_filter_mode_resolution()
    sys.exit(0 if success else 1)
