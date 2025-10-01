#!/usr/bin/env python3
"""
Test script to verify dual-context configuration system works correctly.

This tests the core behavior of config_context() nesting and overlay merging
to ensure the implementation matches the architectural plan.
"""

from openhcs.core.config import GlobalPipelineConfig, PipelineConfig, StepWellFilterConfig, WellFilterMode
from openhcs.core.lazy_config import LazyPathPlanningConfig, ensure_global_config_context
from openhcs.core.context.contextvars_context import config_context, get_current_temp_global
from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService


def test_basic_context_nesting():
    """Test that config_context() properly nests and merges contexts."""
    print("\n" + "="*80)
    print("TEST 1: Basic Context Nesting")
    print("="*80)
    
    # Setup: Global config with num_workers=1
    global_config = GlobalPipelineConfig(num_workers=1)
    ensure_global_config_context(GlobalPipelineConfig, global_config)
    
    print(f"✓ Global config: num_workers={global_config.num_workers}")
    
    # Test: No context - should see global
    current = get_current_temp_global()
    print(f"✓ No context: current_temp_global is None = {current is None}")
    
    # Test: Single context - pipeline with num_workers=4
    pipeline_config = PipelineConfig(num_workers=4)
    with config_context(pipeline_config):
        current = get_current_temp_global()
        print(f"✓ Pipeline context: num_workers={current.num_workers} (expected 4)")
        assert current.num_workers == 4, f"Expected 4, got {current.num_workers}"
    
    # Test: Context exits properly
    current = get_current_temp_global()
    print(f"✓ After exit: current_temp_global is None = {current is None}")
    
    print("✅ TEST 1 PASSED\n")


def test_nested_context_merging():
    """Test that nested contexts merge properly (parent + overlay)."""
    print("="*80)
    print("TEST 2: Nested Context Merging (Parent + Overlay)")
    print("="*80)
    
    # Setup: Global config with num_workers=1
    global_config = GlobalPipelineConfig(num_workers=1)
    ensure_global_config_context(GlobalPipelineConfig, global_config)
    
    print(f"✓ Global config: num_workers={global_config.num_workers}")
    
    # Test: Nested contexts - pipeline (num_workers=4) + overlay (num_workers=None)
    pipeline_config = PipelineConfig(num_workers=4)
    overlay = PipelineConfig(num_workers=None)  # None should be filtered
    
    with config_context(pipeline_config):
        print(f"✓ Pipeline context: num_workers={get_current_temp_global().num_workers}")
        
        with config_context(overlay):
            current = get_current_temp_global()
            print(f"✓ Overlay context (None filtered): num_workers={current.num_workers} (expected 4)")
            # None values are filtered, so should still see pipeline's value
            assert current.num_workers == 4, f"Expected 4 (from pipeline), got {current.num_workers}"
    
    print("✅ TEST 2 PASSED\n")


def test_overlay_with_concrete_value():
    """Test that overlay with concrete value overrides parent."""
    print("="*80)
    print("TEST 3: Overlay with Concrete Value Overrides Parent")
    print("="*80)
    
    # Setup: Global config with num_workers=1
    global_config = GlobalPipelineConfig(num_workers=1)
    ensure_global_config_context(GlobalPipelineConfig, global_config)
    
    print(f"✓ Global config: num_workers={global_config.num_workers}")
    
    # Test: Nested contexts - pipeline (num_workers=4) + overlay (num_workers=8)
    pipeline_config = PipelineConfig(num_workers=4)
    overlay = PipelineConfig(num_workers=8)  # Concrete value should override
    
    with config_context(pipeline_config):
        print(f"✓ Pipeline context: num_workers={get_current_temp_global().num_workers}")
        
        with config_context(overlay):
            current = get_current_temp_global()
            print(f"✓ Overlay context (concrete value): num_workers={current.num_workers} (expected 8)")
            # Concrete value should override pipeline's value
            assert current.num_workers == 8, f"Expected 8 (from overlay), got {current.num_workers}"
    
    print("✅ TEST 3 PASSED\n")


def test_placeholder_resolution_with_context():
    """Test that placeholder resolution uses the merged context correctly."""
    print("="*80)
    print("TEST 4: Placeholder Resolution with Context Stack")
    print("="*80)

    # Setup: Global config with num_workers=1
    global_config = GlobalPipelineConfig(num_workers=1)
    ensure_global_config_context(GlobalPipelineConfig, global_config)

    print(f"✓ Global config: num_workers={global_config.num_workers}")

    # Test: Placeholder resolution without context
    # PipelineConfig is the lazy version of GlobalPipelineConfig
    placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        PipelineConfig, 'num_workers', 'Default'
    )
    print(f"✓ No context: placeholder='{placeholder}' (expected 'Default: 1')")
    assert placeholder == "Default: 1", f"Expected 'Default: 1', got '{placeholder}'"

    # Test: Placeholder resolution with pipeline context
    pipeline_config = PipelineConfig(num_workers=4)
    with config_context(pipeline_config):
        placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
            PipelineConfig, 'num_workers', 'Pipeline default'
        )
        print(f"✓ Pipeline context: placeholder='{placeholder}' (expected 'Pipeline default: 4')")
        assert placeholder == "Pipeline default: 4", f"Expected 'Pipeline default: 4', got '{placeholder}'"

    print("✅ TEST 4 PASSED\n")


def test_reset_scenario_circular_bug():
    """Test the specific scenario that was broken: Pipeline Config Editor reset."""
    print("="*80)
    print("TEST 5: Reset Scenario (Circular Context Bug Fix)")
    print("="*80)
    
    # Setup: Global config with num_workers=1
    global_config = GlobalPipelineConfig(num_workers=1)
    ensure_global_config_context(GlobalPipelineConfig, global_config)
    
    print(f"✓ Global config: num_workers={global_config.num_workers}")
    
    # Simulate: User has edited pipeline config to num_workers=4
    current_config = PipelineConfig(num_workers=4)
    print(f"✓ Current pipeline config (saved): num_workers={current_config.num_workers}")
    
    # BROKEN BEHAVIOR (before fix): context_obj=current_config (circular reference)
    print("\n--- BROKEN BEHAVIOR (before fix) ---")
    with config_context(current_config):  # Circular: using itself as parent
        # User resets num_workers to None
        overlay = PipelineConfig(num_workers=None)

        with config_context(overlay):
            # BUG: Placeholder shows 4 (from current_config) instead of 1 (from global)
            placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
                PipelineConfig, 'num_workers', 'Pipeline default'
            )
            print(f"✗ BROKEN: placeholder='{placeholder}' (shows 4 from circular context)")
            # This is the bug - it shows the current form's value, not the global default

    # FIXED BEHAVIOR (after fix): context_obj=None (no parent, just overlay)
    print("\n--- FIXED BEHAVIOR (after fix) ---")
    # No parent context - just overlay on top of thread-local global
    overlay = PipelineConfig(num_workers=None)

    with config_context(overlay):
        # FIXED: Placeholder shows 1 (from global) because no circular reference
        placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
            PipelineConfig, 'num_workers', 'Pipeline default'
        )
        print(f"✓ FIXED: placeholder='{placeholder}' (expected 'Pipeline default: 1')")
        assert placeholder == "Pipeline default: 1", f"Expected 'Pipeline default: 1', got '{placeholder}'"
    
    print("✅ TEST 5 PASSED\n")


def test_live_placeholder_updates():
    """Test that placeholders update based on current form state (overlay)."""
    print("="*80)
    print("TEST 6: Live Placeholder Updates (Overlay Simulation)")
    print("="*80)
    
    # Setup: Global config with num_workers=1
    global_config = GlobalPipelineConfig(num_workers=1)
    ensure_global_config_context(GlobalPipelineConfig, global_config)
    
    print(f"✓ Global config: num_workers={global_config.num_workers}")
    
    # Simulate: User is editing a field, but hasn't saved yet
    # Form has: num_workers=None (user hasn't set it)
    # User types "8" in another field, we want to see how that affects placeholders
    
    # Initial state: num_workers=None
    overlay = PipelineConfig(num_workers=None)
    with config_context(overlay):
        placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
            PipelineConfig, 'num_workers', 'Pipeline default'
        )
        print(f"✓ Initial overlay (None): placeholder='{placeholder}' (expected 'Pipeline default: 1')")
        assert placeholder == "Pipeline default: 1"

    # User types "8" in num_workers field (unsaved)
    overlay = PipelineConfig(num_workers=8)
    with config_context(overlay):
        placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
            PipelineConfig, 'num_workers', 'Pipeline default'
        )
        print(f"✓ Updated overlay (8): placeholder='{placeholder}' (expected 'Pipeline default: 8')")
        assert placeholder == "Pipeline default: 8"
    
    print("✅ TEST 6 PASSED\n")


def test_dict_overlay_conversion():
    """Test that dict overlay is properly converted to dataclass instance."""
    print("="*80)
    print("TEST 7: Dict Overlay Conversion (Real-World Scenario)")
    print("="*80)

    # Setup: Global config with num_workers=1
    global_config = GlobalPipelineConfig(num_workers=1)
    ensure_global_config_context(GlobalPipelineConfig, global_config)

    print(f"✓ Global config: num_workers={global_config.num_workers}")

    # Simulate: Form opened with current_config having num_workers=4
    # User resets num_workers to None
    # get_current_values() returns a dict with num_workers=None

    # This is what get_current_values() returns - a dict
    overlay_dict = {'num_workers': None, 'test_str_field': 'test'}

    # Convert dict to dataclass instance (filtering None values)
    filtered_overlay = {k: v for k, v in overlay_dict.items() if v is not None}
    overlay_instance = PipelineConfig(**filtered_overlay)

    print(f"✓ Overlay dict: {overlay_dict}")
    print(f"✓ Filtered overlay: {filtered_overlay}")
    print(f"✓ Overlay instance: num_workers={overlay_instance.num_workers}")

    # Test: Placeholder resolution with dict overlay converted to instance
    with config_context(overlay_instance):
        placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
            PipelineConfig, 'num_workers', 'Pipeline default'
        )
        print(f"✓ Placeholder with filtered overlay: '{placeholder}' (expected 'Pipeline default: 1')")
        # None was filtered out, so should see global default
        assert placeholder == "Pipeline default: 1", f"Expected 'Pipeline default: 1', got '{placeholder}'"

    print("✅ TEST 7 PASSED\n")


def test_step_editor_none_inheritance():
    """Test 8: Step Editor with None values inheriting from pipeline → global."""
    print("="*80)
    print("TEST 8: Step Editor None Inheritance (Global → Pipeline → Step)")
    print("="*80)

    # Set up thread-local global with EXCLUDE
    global_config = GlobalPipelineConfig(
        num_workers=1,
        step_well_filter_config=StepWellFilterConfig(well_filter_mode=WellFilterMode.EXCLUDE)
    )
    ensure_global_config_context(GlobalPipelineConfig, global_config)
    print(f"✓ Global config: well_filter_mode={global_config.step_well_filter_config.well_filter_mode}")

    # Create pipeline config with None (inherits from global)
    pipeline_config = PipelineConfig(step_well_filter_config=StepWellFilterConfig(well_filter_mode=None))
    print(f"✓ Pipeline config: well_filter_mode=None (inherits from global)")

    # Simulate step form state with None values (from get_current_values())
    # This is what the Step Editor would have when field is not set
    overlay_dict = {
        'well_filter_mode': None,  # User hasn't changed this field - should inherit
    }
    print(f"✓ Step overlay dict: {overlay_dict}")

    # CRITICAL TEST: Do NOT filter None values before creating overlay instance!
    # OLD (BROKEN): filtered = {k: v for k, v in overlay_dict.items() if v is not None}
    #               overlay = StepWellFilterConfig(**filtered)  # Uses class default INCLUDE!
    # NEW (CORRECT): overlay = StepWellFilterConfig(**overlay_dict)  # Passes None to config_context()

    print("\n--- BROKEN BEHAVIOR (filtering None before creating instance) ---")
    filtered_overlay = {k: v for k, v in overlay_dict.items() if v is not None}
    broken_overlay = StepWellFilterConfig(**filtered_overlay) if filtered_overlay else StepWellFilterConfig()
    print(f"✗ BROKEN overlay instance: well_filter_mode={broken_overlay.well_filter_mode} (class default!)")

    with config_context(pipeline_config):
        with config_context(broken_overlay):
            broken_placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
                StepWellFilterConfig, 'well_filter_mode', 'Pipeline default'
            )
            print(f"✗ BROKEN placeholder: '{broken_placeholder}' (shows INCLUDE from class default)")

    print("\n--- FIXED BEHAVIOR (passing None to config_context) ---")
    fixed_overlay = StepWellFilterConfig(**overlay_dict)
    print(f"✓ FIXED overlay instance: well_filter_mode={fixed_overlay.well_filter_mode} (None - will inherit)")

    # Build context stack: global → pipeline → overlay
    from openhcs.core.context.contextvars_context import get_current_temp_global, get_base_global_config

    print("\n🔍 DEBUG: Context state before nesting:")
    print(f"  - Active context: {get_current_temp_global()}")
    print(f"  - Base global: {get_base_global_config().step_well_filter_config.well_filter_mode if get_base_global_config() else None}")

    with config_context(pipeline_config):
        print(f"\n🔍 DEBUG: After pipeline_config context:")
        current = get_current_temp_global()
        print(f"  - Active context: {current is not None}")
        if current and hasattr(current, 'step_well_filter_config'):
            print(f"  - Context well_filter_mode: {current.step_well_filter_config.well_filter_mode if current.step_well_filter_config else None}")

        with config_context(fixed_overlay):
            print(f"\n🔍 DEBUG: After step overlay context:")
            current = get_current_temp_global()
            print(f"  - Active context: {current is not None}")
            if current and hasattr(current, 'step_well_filter_config'):
                print(f"  - Context well_filter_mode: {current.step_well_filter_config.well_filter_mode if current.step_well_filter_config else None}")

            # Resolve placeholder - should show EXCLUDE from global, not INCLUDE from class default
            fixed_placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
                StepWellFilterConfig, 'well_filter_mode', 'Pipeline default'
            )
            print(f"\n✓ FIXED placeholder: '{fixed_placeholder}' (expected 'Pipeline default: EXCLUDE')")
            assert fixed_placeholder == 'Pipeline default: EXCLUDE', \
                f"Expected 'Pipeline default: EXCLUDE', got '{fixed_placeholder}'"

    print("✅ TEST 8 PASSED\n")


if __name__ == "__main__":
    print("\n" + "🔥"*40)
    print("DUAL-CONTEXT CONFIGURATION SYSTEM TESTS")
    print("🔥"*40)

    try:
        test_basic_context_nesting()
        test_nested_context_merging()
        test_overlay_with_concrete_value()
        test_placeholder_resolution_with_context()
        test_reset_scenario_circular_bug()
        test_live_placeholder_updates()
        test_dict_overlay_conversion()
        test_step_editor_none_inheritance()

        print("="*80)
        print("🎉 ALL TESTS PASSED! 🎉")
        print("="*80)
        print("\nThe dual-context configuration system is working correctly:")
        print("✓ Context nesting works properly")
        print("✓ None values are filtered during merge")
        print("✓ Concrete values override parent context")
        print("✓ Placeholder resolution uses merged context")
        print("✓ Reset scenario shows global defaults (circular bug fixed)")
        print("✓ Live placeholder updates reflect current form state")
        print("✓ Dict overlay properly converted to dataclass instance")
        print()

    except AssertionError as e:
        print(f"\n❌ TEST FAILED: {e}\n")
        raise
    except Exception as e:
        print(f"\n❌ UNEXPECTED ERROR: {e}\n")
        raise

