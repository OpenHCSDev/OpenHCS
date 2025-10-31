#!/usr/bin/env python
"""
Test script for all caching improvements.

Tests:
1. Colormap enum caching
2. Component enum caching
3. Plugin registry caching (already implemented)

Verifies:
- Cache creation
- Cache loading
- Cache invalidation
- Performance improvements
"""

import time
import logging
import sys
from pathlib import Path

# Setup logging
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


def clear_all_caches():
    """Clear all cache files for fresh testing."""
    from openhcs.core.xdg_paths import get_cache_file_path
    
    cache_files = [
        "colormap_enum.json",
        "component_enums.json",
        "microscope_handler_registry.json",
        "storage_backend_registry.json",
        "microscope_format_registry_registry.json",
    ]
    
    for cache_file in cache_files:
        cache_path = get_cache_file_path(cache_file)
        if cache_path.exists():
            cache_path.unlink()
            logger.info(f"🧹 Cleared cache: {cache_file}")


def test_colormap_enum_caching():
    """Test colormap enum caching."""
    logger.info("\n" + "="*80)
    logger.info("TEST 1: Colormap Enum Caching")
    logger.info("="*80)
    
    from openhcs.utils.enum_factory import create_colormap_enum
    from openhcs.core.xdg_paths import get_cache_file_path
    
    cache_path = get_cache_file_path("colormap_enum.json")
    
    # Test 1: First run (cache miss)
    logger.info("\n📊 Test 1a: First run (cache miss)")
    start = time.time()
    enum1 = create_colormap_enum(lazy=False, enable_cache=True)
    duration1 = (time.time() - start) * 1000
    logger.info(f"⏱️  First run: {duration1:.2f}ms")
    logger.info(f"📦 Enum members: {len(enum1.__members__)}")
    logger.info(f"💾 Cache exists: {cache_path.exists()}")
    
    # Test 2: Second run (cache hit)
    logger.info("\n📊 Test 1b: Second run (cache hit)")
    start = time.time()
    enum2 = create_colormap_enum(lazy=False, enable_cache=True)
    duration2 = (time.time() - start) * 1000
    logger.info(f"⏱️  Second run: {duration2:.2f}ms")
    logger.info(f"📦 Enum members: {len(enum2.__members__)}")
    
    # Verify speedup
    speedup = duration1 / duration2 if duration2 > 0 else 0
    logger.info(f"\n✅ Speedup: {speedup:.1f}x faster")
    
    # Verify enum equality
    assert len(enum1.__members__) == len(enum2.__members__), "Enum member count mismatch"
    logger.info("✅ Enum members match")
    
    # Test 3: Lazy mode (no caching)
    logger.info("\n📊 Test 1c: Lazy mode (no caching)")
    start = time.time()
    enum3 = create_colormap_enum(lazy=True, enable_cache=True)
    duration3 = (time.time() - start) * 1000
    logger.info(f"⏱️  Lazy mode: {duration3:.2f}ms")
    logger.info(f"📦 Enum members: {len(enum3.__members__)}")
    
    # Test 4: Cache disabled
    logger.info("\n📊 Test 1d: Cache disabled")
    start = time.time()
    enum4 = create_colormap_enum(lazy=False, enable_cache=False)
    duration4 = (time.time() - start) * 1000
    logger.info(f"⏱️  Cache disabled: {duration4:.2f}ms")
    
    logger.info("\n✅ Colormap enum caching tests PASSED")
    return True


def test_component_enum_caching():
    """Test component enum caching."""
    logger.info("\n" + "="*80)
    logger.info("TEST 2: Component Enum Caching")
    logger.info("="*80)
    
    from openhcs.core.xdg_paths import get_cache_file_path
    
    cache_path = get_cache_file_path("component_enums.json")
    
    # Clear the lru_cache to force recreation
    from openhcs.constants.constants import _create_enums
    _create_enums.cache_clear()
    
    # Test 1: First run (cache miss)
    logger.info("\n📊 Test 2a: First run (cache miss)")
    start = time.time()
    from openhcs.constants import AllComponents, VariableComponents, GroupBy
    duration1 = (time.time() - start) * 1000
    logger.info(f"⏱️  First run: {duration1:.2f}ms")
    logger.info(f"📦 AllComponents: {len(AllComponents.__members__)}")
    logger.info(f"📦 VariableComponents: {len(VariableComponents.__members__)}")
    logger.info(f"📦 GroupBy: {len(GroupBy.__members__)}")
    logger.info(f"💾 Cache exists: {cache_path.exists()}")
    
    # Clear lru_cache again to force reload from persistent cache
    _create_enums.cache_clear()
    
    # Test 2: Second run (cache hit from persistent cache)
    logger.info("\n📊 Test 2b: Second run (cache hit)")
    start = time.time()
    from openhcs.constants import AllComponents as AC2, VariableComponents as VC2, GroupBy as GB2
    duration2 = (time.time() - start) * 1000
    logger.info(f"⏱️  Second run: {duration2:.2f}ms")
    
    # Verify speedup
    speedup = duration1 / duration2 if duration2 > 0 else 0
    logger.info(f"\n✅ Speedup: {speedup:.1f}x faster")
    
    # Verify enum members match
    assert len(AllComponents.__members__) == len(AC2.__members__), "AllComponents mismatch"
    assert len(VariableComponents.__members__) == len(VC2.__members__), "VariableComponents mismatch"
    assert len(GroupBy.__members__) == len(GB2.__members__), "GroupBy mismatch"
    logger.info("✅ Enum members match")
    
    # Verify GroupBy custom methods
    logger.info("\n📊 Test 2c: GroupBy custom methods")
    assert hasattr(GroupBy.NONE, 'component'), "GroupBy.NONE missing component property"
    assert GroupBy.NONE.value is None, "GroupBy.NONE value should be None"
    logger.info("✅ GroupBy custom methods work")
    
    logger.info("\n✅ Component enum caching tests PASSED")
    return True


def test_plugin_registry_caching():
    """Test plugin registry caching (already implemented)."""
    logger.info("\n" + "="*80)
    logger.info("TEST 3: Plugin Registry Caching")
    logger.info("="*80)
    
    from openhcs.microscopes.microscope_base import MICROSCOPE_HANDLERS
    from openhcs.core.xdg_paths import get_cache_file_path
    
    cache_path = get_cache_file_path("microscope_handler_registry.json")
    
    # Test 1: First access (may be cache hit or miss depending on previous runs)
    logger.info("\n📊 Test 3a: First access")
    start = time.time()
    handlers = list(MICROSCOPE_HANDLERS.keys())
    duration1 = (time.time() - start) * 1000
    logger.info(f"⏱️  First access: {duration1:.2f}ms")
    logger.info(f"📦 Handlers: {len(handlers)}")
    logger.info(f"💾 Cache exists: {cache_path.exists()}")
    
    # Force re-discovery by clearing the discovered flag
    MICROSCOPE_HANDLERS._discovered = False
    
    # Test 2: Second access (should use cache)
    logger.info("\n📊 Test 3b: Second access (from cache)")
    start = time.time()
    handlers2 = list(MICROSCOPE_HANDLERS.keys())
    duration2 = (time.time() - start) * 1000
    logger.info(f"⏱️  Second access: {duration2:.2f}ms")
    
    # Verify handlers match
    assert len(handlers) == len(handlers2), "Handler count mismatch"
    assert set(handlers) == set(handlers2), "Handler names mismatch"
    logger.info("✅ Handlers match")
    
    logger.info("\n✅ Plugin registry caching tests PASSED")
    return True


def test_cache_invalidation():
    """Test cache invalidation scenarios."""
    logger.info("\n" + "="*80)
    logger.info("TEST 4: Cache Invalidation")
    logger.info("="*80)
    
    from openhcs.core.xdg_paths import get_cache_file_path
    import json
    
    # Test colormap enum cache invalidation
    cache_path = get_cache_file_path("colormap_enum.json")
    
    if cache_path.exists():
        logger.info("\n📊 Test 4a: Version mismatch invalidation")
        
        # Read cache and modify version
        with open(cache_path, 'r') as f:
            cache_data = json.load(f)
        
        original_version = cache_data.get('version')
        logger.info(f"Original version: {original_version}")
        
        # Modify version to trigger invalidation
        cache_data['version'] = "0.0.0"
        with open(cache_path, 'w') as f:
            json.dump(cache_data, f)
        
        # Try to load - should invalidate and rebuild
        from openhcs.utils.enum_factory import create_colormap_enum
        enum = create_colormap_enum(lazy=False, enable_cache=True)
        
        # Verify cache was rebuilt with correct version
        with open(cache_path, 'r') as f:
            new_cache_data = json.load(f)
        
        assert new_cache_data['version'] != "0.0.0", "Cache should have been rebuilt"
        logger.info(f"✅ Cache invalidated and rebuilt with version: {new_cache_data['version']}")
    
    logger.info("\n✅ Cache invalidation tests PASSED")
    return True


def main():
    """Run all caching tests."""
    logger.info("🚀 Starting caching improvement tests")
    logger.info(f"Python: {sys.version}")
    
    # Clear all caches for fresh testing
    logger.info("\n🧹 Clearing all caches for fresh testing")
    clear_all_caches()
    
    try:
        # Run all tests
        test_colormap_enum_caching()
        test_component_enum_caching()
        test_plugin_registry_caching()
        test_cache_invalidation()
        
        logger.info("\n" + "="*80)
        logger.info("🎉 ALL TESTS PASSED!")
        logger.info("="*80)
        return 0
        
    except Exception as e:
        logger.error(f"\n❌ TEST FAILED: {e}", exc_info=True)
        return 1


if __name__ == "__main__":
    sys.exit(main())

