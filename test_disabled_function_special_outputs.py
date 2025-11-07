"""
Test to verify that disabled functions don't get their special outputs compiled.
"""
import pytest
from openhcs.core.pipeline.path_planner import normalize_pattern, extract_attributes
from openhcs.core.pipeline.function_contracts import special_outputs


# Create test functions with special outputs
@special_outputs(("result1", None))
def func_enabled():
    """A function that should be enabled."""
    return "result"


@special_outputs(("result2", None))
def func_disabled():
    """A function that should be disabled."""
    return "result"


def test_normalize_pattern_skips_disabled_single_function():
    """Test that normalize_pattern skips disabled single functions."""
    # Enabled function
    pattern_enabled = (func_enabled, {"enabled": True})
    functions = list(normalize_pattern(pattern_enabled))
    assert len(functions) == 1
    assert functions[0][0] == func_enabled
    
    # Disabled function
    pattern_disabled = (func_disabled, {"enabled": False})
    functions = list(normalize_pattern(pattern_disabled))
    assert len(functions) == 0, "Disabled function should be filtered out"


def test_normalize_pattern_skips_disabled_in_list():
    """Test that normalize_pattern skips disabled functions in lists."""
    pattern = [
        func_enabled,
        (func_disabled, {"enabled": False}),
        func_enabled,
    ]
    functions = list(normalize_pattern(pattern))
    assert len(functions) == 2, "Should only have 2 enabled functions"
    assert functions[0][0] == func_enabled
    assert functions[1][0] == func_enabled


def test_normalize_pattern_skips_disabled_in_dict():
    """Test that normalize_pattern skips disabled functions in dict patterns."""
    pattern = {
        "channel1": func_enabled,
        "channel2": (func_disabled, {"enabled": False}),
        "channel3": func_enabled,
    }
    functions = list(normalize_pattern(pattern))
    assert len(functions) == 2, "Should only have 2 enabled functions"
    
    # Check that channel2 is not in the results
    channels = [(func, ch, pos) for func, ch, pos in functions]
    channel_keys = [ch for _, ch, _ in channels]
    assert "channel2" not in channel_keys, "Disabled channel should be skipped"


def test_extract_attributes_excludes_disabled():
    """Test that extract_attributes only includes attributes from enabled functions."""
    pattern = {
        "channel1": func_enabled,
        "channel2": (func_disabled, {"enabled": False}),
    }
    attrs = extract_attributes(pattern)
    
    # Should only have result1 (from func_enabled), not result2 (from disabled func_disabled)
    assert "result1" in attrs['outputs']
    assert "result2" not in attrs['outputs'], "Disabled function's outputs should not be extracted"


def test_extract_attributes_with_mixed_pattern():
    """Test extract_attributes with a complex mixed pattern."""
    pattern = [
        func_enabled,
        (func_disabled, {"enabled": False}),
        (func_enabled, {}),  # Enabled by default
    ]
    attrs = extract_attributes(pattern)
    
    # Should have result1 twice (both enabled), but not result2
    assert "result1" in attrs['outputs']
    assert "result2" not in attrs['outputs']


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
