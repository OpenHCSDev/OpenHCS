#!/usr/bin/env python3
"""Test microscope handler automatic discovery."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

def test_discovery():
    """Test automatic discovery works."""
    from openhcs.microscopes import get_all_handler_types, is_handler_available

    handler_types = get_all_handler_types()
    print(f"Found handlers: {handler_types}")

    for handler_type in handler_types:
        available = is_handler_available(handler_type)
        print(f"{handler_type}: {'✅' if available else '❌'}")

    return len(handler_types) > 0

if __name__ == "__main__":
    success = test_discovery()
    print("✅ Discovery works!" if success else "❌ Discovery failed!")
    sys.exit(0 if success else 1)
