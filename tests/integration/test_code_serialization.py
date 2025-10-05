#!/usr/bin/env python3
"""
Standalone test runner for code serialization using pytest.

This script runs the code serialization test using pytest infrastructure.

Usage:
    python tests/integration/test_code_serialization.py
"""

import sys
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent.parent
sys.path.insert(0, str(project_root))

import pytest


def main():
    """Run the code serialization test using pytest."""
    print("=" * 80)
    print("CODE SERIALIZATION TEST")
    print("=" * 80)
    print()

    # Run pytest with the code_serialization test
    # Use -v for verbose, -s to show print statements
    exit_code = pytest.main([
        "tests/integration/test_main.py::test_code_serialization",
        "-v",
        "-s",
        "--tb=short",
        "-k", "code_serialization"
    ])

    print()
    if exit_code == 0:
        print("=" * 80)
        print("✅ CODE SERIALIZATION TEST PASSED!")
        print("=" * 80)
    else:
        print("=" * 80)
        print("❌ CODE SERIALIZATION TEST FAILED!")
        print("=" * 80)

    return exit_code


if __name__ == "__main__":
    sys.exit(main())

