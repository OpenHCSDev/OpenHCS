#!/usr/bin/env python3
"""
Test runner for dual editor reset functionality tests.

Runs all dual editor tests with proper setup and teardown.
"""

import sys
import os
import pytest
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent.parent.parent
sys.path.insert(0, str(project_root))

def run_dual_editor_tests():
    """Run all dual editor tests."""
    test_dir = Path(__file__).parent
    
    test_files = [
        "test_dual_editor_reset_functionality.py",
        "test_dual_editor_widget_validation.py", 
        "test_dual_editor_window_integration.py"
    ]
    
    print("=" * 60)
    print("Running Dual Editor Reset Functionality Tests")
    print("=" * 60)
    
    # Set environment variables for testing
    os.environ['QT_QPA_PLATFORM'] = 'offscreen'  # Run tests headless
    
    # Run each test file
    for test_file in test_files:
        test_path = test_dir / test_file
        if test_path.exists():
            print(f"\n🧪 Running {test_file}...")
            result = pytest.main([
                str(test_path),
                "-v",
                "--tb=short",
                "--no-header",
                "-x"  # Stop on first failure
            ])
            
            if result != 0:
                print(f"❌ Tests failed in {test_file}")
                return result
            else:
                print(f"✅ All tests passed in {test_file}")
        else:
            print(f"⚠️  Test file not found: {test_file}")
    
    print("\n" + "=" * 60)
    print("🎉 All dual editor tests completed successfully!")
    print("=" * 60)
    return 0


def run_specific_test_category(category: str):
    """Run a specific category of tests."""
    test_dir = Path(__file__).parent
    
    category_map = {
        "reset": "test_dual_editor_reset_functionality.py",
        "widgets": "test_dual_editor_widget_validation.py",
        "integration": "test_dual_editor_window_integration.py"
    }
    
    if category not in category_map:
        print(f"Unknown test category: {category}")
        print(f"Available categories: {', '.join(category_map.keys())}")
        return 1
    
    test_file = category_map[category]
    test_path = test_dir / test_file
    
    if not test_path.exists():
        print(f"Test file not found: {test_file}")
        return 1
    
    print(f"Running {category} tests from {test_file}...")
    
    # Set environment variables for testing
    os.environ['QT_QPA_PLATFORM'] = 'offscreen'
    
    return pytest.main([
        str(test_path),
        "-v",
        "--tb=short"
    ])


def run_with_coverage():
    """Run tests with coverage reporting."""
    test_dir = Path(__file__).parent
    
    print("Running dual editor tests with coverage...")
    
    # Set environment variables for testing
    os.environ['QT_QPA_PLATFORM'] = 'offscreen'
    
    return pytest.main([
        str(test_dir),
        "-v",
        "--cov=openhcs.pyqt_gui.widgets",
        "--cov=openhcs.pyqt_gui.windows",
        "--cov-report=html:htmlcov/dual_editor",
        "--cov-report=term-missing"
    ])


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Run dual editor tests")
    parser.add_argument(
        "--category", 
        choices=["reset", "widgets", "integration"],
        help="Run specific test category"
    )
    parser.add_argument(
        "--coverage",
        action="store_true",
        help="Run with coverage reporting"
    )
    
    args = parser.parse_args()
    
    if args.coverage:
        exit_code = run_with_coverage()
    elif args.category:
        exit_code = run_specific_test_category(args.category)
    else:
        exit_code = run_dual_editor_tests()
    
    sys.exit(exit_code)
