#!/usr/bin/env python3
"""Run OpenHCS with performance logging enabled.

This script runs the OpenHCS GUI with detailed performance monitoring.
All timing information is logged to:
- Console (with ⏱️ prefix)
- ~/.local/share/openhcs/logs/performance.log

Usage:
    python run_with_performance_logging.py

The performance log will show:
- Form initialization time
- Placeholder refresh time
- Widget value retrieval time
- Individual placeholder resolution time per field
- Cache hit/miss statistics

After closing the application, check the performance log for detailed timing data.
"""

import sys
from pathlib import Path

# Add openhcs to path
sys.path.insert(0, str(Path(__file__).parent))

def main():
    """Run OpenHCS with performance logging."""
    print("=" * 60)
    print("OPENHCS PERFORMANCE MONITORING")
    print("=" * 60)
    print()
    print("Performance metrics will be logged to:")
    print("  - Console (with ⏱️ prefix)")
    print("  - ~/.local/share/openhcs/logs/performance.log")
    print()
    print("Monitored operations:")
    print("  - Form initialization")
    print("  - Placeholder refresh")
    print("  - Widget value retrieval")
    print("  - Individual placeholder resolution")
    print()
    print("Try these actions to see performance metrics:")
    print("  1. Open the config window (File → Configuration)")
    print("  2. Edit some fields and watch placeholder updates")
    print("  3. Reset fields to None")
    print("  4. Save the configuration")
    print()
    print("=" * 60)
    print()
    
    # Enable performance logging
    from openhcs.utils.performance_monitor import enable_performance_logging, report_all_monitors
    enable_performance_logging()

    # Import and run the GUI
    from openhcs.pyqt_gui.launch import main as gui_main

    try:
        exit_code = gui_main()
    except SystemExit as e:
        exit_code = e.code if hasattr(e, 'code') else 0
    finally:
        print()
        print("=" * 60)
        print("PERFORMANCE SUMMARY")
        print("=" * 60)
        
        # Report accumulated statistics
        report_all_monitors()
        
        # Report cache statistics
        from openhcs.ui.shared.parameter_form_cache import get_placeholder_resolution_cache
        cache = get_placeholder_resolution_cache()
        stats = cache.get_stats()
        
        print()
        print("Placeholder Resolution Cache Statistics:")
        print(f"  Total requests: {stats['total_requests']}")
        print(f"  Cache hits: {stats['hits']}")
        print(f"  Cache misses: {stats['misses']}")
        print(f"  Hit rate: {stats['hit_rate_percent']:.1f}%")
        print(f"  Cache size: {stats['cache_size']} entries")
        print()
        print("=" * 60)
        print()
        print("Full performance log saved to:")
        print("  ~/.local/share/openhcs/logs/performance.log")
        print("=" * 60)


if __name__ == '__main__':
    main()

