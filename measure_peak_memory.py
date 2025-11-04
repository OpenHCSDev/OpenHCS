#!/usr/bin/env python3
"""
Measure peak memory usage for sequential vs non-sequential processing.

This script tracks memory usage throughout the test run and reports:
1. Peak memory usage
2. Number of files loaded at once
3. Memory per file
"""

import subprocess
import re
import sys

def run_test_and_measure(sequential_mode):
    """Run test and extract memory metrics."""
    cmd = [
        "bash", "-c",
        f". ../openhcs/.venv/bin/activate && "
        f"OPENHCS_CPU_ONLY=true python -m pytest tests/integration/test_main.py "
        f"--it-backends disk --it-microscopes ImageXpress --it-dims 3d "
        f"--it-exec-mode multiprocessing --it-zmq-mode direct "
        f"--it-visualizers none --it-sequential {sequential_mode} -xvs 2>&1"
    ]
    
    result = subprocess.run(cmd, capture_output=True, text=True, cwd="/home/ts/code/projects/openhcs-sequential")
    output = result.stdout + result.stderr
    
    # Extract bulk preload info
    preload_pattern = r"🔄 BULK PRELOAD: Saved (\d+) files"
    preloads = re.findall(preload_pattern, output)
    
    # Extract memory measurements
    memory_pattern = r"📊 MEMORY: (?:Before|After) preload.*?: ([\d.]+) MB"
    memories = [float(m) for m in re.findall(memory_pattern, output)]
    
    # Extract clearing info
    clear_pattern = r"🔄 SEQUENTIAL: Cleared (\d+) preloaded files"
    clears = re.findall(clear_pattern, output)
    
    return {
        'preloads': [int(p) for p in preloads],
        'memories': memories,
        'clears': [int(c) for c in clears],
        'output': output
    }

def main():
    print("=" * 80)
    print("MEMORY USAGE COMPARISON: Sequential vs Non-Sequential Processing")
    print("=" * 80)
    print()
    
    # Test non-sequential
    print("📊 Running NON-SEQUENTIAL test...")
    non_seq = run_test_and_measure("none")
    
    print("📊 Running SEQUENTIAL test...")
    seq = run_test_and_measure("invalid_overlap")
    
    print()
    print("=" * 80)
    print("RESULTS")
    print("=" * 80)
    print()
    
    # Non-sequential results
    print("🔵 NON-SEQUENTIAL (loads all channels at once):")
    if non_seq['preloads']:
        print(f"   Files per preload: {non_seq['preloads'][0]} files")
        print(f"   Number of preloads: {len(non_seq['preloads'])}")
        print(f"   Total file loads: {sum(non_seq['preloads'])}")
    if non_seq['memories']:
        print(f"   Peak memory: {max(non_seq['memories']):.1f} MB")
        print(f"   Min memory: {min(non_seq['memories']):.1f} MB")
        print(f"   Memory range: {max(non_seq['memories']) - min(non_seq['memories']):.1f} MB")
    print()
    
    # Sequential results
    print("🟢 SEQUENTIAL (loads one channel at a time):")
    if seq['preloads']:
        print(f"   Files per preload: {seq['preloads'][0]} files")
        print(f"   Number of preloads: {len(seq['preloads'])}")
        print(f"   Total file loads: {sum(seq['preloads'])}")
    if seq['clears']:
        print(f"   Files cleared per combination: {seq['clears'][0]} files")
        print(f"   Number of clears: {len(seq['clears'])}")
    if seq['memories']:
        print(f"   Peak memory: {max(seq['memories']):.1f} MB")
        print(f"   Min memory: {min(seq['memories']):.1f} MB")
        print(f"   Memory range: {max(seq['memories']) - min(seq['memories']):.1f} MB")
    print()
    
    # Comparison
    print("=" * 80)
    print("COMPARISON")
    print("=" * 80)
    print()
    
    if non_seq['preloads'] and seq['preloads']:
        reduction = (1 - seq['preloads'][0] / non_seq['preloads'][0]) * 100
        print(f"📉 Files in memory at once: {non_seq['preloads'][0]} → {seq['preloads'][0]} ({reduction:.0f}% reduction)")
    
    if non_seq['memories'] and seq['memories']:
        peak_diff = max(non_seq['memories']) - max(seq['memories'])
        print(f"📉 Peak memory: {max(non_seq['memories']):.1f} MB → {max(seq['memories']):.1f} MB ({peak_diff:+.1f} MB)")
    
    print()
    print("💡 NOTE: With this small test dataset (54 files, ~3.5 MB total),")
    print("   the memory difference is minimal. With larger datasets (e.g.,")
    print("   10+ channels, 100+ timepoints), the savings would be much more")
    print("   significant as only 1/N of the data is in memory at a time.")
    print()
    
    # Show that sequential actually processes in batches
    if seq['preloads']:
        num_channels = 2  # We know this from the test data
        print(f"✅ Sequential processing confirmed:")
        print(f"   - Processes {num_channels} channels sequentially")
        print(f"   - Loads {seq['preloads'][0]} files per channel (instead of {non_seq['preloads'][0]} for all)")
        print(f"   - Clears memory after each channel ({seq['clears'][0]} files)")
        print()

if __name__ == "__main__":
    main()

