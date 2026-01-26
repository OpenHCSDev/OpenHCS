#!/usr/bin/env python3
"""
Development installation script for openhcs.

This script installs openhcs in development mode with local external modules
from external/ directory (git submodules).

Usage:
    python scripts/dev_install.py [--extras EXTRAS]

Options:
    --extras EXTRAS    Comma-separated list of extras to install (e.g., "dev,gui,gpu")
                       Default: "dev,gui"
"""

import argparse
import subprocess
import sys


def run_command(cmd, check=True):
    """Run a shell command and print output."""
    print(f"\n{'='*60}")
    print(f"Running: {' '.join(cmd)}")
    print(f"{'='*60}")
    result = subprocess.run(cmd, check=check)
    return result


def main():
    parser = argparse.ArgumentParser(
        description="Install openhcs in development mode"
    )
    parser.add_argument(
        "--extras",
        default="dev,gui",
        help="Comma-separated list of extras to install (default: dev,gui)"
    )
    args = parser.parse_args()

    # Install openhcs in editable mode with extras
    extras_spec = f"[{args.extras}]" if args.extras else ""
    cmd = [sys.executable, "-m", "pip", "install", "-e", f".{extras_spec}"]
    run_command(cmd)

    # Install local external modules as editable installs
    external_modules = [
        "external/ObjectState",
        "external/python-introspect",
        "external/metaclass-registry",
        "external/arraybridge",
        "external/PolyStore",
        "external/pyqt-reactive",
        "external/zmqruntime",
        "external/pycodify",
    ]

    for module in external_modules:
        cmd = [sys.executable, "-m", "pip", "install", "-e", module]
        run_command(cmd)

    print("\n" + "="*60)
    print("Development installation complete!")
    print("="*60)
    print("\nYou can now run openhcs with:")
    print("  openhcs")
    print("\nOr run tests with:")
    print("  pytest")


if __name__ == "__main__":
    main()
