#!/usr/bin/env python3
"""
CellProfiler → OpenHCS Converter

Converts .cppipe files to OpenHCS pipelines using absorbed library.
Requires library to be absorbed first via:
    python -m benchmark.converter.absorb

Usage:
    python -m benchmark.converter.convert <cppipe_file>

If a module is not absorbed, conversion FAILS. No fallback. Absorb first.
"""

import argparse
import logging
import sys
from pathlib import Path

from .parser import CPPipeParser
from .pipeline_generator import PipelineGenerator

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s"
)
logger = logging.getLogger(__name__)


def main():
    parser = argparse.ArgumentParser(
        description="Convert .cppipe to OpenHCS pipeline using absorbed library"
    )
    parser.add_argument(
        "cppipe_file",
        type=Path,
        help="Path to .cppipe file"
    )
    parser.add_argument(
        "--output", "-o",
        type=Path,
        default=None,
        help="Output path (default: <name>_openhcs.py)"
    )

    args = parser.parse_args()

    # Validate input
    if not args.cppipe_file.exists():
        logger.error(f"File not found: {args.cppipe_file}")
        sys.exit(1)

    # Default output path
    if args.output is None:
        args.output = args.cppipe_file.parent / f"{args.cppipe_file.stem}_openhcs.py"

    logger.info(f"Converting: {args.cppipe_file}")

    # Parse .cppipe
    cppipe_parser = CPPipeParser()
    modules = cppipe_parser.parse(args.cppipe_file)
    logger.info(f"Parsed {len(modules)} modules")

    for m in modules:
        logger.info(f"  - {m.name}")

    # Initialize generator (loads absorbed library)
    generator = PipelineGenerator()

    # Check all modules are absorbed
    missing = [m for m in modules if not generator.has_module(m.name)]
    if missing:
        logger.error("Modules not absorbed:")
        for m in missing:
            logger.error(f"  - {m.name}")
        logger.error("")
        logger.error("Run: python -m benchmark.converter.absorb")
        sys.exit(1)

    # Generate pipeline from registry (instant, no LLM)
    pipeline = generator.generate_from_registry(
        pipeline_name=args.cppipe_file.stem,
        source_cppipe=args.cppipe_file,
        modules=modules,
    )

    # Save
    pipeline.save(args.output)

    # Summary
    logger.info("=" * 50)
    logger.info(f"Pipeline: {pipeline.name}")
    logger.info(f"Modules: {len(pipeline.converted_modules)}")
    logger.info(f"Output: {args.output}")
    logger.info("=" * 50)


if __name__ == "__main__":
    main()

