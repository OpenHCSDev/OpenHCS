#!/usr/bin/env python3
"""
Absorb CellProfiler library into OpenHCS (one-time).

Usage:
    python -m benchmark.converter.absorb [--model <model>]
    
This absorbs the entire CellProfiler library into benchmark/cellprofiler_library/.
After absorption, .cppipe conversion is instant (no LLM needed).
"""

import argparse
import logging
import sys

from .llm_converter import LLMFunctionConverter
from .library_absorber import LibraryAbsorber

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s"
)
logger = logging.getLogger(__name__)


def main():
    parser = argparse.ArgumentParser(
        description="Absorb CellProfiler library into OpenHCS (one-time)"
    )
    parser.add_argument(
        "--model",
        type=str,
        default=None,
        help="LLM model (e.g. 'qwen2.5-coder:7b' for Ollama, 'minimax/minimax-m2.1' for OpenRouter)"
    )
    parser.add_argument(
        "--skip-existing",
        action="store_true",
        default=True,
        help="Skip modules already absorbed (default: True)"
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Re-absorb all modules even if they exist"
    )
    
    args = parser.parse_args()
    
    # Initialize LLM converter
    converter = LLMFunctionConverter(model=args.model)
    
    # Test connection
    success, message = converter.test_connection()
    if not success:
        logger.error(f"LLM connection failed: {message}")
        sys.exit(1)
    logger.info(message)
    
    # Absorb library
    absorber = LibraryAbsorber(llm_converter=converter)
    
    logger.info("=" * 60)
    logger.info("ABSORBING CELLPROFILER LIBRARY")
    logger.info("This is a one-time operation.")
    logger.info("=" * 60)
    
    result = absorber.absorb_all(skip_existing=not args.force)
    
    # Report
    logger.info("=" * 60)
    logger.info(f"ABSORPTION COMPLETE")
    logger.info(f"  Absorbed: {result.success_count} modules")
    logger.info(f"  Failed: {result.failure_count} modules")
    
    if result.failed:
        logger.info("Failed modules:")
        for name, error in result.failed:
            logger.info(f"  - {name}: {error}")
    
    logger.info("=" * 60)
    logger.info("Run .cppipe conversion:")
    logger.info("  python -m benchmark.converter.convert <file.cppipe>")
    logger.info("=" * 60)


if __name__ == "__main__":
    main()

