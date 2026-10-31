"""Run the packaged local tests from any working directory.

Usage: python -B scripts/run_tests.py [--pattern test_*.py] [--quiet]
These tests do not constitute an end-to-end proof system or security estimate.
"""
import argparse
from pathlib import Path
import sys
import unittest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pattern', default='test_*.py')
    parser.add_argument('--quiet', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    sys.path.insert(0, str(root))
    suite = unittest.defaultTestLoader.discover(
        str(root / 'tests'), pattern=args.pattern, top_level_dir=str(root))
    result = unittest.TextTestRunner(verbosity=1 if args.quiet else 2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    raise SystemExit(main())
