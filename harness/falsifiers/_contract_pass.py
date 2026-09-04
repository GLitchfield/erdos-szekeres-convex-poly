#!/usr/bin/env python3
"""Falsifier contract fixture: always passes (exit 0). Used by the harness acceptance tests."""
import sys
print("contract fixture: no counterexample searched; pass", file=sys.stderr)
sys.exit(0)
