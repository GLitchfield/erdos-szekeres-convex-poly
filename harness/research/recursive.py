"""Explicit compatibility boundary for the retained F2 evaluator.

This preserves both historical and Lean-aligned zero-child arithmetic. The name
describes the implementation choice; it is not a Lean equivalence certificate.
"""
from pathlib import Path
import sys
from threading import Lock

VERSIONS = {
    'historical-f2-v1': 'python-historical',
    'context-bound-zero-children-v1': 'python-zero-children',
    'context-bound-zero-children-c-v1': 'compiled-zero-children',
}
_FACTORY_LOCK = Lock()


def evaluator(a, u, k, *, semantics, cache_size=16000):
    if semantics not in VERSIONS:
        raise ValueError('explicit registered recursion semantics required')
    if VERSIONS[semantics] == 'compiled-zero-children':
        from .context_bound import compiled_evaluator
        return compiled_evaluator(a, u, k, cache_size=cache_size)
    scripts = str(Path(__file__).resolve().parents[2] / 'scripts')
    if scripts not in sys.path: sys.path.insert(0,scripts)
    try:
        import decomposable_recursive_formula as legacy
    except ModuleNotFoundError as exc:
        if exc.name == 'numpy':
            raise RuntimeError(
                'recursive research probes require the es-harness[research] extra (numpy)'
            ) from None
        raise
    # The legacy factory reads CACHE_SIZE only while applying its lru_cache
    # decorator.  Serialize that instant and restore the module default so one
    # registered probe cannot silently change a later legacy caller's cache.
    with _FACTORY_LOCK:
        previous = legacy.CACHE_SIZE
        legacy.CACHE_SIZE = cache_size
        try:
            return legacy.make_F2(a, u, k, include_zero_children=VERSIONS[semantics] == 'python-zero-children')
        finally:
            legacy.CACHE_SIZE = previous
