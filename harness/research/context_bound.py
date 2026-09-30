"""ctypes boundary for the compiled context-bound-zero-children-v1 evaluator.

This is exploratory arithmetic and carries no Lean proof credit.
"""
from __future__ import annotations

import argparse
from collections import namedtuple
import ctypes
import hashlib
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile
from threading import Lock


SEMANTICS = "context-bound-zero-children-c-v1"
_BUILD_LOCK = Lock()
_LIBRARY = None
_C_INT_MAX = (1 << (ctypes.sizeof(ctypes.c_int) * 8 - 1)) - 1
_C_SIZE_MAX = (1 << (ctypes.sizeof(ctypes.c_size_t) * 8)) - 1
_CacheInfo = namedtuple("CacheInfo", "hits misses maxsize currsize")


def _cache_directory():
    directory = Path(tempfile.gettempdir()) / f"es-context-bound-{os.getuid()}"
    directory.mkdir(mode=0o700, parents=True, exist_ok=True)
    info = directory.stat()
    if (directory.is_symlink() or not directory.is_dir() or info.st_uid != os.getuid() or
            stat.S_IMODE(info.st_mode) & 0o077):
        raise RuntimeError(f"unsafe compiled context-bound cache directory: {directory}")
    return directory


def _load_library():
    global _LIBRARY
    if _LIBRARY is not None:
        return _LIBRARY
    source = Path(__file__).with_suffix(".c")
    digest = hashlib.sha256(source.read_bytes() + b"-std=c11-O3-v1").hexdigest()[:20]
    directory = _cache_directory()
    target = directory / f"context-bound-{digest}.so"
    with _BUILD_LOCK:
        if not target.exists():
            compiler = shutil.which(os.environ.get("CC", "cc"))
            if compiler is None:
                raise RuntimeError("a C compiler (`cc` or CC) is required for compiled context bounds")
            fd, temporary = tempfile.mkstemp(prefix=".context-bound-", suffix=".so", dir=directory)
            os.close(fd)
            try:
                proc = subprocess.run(
                    [compiler, "-std=c11", "-O3", "-fPIC", "-shared", str(source), "-o", temporary],
                    capture_output=True, text=True,
                )
                if proc.returncode:
                    raise RuntimeError("failed to compile context_bound.c: " + proc.stderr.strip())
                os.replace(temporary, target)
            finally:
                Path(temporary).unlink(missing_ok=True)
        library = ctypes.CDLL(str(target))
        function = library.es_context_bound
        function.argtypes = [
            ctypes.c_int, ctypes.c_int, ctypes.c_int,
            ctypes.POINTER(ctypes.c_int), ctypes.c_size_t,
            ctypes.POINTER(ctypes.c_int), ctypes.c_size_t, ctypes.c_size_t,
            ctypes.POINTER(ctypes.c_int64),
        ]
        function.restype = ctypes.c_int
        _LIBRARY = library
    return _LIBRARY


def _encode(word, maxima):
    encoded = []
    for token in word:
        if token == "S":
            encoded.append(0)
            continue
        if not isinstance(token, (tuple, list)) or len(token) != 2:
            raise ValueError(f"invalid context token {token!r}")
        level, side = token
        if type(level) is not int or level < 1 or side not in ("lower", "upper"):
            raise ValueError(f"invalid context token {token!r}")
        encoded.append(level if side == "lower" else -level)
    maxima = tuple(maxima)
    if any(type(value) is not int or not 0 <= value <= _C_INT_MAX for value in maxima):
        raise ValueError("maxima must be nonnegative C integers")
    if not encoded or 0 not in encoded:
        raise ValueError("a context word must contain at least one S")
    if any(abs(value) > _C_INT_MAX - len(encoded) for value in encoded):
        raise ValueError("context levels exceed the compiled evaluator range")
    return encoded, maxima


class _CompiledEvaluator:
    def __init__(self, a: int, u: int, k: int, cache_size: int):
        if (any(type(value) is not int or not 1 <= value <= _C_INT_MAX for value in (a, u)) or
                type(k) is not int or not 3 <= k <= _C_INT_MAX):
            raise ValueError("a and u must be positive C integers and k a C integer >= 3")
        if type(cache_size) is not int or not 1 <= cache_size <= _C_SIZE_MAX:
            raise ValueError("cache_size must be a positive size_t integer")
        self.a, self.u, self.k, self.cache_size = a, u, k, cache_size
        self._misses = 0
        self._function = _load_library().es_context_bound

    def __call__(self, word, maxima):
        encoded, maxima = _encode(word, maxima)
        word_array = (ctypes.c_int * len(encoded))(*encoded)
        maxima_array = (ctypes.c_int * len(maxima))(*maxima)
        result = ctypes.c_int64()
        self._misses += 1
        rc = self._function(
            self.a, self.u, self.k, word_array, len(encoded), maxima_array, len(maxima),
            self.cache_size, ctypes.byref(result),
        )
        if rc == 2:
            raise MemoryError("compiled context-bound evaluator allocation failed")
        if rc == 4:
            raise OverflowError("compiled context-bound result exceeds signed 64-bit range")
        if rc:
            raise ValueError(f"compiled context-bound evaluator rejected the context (rc={rc})")
        return int(result.value)

    def cache_clear(self):
        """Reset top-level call statistics; C recursion uses a fresh memo per call."""
        self._misses = 0

    def cache_info(self):
        """Match the retained evaluator interface without claiming a persistent C cache."""
        return _CacheInfo(hits=0, misses=self._misses, maxsize=self.cache_size, currsize=0)


def compiled_evaluator(a, u, k, *, cache_size=16000):
    """Return a callable implementing ``context-bound-zero-children-c-v1``."""
    return _CompiledEvaluator(a, u, k, cache_size)


def _parse_word(spec: str):
    word = []
    for raw in spec.split(","):
        token = raw.strip()
        if token == "S":
            word.append("S")
        elif len(token) >= 2 and token[-1] in "LU" and token[:-1].isdigit():
            word.append((int(token[:-1]), "lower" if token[-1] == "L" else "upper"))
        else:
            raise ValueError(f"invalid --word token {token!r}")
    return tuple(word)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", required=True, help="a,u,k")
    parser.add_argument("--word", required=True, help="comma-separated S, 1L, 2U, ...")
    parser.add_argument("--maxima", default="", help="comma-separated sibling maxima")
    parser.add_argument("--cache-size", type=int, default=16000)
    args = parser.parse_args(argv)
    a, u, k = (int(value) for value in args.case.split(","))
    maxima = tuple(int(value) for value in args.maxima.split(",") if value)
    value = compiled_evaluator(a, u, k, cache_size=args.cache_size)(_parse_word(args.word), maxima)
    print(value)


if __name__ == "__main__":
    main()
