#!/usr/bin/env python3
"""Lemma 2 of the induction (experiment 0120): F does not increase when a sibling's chain
maximum grows.  For every abstract context (as in decomposable_additivity_test.py) and every
level, compare F with that level's maximum raised by one."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decomposable_recursive_formula import make_F  # noqa: E402
from decomposable_additivity_test import contexts  # noqa: E402


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", required=True)
    parser.add_argument("--s-max", type=int, default=5)
    parser.add_argument("--e-max", type=int, default=2)
    parser.add_argument("--levels", type=int, default=2)
    args = parser.parse_args()
    a, u, k = (int(x) for x in args.case.split(","))
    F = make_F(a, u, k)
    checked = violations = 0
    examples = []
    for word, maxima in contexts(args.s_max, args.e_max, args.levels, k):
        base = F(word, maxima)
        for i in range(len(maxima)):
            if maxima[i] + 1 > k - 2:
                continue
            bigger = maxima[:i] + (maxima[i] + 1,) + maxima[i + 1:]
            checked += 1
            if F(word, bigger) > base:
                violations += 1
                if len(examples) < 10:
                    examples.append({"word": ["S" if w == "S" else f"{w[0]}{'L' if w[1]=='lower' else 'U'}" for w in word],
                                     "maxima": list(maxima), "F": base, "F_bigger": F(word, bigger), "level": i + 1})
    print(json.dumps({"case": args.case, "checked": checked, "violations": violations, "examples": examples}))


if __name__ == "__main__":
    main()
