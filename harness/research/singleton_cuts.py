"""Pure singleton-cut enumeration, retained from R13's diagnostic probes.

This enumerates arithmetic queries; neither the enumeration nor an evaluator
result is a Lean proof of singleton attainment or contraction.
"""
from __future__ import annotations

from .primitives import part


def singleton_cut_values(evaluate, row):
    """Return every (sum, position, side, sibling_maximum) singleton cut.

    ``row`` follows ``primitives.part``: word, maxima, a, u, k and chosen.
    Require k >= 3 and at least two S positions, so both parts are nonempty.
    The callable evaluates (word, maxima) at the row's global parameters;
    exposed a/u/k attributes must agree. Values of zero are retained, including
    a positive leaf paired with a zero complement. Evaluator errors propagate.

    Order matches runs/r13-sol-20260930/probe_singleton_normal.py: increasing
    child position and lower coupling d, then lower/d and upper/(k-1-d).
    Cache ownership, guards, progress and result storage stay with the caller.
    """
    k = row["k"]
    if type(k) is not int or k < 3:
        raise ValueError("singleton cuts require integer k >= 3")
    for key in ("a", "u", "k"):
        if hasattr(evaluate, key) and getattr(evaluate, key) != row[key]:
            raise ValueError(f"evaluator {key} does not match the context row")
    children = frozenset(i for i, token in enumerate(row["word"]) if token == "S")
    if len(children) < 2:
        raise ValueError("proper singleton cuts require at least two S positions")
    values = []
    for p in sorted(children):
        for d in range(1, k - 1):
            for side, maximum in (("lower", d), ("upper", k - 1 - d)):
                opposite = "upper" if side == "lower" else "lower"
                leaf = part(row, {p}, side, maximum)
                rest = part(row, children - {p}, opposite, k - 1 - maximum)
                value = evaluate(leaf["word"], leaf["maxima"])
                value += evaluate(rest["word"], rest["maxima"])
                values.append((value, p, side, maximum))
    return values
