"""Validated finite-context endpoint-slot operations.

Retains R24 profile_transform.py mathematics. These numerical operations have
a general hand derivation and independent signature fixtures, not a Lean
equivalence receipt. They do not evaluate unrestricted profile maxima.
"""
from __future__ import annotations


def _matrix(value, name):
    matrix = tuple(tuple(row) for row in value)
    n = len(matrix)
    if any(len(row) != n for row in matrix):
        raise ValueError(f"{name} must be square")
    if any(type(x) is not int or x < 0 for row in matrix for x in row):
        raise ValueError(f"{name} entries must be nonnegative integers")
    if any(matrix[i][j] != 0 for i in range(n) for j in range(i)):
        raise ValueError(f"{name} must have zero entries below its diagonal")
    return matrix


def _indices(keep, n, *, proper):
    kept = tuple(keep)
    if any(type(i) is not int or not 0 <= i < n for i in kept):
        raise ValueError("retained indices must be integers in range")
    if len(set(kept)) != len(kept) or not kept:
        raise ValueError("retained indices must be distinct and nonempty")
    if proper and len(kept) == n:
        raise ValueError("retained indices must form a proper subset")
    return tuple(sorted(kept))


def refine_slot_profile(caps, cups, keep, side, opposite_max, strong):
    """Return immutable (cap, cup) matrices for a finite context child.

    Matrices are square nonnegative integer upper-triangular endpoint limits
    on the same n ordered slots. Keep is a distinct nonempty proper subset of
    range(n), in any input order. Side is lower/upper, and 1<=opposite_max<strong.
    Strong and opposite_max are integer capacities, not forbidden sizes.
    Zero chain capacities remain zero; all unretained slots impose endpoint
    constraints, including slots that a later attaining tree leaves empty.
    """
    caps, cups = _matrix(caps, "caps"), _matrix(cups, "cups")
    n = len(caps)
    if len(cups) != n:
        raise ValueError("cap and cup matrices must have the same size")
    kept = _indices(keep, n, proper=True)
    if side not in ("lower", "upper"):
        raise ValueError("side must be lower or upper")
    if (type(strong) is not int or type(opposite_max) is not int
            or not 1 <= opposite_max < strong):
        raise ValueError("require integer capacities 1 <= opposite_max < strong")
    kept_set = set(kept)
    opposite = tuple(i for i in range(n) if i not in kept_set)
    growing, inherited = (cups, caps) if side == "lower" else (caps, cups)
    refined, unchanged = [], []
    for ii, first in enumerate(kept):
        row, other = [0] * len(kept), [0] * len(kept)
        left = tuple(x for x in opposite if x < first)
        for jj in range(ii, len(kept)):
            last = kept[jj]
            right = tuple(x for x in opposite if x > last)
            bounds = [growing[first][last], strong - opposite_max]
            bounds.extend(growing[x][last] - 1 for x in left)
            bounds.extend(growing[first][y] - 1 for y in right)
            bounds.extend(growing[x][y] - 2 for x in left for y in right)
            row[jj] = max(0, min(bounds))
            other[jj] = inherited[first][last]
        refined.append(tuple(row))
        unchanged.append(tuple(other))
    if side == "lower":
        return tuple(unchanged), tuple(refined)
    return tuple(refined), tuple(unchanged)


def expand_run_profile(word, caps, cups):
    """Expand run matrices to existing S slots and retain marker barriers.

    Word is an ordered iterable whose child token is the string S; every other
    token is treated as an inert marker. The matrices must have one row per
    nonempty consecutive S run. No marker level/maximum semantics are inferred.
    An empty word/profile gives empty matrices and barriers.
    """
    word = tuple(word)
    caps, cups = _matrix(caps, "caps"), _matrix(cups, "cups")
    positions = tuple(i for i, token in enumerate(word) if token == "S")
    run_of, run = [], -1
    for position in positions:
        if position == 0 or word[position - 1] != "S":
            run += 1
        run_of.append(run)
    if len(caps) != run + 1 or len(cups) != run + 1:
        raise ValueError("matrices must match the number of S runs")
    expanded = tuple(
        tuple(tuple(matrix[run_of[i]][run_of[j]] if i <= j else 0
                    for j in range(len(positions))) for i in range(len(positions)))
        for matrix in (caps, cups)
    )
    barriers = tuple(positions[i + 1] != positions[i] + 1
                     for i in range(len(positions) - 1))
    return expanded[0], expanded[1], barriers


def child_slot_barriers(barriers, keep):
    """Restrict barriers, adding one across each converted child-slot gap.

    Boolean barriers describe n=len(barriers)+1 ordered slots. Keep is a
    distinct nonempty subset of range(n); a full subset is allowed here.
    """
    barriers = tuple(barriers)
    if any(type(value) is not bool for value in barriers):
        raise ValueError("barriers must be booleans")
    kept = _indices(keep, len(barriers) + 1, proper=False)
    return tuple(last != first + 1 or barriers[first]
                 for first, last in zip(kept, kept[1:]))
