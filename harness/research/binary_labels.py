"""Pure binary-label primitives retained from R25's classical constructions.

No solver, compiler, budgets or result storage. Materialized labels may be
large; callers own guarded execution. These are not Lean certificates.
"""
from collections.abc import Iterable
from itertools import combinations


def classical_pascal_labels(cup: int, cap: int) -> tuple[str, ...]:
    """Classical K(cup, cap), in spatial order; either bound1 is a singleton.

    Both inputs must be actual positive integers. The prefix-free binary
    labels have size choose(cup+cap-2,cup-1). With both bounds at least2
    their decoded cup/cap maxima attain the bounds; otherwise both are1.
    Recursion can reach depth cup+cap-2 and materializes the full output.
    """
    if type(cup) is not int or type(cap) is not int or cup < 1 or cap < 1:
        raise ValueError("cup and cap must be actual positive integers")

    def construct(a: int, b: int) -> tuple[str, ...]:
        if a == 1 or b == 1:
            return ("",)
        return (tuple("0" + x for x in construct(a - 1, b))
                + tuple("1" + x for x in construct(a, b - 1)))

    return construct(cup, cap)


def binary_label_coloring(labels: Iterable[str]) -> dict[tuple[int, int, int], bool]:
    """Decode finite prefix-free binary words in the given spatial order.

    True means cup: at the first coordinate where an increasing triple's
    bits differ, its middle word has bit0. Empty input and the singleton
    empty word are valid. Bare strings, duplicates, prefixes, nonstrings
    and nonbinary words are rejected. Does not require lexicographic order.
    """
    if isinstance(labels, (str, bytes)):
        raise ValueError("labels must be an iterable of binary words")
    words = tuple(labels)
    if any(type(word) is not str or set(word) - {"0", "1"} for word in words):
        raise ValueError("each label must be an actual binary string")
    ordered = sorted(words)
    if any(right.startswith(left) for left, right in zip(ordered, ordered[1:])):
        raise ValueError("labels must be distinct and prefix-free")
    colors = {}
    for a, b, c in combinations(range(len(words)), 3):
        coordinate = next(i for i, bits in enumerate(zip(words[a], words[b], words[c]))
                          if len(set(bits)) > 1)
        colors[a, b, c] = words[b][coordinate] == "0"
    return colors
