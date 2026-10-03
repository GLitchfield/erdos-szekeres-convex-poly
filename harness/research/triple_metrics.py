"""Solver-free exact metrics of small complete ordered triple colorings.

Retained arithmetic: R25 check_bdl_mechanism.Finite and the direct predicates
in scripts/check_decomposable_enumeration.py. True means cup. Every triple
of a chain and every defining quadruple of a strong set is checked, even
when the coloring fails one-change. This is diagnostic, not Lean evidence.

Construction/strong queries enumerate subsets: worst-case O(2**n * n**4)
time and O(2**n) stored masks. Caller owns guarded execution and storage.
"""
from __future__ import annotations

from collections.abc import Mapping
from itertools import combinations
from math import comb
from types import MappingProxyType

Triple = tuple[int, int, int]


def validate_coloring(colors: Mapping[Triple, bool], n: int) -> None:
    """Validate the shared complete Boolean ordered-triple input contract."""
    if type(n) is not int or n < 0:
        raise ValueError("n must be a nonnegative integer (not bool)")
    if not isinstance(colors, Mapping):
        raise TypeError("colors must be a mapping of ordered triples to bool")
    if len(colors) != (comb(n, 3) if n >= 3 else 0):
        raise ValueError("colors must contain exactly all triples on range(n)")
    for triple, cup in colors.items():
        if (not isinstance(triple, tuple) or len(triple) != 3
                or any(type(x) is not int for x in triple)
                or not 0 <= triple[0] < triple[1] < triple[2] < n):
            raise ValueError("keys must be ordered integer triples in range(n)")
        if type(cup) is not bool:
            raise ValueError("colors must be bool: True is cup, False is cap")


class FiniteTripleColoring:
    """Exact subset cup/cap/strong maxima and maximum-chain endpoints.

    Input is copied; subsequent caller mutations cannot alter cached metrics.
    Results are immutable tuples/frozensets. Empty-set maxima are zero and
    its endpoint sets are empty. No one-change or decomposition is assumed.
    """

    def __init__(self, colors: Mapping[Triple, bool], n: int):
        validate_coloring(colors, n)
        self.n = n
        self.full = (1 << n) - 1
        self.colors = MappingProxyType(dict(colors))
        chains: dict[bool, list[int]] = {True: [], False: []}
        for size in range(n + 1):
            for points in combinations(range(n), size):
                mask = sum(1 << x for x in points)
                seen = {self.colors[T] for T in combinations(points, 3)}
                for want in (True, False):
                    if not seen or seen == {want}:
                        chains[want].append(mask)
        key = lambda mask: (mask.bit_count(), mask)
        self._chains = {want: tuple(sorted(masks, key=key, reverse=True))
                        for want, masks in chains.items()}
        self._metrics: dict[int, tuple[int, int]] = {}
        self._strong: tuple[int, ...] | None = None

    def _ground(self, mask: int | None) -> int:
        if mask is None:
            return self.full
        if type(mask) is not int or not 0 <= mask <= self.full:
            raise ValueError("subset mask must be an integer in range(2**n)")
        return mask

    @staticmethod
    def _want(want: bool) -> bool:
        if type(want) is not bool:
            raise ValueError("chain color must be bool: True cup, False cap")
        return want

    def points(self, mask: int | None = None) -> tuple[int, ...]:
        ground = self._ground(mask)
        return tuple(x for x in range(self.n) if ground >> x & 1)

    def monochromatic_masks(self, want: bool) -> tuple[int, ...]:
        """Every chain, sorted by decreasing (size, mask); includes empty."""
        return self._chains[self._want(want)]

    def metrics(self, mask: int | None = None) -> tuple[int, int]:
        """Return maximum cup/cap cardinalities on the requested subset."""
        ground = self._ground(mask)
        if ground not in self._metrics:
            self._metrics[ground] = tuple(
                next(S.bit_count() for S in self._chains[want]
                     if S & ground == S) for want in (True, False))
        return self._metrics[ground]

    def maximal_chain_masks(self, mask: int | None, want: bool) -> tuple[int, ...]:
        ground = self._ground(mask)
        want = self._want(want)
        size = self.metrics(ground)[0 if want else 1]
        return tuple(S for S in self._chains[want]
                     if S.bit_count() == size and S & ground == S)

    def extrema(self, mask: int | None, want: bool) -> tuple[frozenset[int], frozenset[int]]:
        """First/last points of ALL maximum chains; both empty at mask zero."""
        chains = self.maximal_chain_masks(mask, want)
        return (frozenset((S & -S).bit_length() - 1 for S in chains if S),
                frozenset(S.bit_length() - 1 for S in chains if S))

    def strong_masks(self) -> tuple[int, ...]:
        """All strong subsets, by the two equalities on EVERY quadruple."""
        if self._strong is None:
            found = []
            for size in range(self.n + 1):
                for points in combinations(range(self.n), size):
                    if all(self.colors[a, b, c] == self.colors[a, b, d]
                           and self.colors[a, c, d] == self.colors[b, c, d]
                           for a, b, c, d in combinations(points, 4)):
                        found.append(sum(1 << x for x in points))
            self._strong = tuple(sorted(found,
                key=lambda S: (S.bit_count(), S), reverse=True))
        return self._strong

    def strong_number(self, mask: int | None = None) -> int:
        ground = self._ground(mask)
        return next(S.bit_count() for S in self.strong_masks() if S & ground == S)
