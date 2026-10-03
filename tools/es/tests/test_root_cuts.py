"""Independent mixed-triple fixtures for diagnostic root-cut arithmetic."""
from itertools import combinations, product
import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))
from harness.research.root_cuts import graph_profile, root_masks


def direct_roots(colors, n):
    """No graph arithmetic: apply the defining DS rule on each mixed triple."""
    return tuple(A for A in range(1, (1 << n) - 1)
                 if all(cup == bool(A >> T[1] & 1)
                        for T, cup in colors.items()
                        if 0 < sum(bool(A >> x & 1) for x in T) < 3))


def test_every_arbitrary_coloring_through_five_matches_direct_root_semantics():
    # Includes non-one-change/nondecomposable inputs, not just admitted cases.
    for n in range(6):
        triples = tuple(combinations(range(n), 3))
        for mask in range(1 << len(triples)):
            colors = {T: bool(mask >> i & 1) for i, T in enumerate(triples)}
            expected = direct_roots(colors, n)
            assert root_masks(colors, n) == expected, (n, mask)
            assert len(expected) <= 4, (n, mask, expected)
            adjacency, reachability, components = graph_profile(colors, n)
            assert len(components) <= 4, (n, mask, components)
            assert sum(components) == (1 << n) - 1
            assert all(adjacency[x] & reachability[x] == adjacency[x] for x in range(n))
            representatives = [(C & -C).bit_length() - 1 for C in components]
            for triple in combinations(representatives, 3):
                assert any(reachability[x] >> y & 1 or reachability[y] >> x & 1
                           for x, y in combinations(triple, 2))
            # Independent strong predicate on EVERY component transversal.
            choices = [tuple(x for x in range(n) if C >> x & 1) for C in components]
            for selected in product(*choices):
                for a, b, c, d in combinations(sorted(selected), 4):
                    assert colors[a, b, c] == colors[a, b, d]
                    assert colors[a, c, d] == colors[b, c, d]
            for C in components:
                if C.bit_count() >= 2:
                    x = (C & -C).bit_length() - 1
                    for y in representatives:
                        assert reachability[x] >> y & 1 or reachability[y] >> x & 1


def test_color_duality_complements_the_lower_parts():
    triples = tuple(combinations(range(5), 3))
    for mask in (0, 1, 42, 511, 1023):
        colors = {T: bool(mask >> i & 1) for i, T in enumerate(triples)}
        dual = {T: not cup for T, cup in colors.items()}
        assert root_masks(dual, 5) == tuple(sorted(31 ^ A for A in root_masks(colors, 5)))


def test_retained_research_fixtures():
    fixture = json.loads((ROOT / "harness/research/examples/root-cuts-v1.json").read_text())
    for case in fixture["cases"]:
        n, mask = case["n"], case["mask"]
        colors = {T: bool(mask >> i & 1) for i, T in enumerate(combinations(range(n), 3))}
        expected = tuple(case["roots"])
        assert direct_roots(colors, n) == expected
        assert root_masks(colors, n) == expected


def test_two_point_and_empty_boundaries():
    assert graph_profile({}, 0) == ((), (), ())
    assert root_masks({}, 0) == root_masks({}, 1) == ()
    assert root_masks({}, 2) == (1, 2)
    assert root_masks({(0, 1, 2): True}, 3) == (2, 3, 6)
    assert root_masks({(0, 1, 2): False}, 3) == (1, 4, 5)


@pytest.mark.parametrize("n", [-1, True, 3.0, "3"])
def test_reject_invalid_size(n):
    with pytest.raises(ValueError):
        root_masks({}, n)


@pytest.mark.parametrize("colors,n", [
    ({}, 3),
    ({(0, 1, 2): True, (0, 2, 3): False}, 4),
    ({(0, 2, 1): True}, 3),
    ({(0, 1, 3): True}, 3),
    ({(0, 1, 2): 1}, 3),
    ({(0, 1, 2): None}, 3),
    ({(False, 1, 2): True}, 3),
    ({"012": True}, 3),
])
def test_reject_incomplete_or_malformed_colorings(colors, n):
    with pytest.raises(ValueError):
        graph_profile(colors, n)


def test_reject_nonmapping():
    with pytest.raises(TypeError):
        root_masks([], 3)
