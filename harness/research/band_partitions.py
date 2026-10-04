"""Band partitions for the Band Decomposition Lemma (BDL): exact search, verifier, and SAT cross-check.

Promoted on 3 Oct 2026 from runs/claude-bandrule-20261003/bl.py (``partitions``, ``check_partition``,
``bdl_range``) and runs/claude-audit-bdl-20261003/dec.py (``band_partition_bt``,
``band_partition_sat``, ``check_partition``). The run files stay unchanged as the recorded artifacts.

Definitions (chain conventions of harness.research.chains: sets of <= 2 points are both cups and caps):

* A band partition of a point set X for parameter k is a map b: X -> Z such that every band
  X_j = b^-1(j) has cup(X_j) <= j + 1 and cap(X_j) <= k - 1 - j. Band j can hold a point only when
  0 <= j <= k - 2, and bands 0 and k - 2 hold at most one point each (a pair is a 2-cup and a 2-cap).
* BDL range: with alpha = cup(X), beta = cap(X), the bands are j in [k - 1 - beta, alpha - 1]
  (``bdl_range``). BDL asserts: a decomposable X with strong(X) <= k - 1 and alpha + beta >= k has a band
  partition in that range. alpha + beta = k is the one-band case (X itself, j = alpha - 1).
* Exhaustive evidence (runs/claude-audit-bdl-20261003, diagnostic, no Lean): BDL holds for every
  decomposable colouring on n <= 9 points (9,716,124 multi-band pairs); the frozen n <= 6 per-n counts
  are regression fixture examples/band-partitions-v1.json.

``partitions`` is a complete backtracking search over points in x-order with incremental per-band
longest-chain tables (exact: an empty result means no partition exists, given ``allowed``).
``check_partition`` is an independent verifier that recomputes every band's chain numbers from scratch.
``partition_sat`` is a second exact method (python-sat CaDiCaL), used to re-check "no partition" verdicts.
Diagnostic computation only, not Lean proofs.
"""
from __future__ import annotations

from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from .chains import chains as _chains, longest_chain

Triple = Tuple[int, int, int]
Coloring = Mapping[Triple, bool]


def bdl_range(alpha: int, beta: int, k: int) -> List[int]:
    """BDL band indices ``k - 1 - beta .. alpha - 1`` for cup number alpha and cap number beta."""
    return list(range(k - 1 - beta, alpha))


def band_limits(j: int, k: int) -> Tuple[int, int]:
    """``(cup limit, cap limit) = (j + 1, k - 1 - j)`` of band j."""
    return j + 1, k - 1 - j


def allowed_from_forbid(points: Iterable[int], bands: Iterable[int], forbid: Mapping[int, Iterable[int]]) -> Dict[int, set]:
    """``allowed[p]`` = bands not forbidding p, from ``forbid[j]`` = points that may not go in band j
    (e.g. the P invariant: bottom band j0 only inside x <= L*)."""
    bands = list(bands)
    forbid = {j: set(v) for j, v in forbid.items()}
    return {p: {j for j in bands if p not in forbid.get(j, ())} for p in points}


def partitions(cup: Coloring, points: Iterable[int], k: int, bands: Iterable[int], *,
               allowed: Optional[Mapping[int, Iterable[int]]] = None, limit: Optional[int] = None,
               first: bool = False) -> List[Tuple[int, ...]]:
    """Every band partition of ``points`` with bands from ``bands`` (in that preference order), as tuples
    aligned with sorted(points): ``b[i]`` is the band of the i-th point (so ``b[p]`` for points range(n)).

    ``allowed[p]`` optionally restricts point p's bands; ``limit`` stops after that many partitions;
    ``first=True`` stops after the first. Exact and complete within those restrictions.
    """
    S = sorted(points)
    n = len(S)
    bands = list(bands)
    allowed_sets = None if allowed is None else {p: set(allowed[p]) for p in S}
    b: List[Optional[int]] = [None] * n
    ecup: Dict[Tuple[int, int], int] = {}
    ecap: Dict[Tuple[int, int], int] = {}
    out: List[Tuple[int, ...]] = []

    def rec(i: int) -> bool:
        if limit is not None and len(out) >= limit:
            return True
        if i == n:
            out.append(tuple(b))  # type: ignore[arg-type]
            return first
        p = S[i]
        for j in bands:
            if allowed_sets is not None and j not in allowed_sets[p]:
                continue
            mc, ma = j + 1, k - 1 - j
            if mc < 1 or ma < 1:
                continue
            same = [x for x in range(i) if b[x] == j]
            ok = True
            newc: Dict[Tuple[int, int], int] = {}
            newk: Dict[Tuple[int, int], int] = {}
            for x in same:
                vc = vk = 2
                for h in same:
                    if h >= x:
                        break
                    if cup[(S[h], S[x], p)]:
                        if ecup[(h, x)] + 1 > vc:
                            vc = ecup[(h, x)] + 1
                    elif ecap[(h, x)] + 1 > vk:
                        vk = ecap[(h, x)] + 1
                if vc > mc or vk > ma:
                    ok = False
                    break
                newc[(x, i)] = vc
                newk[(x, i)] = vk
            if not ok:
                continue
            b[i] = j
            ecup.update(newc)
            ecap.update(newk)
            if rec(i + 1):
                return True
            for key in newc:
                del ecup[key]
                del ecap[key]
            b[i] = None
        return False

    rec(0)
    return out


def find_partition(cup: Coloring, points: Iterable[int], k: int, bands: Iterable[int], *,
                   allowed: Optional[Mapping[int, Iterable[int]]] = None) -> Optional[Tuple[int, ...]]:
    """The first band partition in search order (aligned with sorted(points)), or None if none exists."""
    found = partitions(cup, points, k, bands, allowed=allowed, first=True)
    return found[0] if found else None


def check_partition(cup: Coloring, points: Iterable[int], k: int, b: Sequence[int],
                    bands: Optional[Iterable[int]] = None) -> bool:
    """Independent verifier: ``b`` (aligned with sorted(points)) puts every point in a band j (inside
    ``bands`` when given) whose members have cup <= j + 1 and cap <= k - 1 - j, recomputed from scratch."""
    S = sorted(points)
    if len(b) != len(S):
        return False
    allowed = None if bands is None else set(bands)
    members: Dict[int, List[int]] = {}
    for p, j in zip(S, b):
        if allowed is not None and j not in allowed:
            return False
        members.setdefault(j, []).append(p)
    for j, mem in members.items():
        if longest_chain(cup, mem, True) > j + 1 or longest_chain(cup, mem, False) > k - 1 - j:
            return False
    return True


def partition_sat(cup: Coloring, points: Iterable[int], k: int, bands: Iterable[int], *,
                  allowed: Optional[Mapping[int, Iterable[int]]] = None) -> Optional[Tuple[int, ...]]:
    """Exact SAT decision (python-sat Cadical195): variables x[p, j]; every point in at least one band; no
    (j + 2)-cup and no (k - j)-cap inside band j; bands outside 0..k-2 and disallowed pairs are unit-false.
    A point true in several bands keeps the first (band conditions are hereditary). Returns a partition
    aligned with sorted(points), or None. Clause count grows with the number of chains; small sets only."""
    from pysat.solvers import Cadical195

    S = sorted(points)
    bands = list(bands)
    if not S:
        return ()
    if not bands:
        return None
    var = {}
    for p in S:
        for j in bands:
            var[(p, j)] = len(var) + 1
    clauses = [[var[(p, j)] for j in bands] for p in S]
    for j in bands:
        mc, ma = j + 1, k - 1 - j
        if mc < 1 or ma < 1:
            clauses += [[-var[(p, j)]] for p in S]
            continue
        if allowed is not None:
            clauses += [[-var[(p, j)]] for p in S if j not in set(allowed[p])]
        for c in _chains(cup, mc + 1, True, S):
            clauses.append([-var[(p, j)] for p in c])
        for d in _chains(cup, ma + 1, False, S):
            clauses.append([-var[(p, j)] for p in d])
    solver = Cadical195(bootstrap_with=clauses)
    try:
        if not solver.solve():
            return None
        model = set(v for v in solver.get_model() if v > 0)
    finally:
        solver.delete()
    return tuple(next(j for j in bands if var[(p, j)] in model) for p in S)
