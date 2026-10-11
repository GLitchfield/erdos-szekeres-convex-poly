"""CEGAR search for one-change colourings (signotopes) that admit NO structure of a given kind.

Promoted on 10 Oct 2026 from runs/claude-fbdl-20261010/fbdl_obstructions.py, the tool that refuted the full-range
band stack FBDL(6) (node ErdosSzekeres.fbdl_full_band_stack).  The run file stays unchanged as the recorded artifact.

The question "is there a colouring chi in a SAT-described class with no witness structure b" is exists-forall and
is answered by counterexample-guided refinement over an incremental solver:

    solve the class -> chi;  look for a witness b of chi (an exact search);
    b found  -> add the clause "b is not a valid witness of the colouring" (built from chi-independent literals);
    no b     -> chi is an OBSTRUCTION: record it, block its key, continue;
    UNSAT    -> every colouring in the class has a witness (the universal statement holds for this n).

``cegar`` is the generic loop; ``band_stack_obstructions`` instantiates it for FBDL: witnesses are band partitions
(``harness.research.band_partitions``: band j has no (j+2)-cup and no (k-j)-cap, chain convention), and the
blocking clause of a stack b says "some (j+2)-subset of band j is a cup or some (k-j)-subset is a cap" through
auxiliary literals y -> (all triples of the subset have that colour) (``ChainLiterals``).  The clause is sound
for every colouring: it is violated exactly by the colourings for which b is a valid stack.

Semantics and costs: diagnostic (python-sat CaDiCaL, no proof log, no Lean).  Exact in both directions when it
ends: an UNSAT verdict means every colouring of the class has a witness; every recorded obstruction is re-checked
by the independent backtracking search.  Iterations observed: FBDL k=6 hexagon-free n=12 437, n=13 1,654, n=14
4,600, n=15 12,705 (12,136 s), n=16 first obstruction after 9,162 (about 330 s); without the hexagon-free clause
the obstructions on 12 points are exactly the 12-cup and 12-cap (469 iterations).  Deletion-minimality of an
obstruction is checked against every (n-1)-subset.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from typing import Callable, Dict, Iterable, List, Optional, Sequence, Tuple

from .band_partitions import check_partition, find_partition, partition_sat
from .chains import longest_chain, strong_number
from .signotope_sat import SignotopeSAT, key_of

Triple = Tuple[int, int, int]
Coloring = Dict[Triple, bool]


class ChainLiterals:
    """Auxiliary literals ``lit(sub, cup)`` with ``lit -> every triple of sub is a cup`` (``cup=True``) or a cap.

    One-directional: the literal may be false for a monochromatic subset, which keeps the blocking clauses sound
    (a clause of such literals is satisfiable exactly when one of its subsets is monochromatic as stated)."""

    def __init__(self, base: SignotopeSAT, solver):
        self.base, self.solver, self.aux = base, solver, {}

    def lit(self, sub: Sequence[int], cup: bool) -> int:
        key = (tuple(sub), cup)
        if key not in self.aux:
            y = self.base.new()
            self.aux[key] = y
            for t in itertools.combinations(sub, 3):
                self.solver.add_clause([-y, self.base.T[t]] if cup else [-y, -self.base.T[t]])
        return self.aux[key]

    def __len__(self) -> int:
        return len(self.aux)


def band_stack_blocking_clause(chains: ChainLiterals, b: Sequence[int], k: int, n: int) -> List[int]:
    """Literals of the clause "b is not a valid band stack": a (j+2)-cup or a (k-j)-cap inside band j for some j.

    ``b[p]`` is the band of point p (bands 0..k-2, library convention ``band_partitions``)."""
    lits: List[int] = []
    for j in range(k - 1):
        pts = [p for p in range(n) if b[p] == j]
        lits += [chains.lit(s, True) for s in itertools.combinations(pts, j + 2)]
        lits += [chains.lit(s, False) for s in itertools.combinations(pts, k - j)]
    return lits


@dataclass
class CegarResult:
    """Outcome of ``cegar``: ``status`` is 'unsat' (every colouring has a witness), 'max_iter' or 'stopped'."""

    status: str
    iterations: int
    obstructions: List[dict] = field(default_factory=list)
    aux_literals: int = 0


def cegar(base: SignotopeSAT, find_witness: Callable[[Coloring], Optional[object]],
          blocking_clause: Callable[["ChainLiterals", object], List[int]], *,
          describe: Optional[Callable[[Coloring], dict]] = None, max_iter: Optional[int] = None,
          on_obstruction: Optional[Callable[[dict], None]] = None,
          on_progress: Optional[Callable[[int, int, int], None]] = None, report_every: int = 200,
          stop: Optional[Callable[[], bool]] = None) -> CegarResult:
    """Generic loop.  ``base.cl`` describes the class; ``find_witness(chi)`` returns a witness or None;
    ``blocking_clause(chains, b)`` returns the literals excluding every colouring for which b is a witness.
    Each obstruction is recorded as ``{'n', 'key', **describe(chi)}`` and blocked by its key."""
    from pysat.solvers import Cadical195

    n = base.n
    T3 = list(itertools.combinations(range(n), 3))
    solver = Cadical195(bootstrap_with=base.cl)
    chains = ChainLiterals(base, solver)
    res = CegarResult("stopped", 0)
    try:
        while max_iter is None or res.iterations < max_iter:
            if stop is not None and stop():
                break
            if not solver.solve():
                res.status = "unsat"
                break
            model = set(v for v in solver.get_model() if v > 0)
            chi: Coloring = {t: (base.T[t] in model) for t in T3}
            res.iterations += 1
            b = find_witness(chi)
            if b is None:
                rec = {"n": n, "key": key_of(n, chi)}
                if describe is not None:
                    rec.update(describe(chi))
                res.obstructions.append(rec)
                if on_obstruction is not None:
                    on_obstruction(rec)
                solver.add_clause([-base.T[t] if chi[t] else base.T[t] for t in T3])
            else:
                solver.add_clause(blocking_clause(chains, b))
            if on_progress is not None and res.iterations % report_every == 0:
                on_progress(res.iterations, len(res.obstructions), len(chains))
        else:
            res.status = "max_iter"
    finally:
        res.aux_literals = len(chains)
        solver.delete()
    return res


def band_stack_obstructions(n: int, k: int, *, kfree: bool = False, forbid: int = 0, max_iter: Optional[int] = None,
                            minimality: bool = True, on_obstruction=None, on_progress=None, report_every: int = 200,
                            stop=None) -> CegarResult:
    """Colourings on n points with no full-range band stack for parameter k (FBDL(k) obstructions).

    ``kfree`` adds "no convex k-set" (then an obstruction refutes FBDL(k) at n); ``forbid=m`` excludes m-cups and
    m-caps (drops the trivial full-chain obstructions).  Records carry ``cup``, ``cap``, ``strong`` and, with
    ``minimality``, whether every (n-1)-subset has a stack.  The witness search is ``partition_sat`` re-checked
    by ``find_partition``; a found stack is verified by ``check_partition`` before it is blocked."""
    base = SignotopeSAT(n)
    if kfree:
        base.no_strong_set(k)
    if forbid:
        base.no_cup(forbid)
        base.no_cap(forbid)
    bands = list(range(k - 1))
    pts = range(n)

    def find_witness(chi):
        b = partition_sat(chi, pts, k, bands)
        if b is None:
            if find_partition(chi, pts, k, bands) is not None:
                raise RuntimeError("partition_sat and find_partition disagree")
            return None
        if not check_partition(chi, pts, k, b, bands):
            raise RuntimeError("partition_sat returned an invalid stack")
        return b

    def describe(chi):
        rec = {"k": k, "kfree": kfree, "forbid": forbid,
               "cup": longest_chain(chi, pts, True), "cap": longest_chain(chi, pts, False), "strong": strong_number(chi, pts)}
        if minimality:
            rec["minimal"] = all(find_partition(chi, [q for q in pts if q != p], k, bands) is not None for p in pts)
        return rec

    return cegar(base, find_witness, lambda chains, b: band_stack_blocking_clause(chains, b, k, n), describe=describe,
                 max_iter=max_iter, on_obstruction=on_obstruction, on_progress=on_progress, report_every=report_every, stop=stop)
