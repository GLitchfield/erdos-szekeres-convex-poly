"""Heuristic realization of a rank-3 chirotope (one-change colouring / signotope key) by a planar point set.

Method (promoted 2026-10-10 from runs/claude-halving-20261008/cell_descent.py, the realizer that found the
16-point SPLIT(6) counterexample):
  1. penalty start: L-BFGS on sum relu(eps - s*det)^2 over all triples, coordinates parametrised to keep the
     sweep order (x = cumulative softmax, y = tanh);
  2. exact single-point moves: with the other n-1 points fixed, the triples through point i are half-planes in
     (x_i, y_i); every cell of that line arrangement inside the x-order strip is sampled (vertices offset in four
     directions, strip crossings), the point moves to a cell with the FEWEST violated triples and is centred there
     by an LP; the global violated count never increases;
  3. kicks (a random point to a random near-best cell) when stuck, then restarts.
A result is accepted only after rounding to integer coordinates whose exact sweep key (point_sets.sweep_key)
equals the target.  Failure is heuristic evidence only: on realizable random 16-point sets the method succeeds at
the first restart in under a second, but near-misses of 1-2 violated triples also occur on realizable inputs.
Non-realizability needs a certificate (biquadratic final polynomial or order-type database), not this module.

numpy and scipy are imported lazily; point_sets is pure Python.
"""
from __future__ import annotations

import itertools
from typing import Sequence

from harness.research import point_sets as ps


def chi_from_key(n: int, key: str) -> dict[tuple[int, int, int], bool]:
    assert len(key) == n * (n - 1) * (n - 2) // 6, 'key length must be C(n,3)'
    return {t: key[i] == '1' for i, t in enumerate(itertools.combinations(range(n), 3))}


def _np():
    import numpy as np
    return np


def _setup(n, chi):
    np = _np()
    T = np.array(list(itertools.combinations(range(n), 3)))
    s = np.array([1.0 if chi[tuple(t)] else -1.0 for t in T])
    return T, s


def _dets(x, y, T):
    a, b, c = T[:, 0], T[:, 1], T[:, 2]
    return (x[b] - x[a]) * (y[c] - y[a]) - (x[c] - x[a]) * (y[b] - y[a])


def _coords(z, n):
    np = _np()
    u, v = z[:n], z[n:]
    e = np.exp(u - u.max())
    return np.cumsum(e) / e.sum(), np.tanh(v)


def penalty_start(n, chi, rng, eps=1e-3, maxiter=3000):
    """One L-BFGS run from a random start; returns (x, y) rescaled to [-0.95, 0.95]^2 with x increasing."""
    np = _np()
    from scipy.optimize import minimize
    T, s = _setup(n, chi)

    def loss(z):
        x, y = _coords(z, n)
        r = np.maximum(0.0, eps - s * _dets(x, y, T))
        return float((r * r).sum())

    z0 = np.concatenate([rng.normal(0, 1, n), rng.normal(0, 1, n)])
    res = minimize(loss, z0, method='L-BFGS-B', options={'maxiter': maxiter, 'maxfun': 200000})
    x, y = _coords(res.x, n)
    return _rescale(x), _rescale(y)


def _rescale(v):
    np = _np()
    v = np.asarray(v, float)
    if v.max() > v.min():
        v = 2 * (v - v.min()) / (v.max() - v.min()) - 1
    return 0.95 * v


def violated(n, chi, x, y):
    """Number of triples whose orientation disagrees with chi."""
    T, s = _setup(n, chi)
    return int((s * _dets(x, y, T) <= 0).sum())


def _affine_rows(n, chi, i, x, y):
    """For every pair a<b of other points: (s c1, s c2, s c0) with s*det(sorted(a,b,i)) = s*(c0 + c1 x_i + c2 y_i)."""
    np = _np()
    rows = []
    for a, b in itertools.combinations([p for p in range(n) if p != i], 2):
        t = tuple(sorted((a, b, i)))
        s = 1.0 if chi[t] else -1.0
        p, q, r = t

        def f(xi, yi):
            X = x.copy(); Y = y.copy(); X[i] = xi; Y[i] = yi
            return (X[q] - X[p]) * (Y[r] - Y[p]) - (X[r] - X[p]) * (Y[q] - Y[p])

        c0 = f(0.0, 0.0); c1 = f(1.0, 0.0) - c0; c2 = f(0.0, 1.0) - c0
        rows.append((s * c1, s * c2, s * c0))
    return np.array(rows)


def best_cell(n, chi, i, x, y, box=1.0, gap=1e-4, rng=None, rank=0):
    """Move point i to a cell of the arrangement of its 'other pair' lines with the fewest violated triples
    (rank > 0 with rng: a random cell among those with the rank-th smallest count).  Returns (xi, yi, count)."""
    np = _np()
    from scipy.optimize import linprog
    A = _affine_rows(n, chi, i, x, y)
    lo = x[i - 1] + gap if i > 0 else -box
    hi = x[i + 1] - gap if i < n - 1 else box
    if lo >= hi:
        return None
    c1, c2, c0 = A[:, 0], A[:, 1], A[:, 2]
    I, J = np.triu_indices(len(A), 1)
    det = c1[I] * c2[J] - c1[J] * c2[I]
    ok = np.abs(det) > 1e-14
    vx = (-c0[I] * c2[J] + c0[J] * c2[I])[ok] / det[ok]
    vy = (-c1[I] * c0[J] + c1[J] * c0[I])[ok] / det[ok]
    for xb in (lo + 1e-9, hi - 1e-9):
        nz = np.abs(c2) > 1e-14
        vx = np.concatenate([vx, np.full(nz.sum(), xb)])
        vy = np.concatenate([vy, (-c0[nz] - c1[nz] * xb) / c2[nz]])
    vx = np.concatenate([vx, [lo, lo, hi, hi, (lo + hi) / 2, x[i]]])
    vy = np.concatenate([vy, [-box, box, -box, box, 0.0, y[i]]])
    d = 1e-6 * max(hi - lo, 1e-3)
    cx = np.concatenate([vx + d, vx + d, vx - d, vx - d, vx])
    cy = np.concatenate([vy + d, vy - d, vy + d, vy - d, vy])
    keep = (cx > lo) & (cx < hi) & (np.abs(cy) <= box)
    cx, cy = cx[keep], cy[keep]
    if len(cx) == 0:
        return None
    val = c1[None, :] * cx[:, None] + c2[None, :] * cy[:, None] + c0[None, :]
    viol = (val <= 0).sum(axis=1)
    order = np.argsort(viol, kind='stable')
    if rng is not None and rank > 0:
        vals = np.unique(viol[order])
        target = vals[min(rank, len(vals) - 1)]
        k = rng.choice(np.flatnonzero(viol == target))
    else:
        k = order[0]
    sat = val[k] > 0
    A_ub = np.column_stack([-c1[sat], -c2[sat], np.ones(int(sat.sum()))])
    res = linprog([0, 0, -1], A_ub=A_ub, b_ub=c0[sat], bounds=[(lo, hi), (-box, box), (None, None)], method='highs')
    if res.status == 0:
        xi, yi = res.x[0], res.x[1]
        v2 = int(((c1 * xi + c2 * yi + c0) <= 0).sum())
        if v2 <= viol[k]:
            return xi, yi, v2
    return float(cx[k]), float(cy[k]), int(viol[k])


def descent(n, chi, x, y, rng, kicks=20):
    """Best-cell moves over all points until no improvement, with `kicks` random perturbations when stuck.
    Returns (x, y, violated) for the best state seen (violated == 0 means all triples agree in floats)."""
    x = x.copy(); y = y.copy()
    cur = violated(n, chi, x, y); best = cur; bx, by = x.copy(), y.copy(); left = kicks
    while True:
        improved = False
        for i in rng.permutation(n):
            r = best_cell(n, chi, int(i), x, y)
            if r is None:
                continue
            x2 = x.copy(); y2 = y.copy(); x2[i] = r[0]; y2[i] = r[1]
            new = violated(n, chi, x2, y2)
            if new <= cur:
                improved |= new < cur
                x, y, cur = x2, y2, new
        if cur < best:
            best, bx, by = cur, x.copy(), y.copy()
        if cur == 0:
            return x, y, 0
        if not improved:
            if left == 0:
                return bx, by, best
            left -= 1
            i = int(rng.integers(n))
            r = best_cell(n, chi, i, x, y, rng=rng, rank=int(rng.integers(1, 4)))
            if r is not None:
                x[i], y[i] = r[0], r[1]; cur = violated(n, chi, x, y)


def realize(n: int, key: str, restarts: int = 20, kicks: int = 40, seed: int = 0, verbose: bool = False):
    """Try to realize the chirotope `key` on n points.  Returns (points, best_violated): integer points whose
    exact sweep key equals `key`, or None with the fewest violated triples seen (heuristic evidence only)."""
    np = _np()
    chi = chi_from_key(n, key)
    rng = np.random.default_rng(seed)
    best = n ** 3
    for r in range(restarts):
        x, y = penalty_start(n, chi, rng)
        xs, ys, b = descent(n, chi, x, y, rng, kicks=kicks)
        best = min(best, b)
        if verbose:
            print(f'restart {r}: violated {b}', flush=True)
        if b == 0:
            P = ps.integer_points(list(map(float, xs)), list(map(float, ys)), key=key)
            if P is None:
                P = ps.rational_points(list(map(float, xs)), list(map(float, ys)))
                if not (ps.general_position(P) and ps.sweep_key(P) == key):
                    continue
            return P, 0
    return None, best


def random_realizable_key(n: int, seed: int) -> tuple[str, list[ps.Point]]:
    """A control: the key of n random integer points with distinct x (realizable by construction)."""
    import random
    rng = random.Random(seed)
    while True:
        P = [(rng.randrange(-10 ** 6, 10 ** 6), rng.randrange(-10 ** 6, 10 ** 6)) for _ in range(n)]
        if len({p[0] for p in P}) == n and ps.general_position(P):
            P.sort()
            return ps.sweep_key(P), P
