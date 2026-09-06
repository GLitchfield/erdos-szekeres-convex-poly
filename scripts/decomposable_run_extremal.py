#!/usr/bin/env python3
"""Workstream B, step 2: exact extremal tables of a depth-1 child by run structure.

By experiment 0117 a lower child L of a deep-below split sees of its sibling U
only U's longest cap d and, for each cup Q of L, whether some U-vertex lies
left of first(Q) and whether some lies right of last(Q).  Writing the
interleaving as runs L^{r_1} U^{s_1} L^{r_2} ... , that information is: the
number p of L-runs, whether a U-run precedes the first L-run (sU) and whether
one follows the last (eU).  A cup with first vertex in run i and last vertex
in run j may then have at most u - 1 - [i > 1 or sU] - [j < p or eU] vertices,
and at most k - 1 - d; caps of L at most a - 1; strong sets of L at most k - 1.

E_low(a,u,k; p, sU, eU, d) is the largest decomposable coloring that can be
split into p nonempty consecutive runs under these constraints; E_up is the
mirror image (caps extended by L-vertices, cups at most u - 1, longest cup c
of L).  Both are computed by brute force over the decomposable class through
--max-n vertices with numpy.  These are the data any closed-form induction
bound must match; the tables of experiment 0116 are the case p <= 2.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from enumerate_decomposable_colorings import enumerate_class, coloring_dict, strong_sizes, threshold  # noqa: E402


def chain_table(chi, n, left):
    """T[f][l] = longest chain of color ``left`` with first vertex f and last vertex l (0 if none)."""
    T = np.zeros((n, n), dtype=np.int8)
    for v in range(n):
        T[v][v] = 1
    end = {}
    for j in range(n):
        for i in range(j):
            best = {i: 2}
            for h in range(i):
                if chi[(h, i, j)] == left:
                    for f, v in end[(h, i)].items():
                        if v + 1 > best.get(f, 0):
                            best[f] = v + 1
            end[(i, j)] = best
            for f, v in best.items():
                T[f][j] = max(T[f][j], v)
    return T


def compositions(m, p):
    for cuts in itertools.combinations(range(1, m), p - 1):
        yield [b - a for a, b in zip((0,) + cuts, cuts + (m,))]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=8)
    parser.add_argument("--cases", default="4,4,5;4,5,5;5,4,5;5,5,5;4,4,6;4,5,6")
    parser.add_argument("--max-runs", type=int, default=4)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--class-dir", type=Path, default=None,
                        help="directory of class_<n>.bin records written by tools/decomp_enum/enum_avoid (one case)")
    parser.add_argument("--avoiding", action="store_true",
                        help="enumerate only the (a,u,k)-avoiding subclass of the single case given (hereditary; exact), "
                             "which reaches thresholds beyond the full class's n <= 9")
    args = parser.parse_args()
    started = time.time()
    data = {}
    if args.class_dir is not None:
        MASKW = 9   # tools/decomp_enum/enum_avoid.c: MAXN 16, C(16,3) = 560 bits -> 9 words
        for m in range(1, args.max_n + 1):
            f = args.class_dir / f"class_{m}.bin"
            if m <= 2:
                # the enumerator writes n >= 3 only; one and two vertices are the empty coloring
                t = np.triu(np.full((m, m), 2, dtype=np.int8)); np.fill_diagonal(t, 1)
                data[m] = (t[None], t[None].copy(), np.array([m], dtype=np.int8))
                continue
            if not f.exists():
                data[m] = (np.zeros((0, m, m), dtype=np.int8), np.zeros((0, m, m), dtype=np.int8), np.zeros(0, dtype=np.int8))
                continue
            raw = np.fromfile(f, dtype=np.uint8)
            # record layout: MASKW*8 bytes mask, m*m cupT, m*m capT, 4 tail bytes
            rec = MASKW * 8 + 2 * m * m + 4
            assert raw.size % rec == 0, f"{f}: {raw.size} bytes is not a multiple of the record size {rec}"
            count = raw.size // rec
            recs = raw.reshape(count, rec)
            cups = recs[:, MASKW * 8: MASKW * 8 + m * m].astype(np.int8).reshape(count, m, m)
            caps = recs[:, MASKW * 8 + m * m: MASKW * 8 + 2 * m * m].astype(np.int8).reshape(count, m, m)
            strong = recs[:, -4].astype(np.int8)
            data[m] = (cups, caps, strong)
        print(f"class records loaded: { {m: len(data[m][2]) for m in data} }", file=sys.stderr, flush=True)
        classes = None
    elif args.avoiding:
        from decomposable_avoiding_class import enumerate_avoiding
        cases = args.cases.split(";")
        assert len(cases) == 1, "--avoiding takes exactly one case"
        a0, u0, k0 = (int(x) for x in cases[0].split(","))
        classes, tindex = enumerate_avoiding(a0, u0, k0, args.max_n)
        for m in range(1, args.max_n + 1):
            recs = classes.get(m, {})
            if not recs:
                data[m] = (np.zeros((0, m, m), dtype=np.int8), np.zeros((0, m, m), dtype=np.int8), np.zeros(0, dtype=np.int8))
                continue
            cups = np.stack([t[0] for t in recs.values()]); caps = np.stack([t[1] for t in recs.values()])
            strong = np.array([t[2] for t in recs.values()], dtype=np.int8)
            data[m] = (cups, caps, strong)
        print(f"avoiding subclass sizes: { {m: len(classes.get(m, {})) for m in range(1, args.max_n + 1)} }", file=sys.stderr, flush=True)
    else:
        classes, tindex = enumerate_class(args.max_n, progress=False)
    for m in range(1, args.max_n + 1):
        if args.avoiding or args.class_dir is not None:
            break
        idx = tindex[m]
        masks = sorted(classes[m])
        cups = np.zeros((len(masks), m, m), dtype=np.int8)
        caps = np.zeros((len(masks), m, m), dtype=np.int8)
        strong = np.zeros(len(masks), dtype=np.int8)
        for r, mask in enumerate(masks):
            if m < 3:
                cups[r] = caps[r] = np.triu(np.full((m, m), 2, dtype=np.int8)); np.fill_diagonal(cups[r], 1); np.fill_diagonal(caps[r], 1)
                strong[r] = m
                continue
            chi = coloring_dict(mask, m, idx)
            cups[r] = chain_table(chi, m, True)
            caps[r] = chain_table(chi, m, False)
            strong[r] = strong_sizes(chi, m)
        data[m] = (cups, caps, strong)
        print(f"tables n={m}: {len(masks)} colorings ({time.time()-started:.0f}s)", file=sys.stderr, flush=True)

    def extremal(a, u, k, p, s_flag, e_flag, coupling, lower: bool):
        """Largest m with a decomposable coloring in p runs meeting the constraints."""
        for m in range(args.max_n, p - 1, -1):
            cups, caps, strong = data[m]
            if len(strong) == 0:
                continue
            ok_strong = strong <= k - 1
            if lower:
                base_ok = ok_strong & (caps.max(axis=(1, 2)) <= a - 1)
            else:
                base_ok = ok_strong & (cups.max(axis=(1, 2)) <= u - 1)
            if not base_ok.any():
                continue
            for comp in compositions(m, p):
                run = np.repeat(np.arange(p), comp)
                left_ext = (run > 0) | bool(s_flag)
                right_ext = (run < p - 1) | bool(e_flag)
                if lower:
                    limit = np.minimum(u - 1 - left_ext[:, None].astype(int) - right_ext[None, :].astype(int), k - 1 - coupling)
                    tables = cups
                else:
                    limit = np.minimum(a - 1 - left_ext[:, None].astype(int) - right_ext[None, :].astype(int), k - 1 - coupling)
                    tables = caps
                limit = np.triu(limit)
                good = base_ok & (tables <= limit[None, :, :]).all(axis=(1, 2))
                if good.any():
                    return m
        return 0

    result = {"max_n": args.max_n, "cases": {}}
    for case in args.cases.split(";"):
        a, u, k = (int(x) for x in case.split(","))
        T = threshold(a, u, k)
        if T > args.max_n:
            print(f"skipping ({a},{u},{k}): threshold {T} > max-n", file=sys.stderr)
            continue
        low = {}
        up = {}
        for p in range(1, args.max_runs + 1):
            for s_flag in (0, 1):
                for e_flag in (0, 1):
                    for d in range(1, k - 1):
                        low[f"p={p},sU={s_flag},eU={e_flag},d={d}"] = extremal(a, u, k, p, s_flag, e_flag, d, lower=True)
                    for c in range(1, k - 1):
                        up[f"p={p},sL={s_flag},eL={e_flag},c={c}"] = extremal(a, u, k, p, s_flag, e_flag, c, lower=False)
        result["cases"][case] = {"threshold": T, "E_low": low, "E_up": up}
        print(json.dumps({"case": case, "threshold": T, "seconds": round(time.time() - started, 1)}), file=sys.stderr, flush=True)
    result["seconds"] = round(time.time() - started, 1)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=1) + "\n")


if __name__ == "__main__":
    main()
