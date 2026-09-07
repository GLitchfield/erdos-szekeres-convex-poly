#!/usr/bin/env python3
"""Extract the choice rule behind the end-cut normal form (experiment 0124).

For a context with at least two runs, an interior block B (neither a prefix nor a suffix),
an orientation and a coupling d, the interior-first tree is: cut B off, then the rest R
(two pieces) is a two-run context whose best tree, by the normal form, strips one of its
ends e2 on some side s2 at some coupling m2 (we record every optimal first strip of R).
The end-first tree strips a global end e1 on side s1 at coupling m1 at the root, then
cuts B in the residual σ' at coupling d'.  For each interior cut we record the set of
(e1, s1, m1, d') with V(B-cut) <= base(e1 strip) + V_{σ'}(B, o, d') and test rules such
as "e1 = e2, s1 = s2, m1 = m2, d' = d" and their relaxations, so that the strip lemma
can be stated as a specific inequality.  Literal Lean recursion.
"""
from __future__ import annotations

import argparse
import collections
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import decomposable_recursive_formula as drf  # noqa: E402
from decomposable_additivity_test import child, contexts  # noqa: E402
from decomposable_recursive_formula import run_index  # noqa: E402


def cut(F, word, maxima, block, o, d, k):
    """The two parts of an interval cut and their bounds: block on side o at coupling d."""
    rest = frozenset(i for i, w in enumerate(word) if w == "S") - block
    if o == "lower":
        A = child(word, maxima, block, "lower", d); R = child(word, maxima, rest, "upper", k - 1 - d)
    else:
        A = child(word, maxima, block, "upper", k - 1 - d); R = child(word, maxima, rest, "lower", d)
    return A, R, F(*A) + F(*R)


def strips(F, word, maxima, k):
    """All end strips of a context: (end, side, coupling) -> (base of the singleton, residual context)."""
    pos = [i for i, w in enumerate(word) if w == "S"]
    out = {}
    for end, p in (("first", pos[0]), ("last", pos[-1])):
        for s in ("lower", "upper"):
            for m in range(1, k - 1):
                single = frozenset([p]); rest = frozenset(pos) - single
                if s == "lower":
                    P = child(word, maxima, single, "lower", m); Q = child(word, maxima, rest, "upper", k - 1 - m)
                else:
                    P = child(word, maxima, single, "upper", k - 1 - m); Q = child(word, maxima, rest, "lower", m)
                out[end, s, m] = (F(*P), Q)
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", required=True)
    ap.add_argument("--s-max", type=int, default=4)
    ap.add_argument("--e-max", type=int, default=2)
    ap.add_argument("--levels", type=int, default=2)
    ap.add_argument("--cache-size", type=int, default=1_500_000)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    a, u, k = map(int, args.case.split(","))
    drf.CACHE_SIZE = args.cache_size
    F = drf.make_F2(a, u, k, include_zero_children=True)
    stats = collections.Counter()
    examples = collections.defaultdict(list)
    rules = {
        "same_end_same_side_same_m_same_d": lambda r, e1, s1, m1, d1, d: any(e1 == e2 and s1 == s2 and m1 == m2 and d1 == d for (e2, s2, m2) in r),
        "same_end_same_side_same_m": lambda r, e1, s1, m1, d1, d: any(e1 == e2 and s1 == s2 and m1 == m2 for (e2, s2, m2) in r),
        "same_end_same_side": lambda r, e1, s1, m1, d1, d: any(e1 == e2 and s1 == s2 for (e2, s2, m2) in r),
        "same_end": lambda r, e1, s1, m1, d1, d: any(e1 == e2 for (e2, s2, m2) in r),
        "same_end_same_side_m_within_1_same_d": lambda r, e1, s1, m1, d1, d: any(e1 == e2 and s1 == s2 and abs(m1 - m2) <= 1 and d1 == d for (e2, s2, m2) in r),
        "same_end_same_side_same_m_d_within_1": lambda r, e1, s1, m1, d1, d: any(e1 == e2 and s1 == s2 and m1 == m2 and abs(d1 - d) <= 1 for (e2, s2, m2) in r),
        "same_end_same_side_both_within_1": lambda r, e1, s1, m1, d1, d: any(e1 == e2 and s1 == s2 and abs(m1 - m2) <= 1 and abs(d1 - d) <= 1 for (e2, s2, m2) in r),
        "same_end_any_side_both_within_1": lambda r, e1, s1, m1, d1, d: any(e1 == e2 and abs(m1 - m2) <= 1 and abs(d1 - d) <= 1 for (e2, s2, m2) in r),
        "same_d_any_strip": lambda r, e1, s1, m1, d1, d: d1 == d,
    }
    for word, maxima in contexts(args.s_max, args.e_max, args.levels, k):
        pos = [i for i, w in enumerate(word) if w == "S"]
        ridx = run_index(word)
        nruns = len({ridx[p] for p in pos})
        if nruns < 2:
            continue
        n = len(pos)
        root_strips = strips(F, word, maxima, k)
        for i in range(1, n):
            for j in range(i + 1, n):
                B = frozenset(pos[i:j])  # interior: 0 < i, j < n
                for o in ("lower", "upper"):
                    for d in range(1, k - 1):
                        A, R, v = cut(F, word, maxima, B, o, d, k)
                        stats["interior_cuts"] += 1
                        # optimal first strips of the rest part R (a two-run context)
                        bR = F(*R)
                        rs = strips(F, R[0], R[1], k)
                        opt = {key for key, (bp, Q) in rs.items() if bp + F(*Q) == bR}
                        if not opt:
                            stats["rest_not_end_attained"] += 1
                            if len(examples["rest_not_end_attained"]) < 5:
                                examples["rest_not_end_attained"].append({"word": word, "maxima": list(maxima), "block": sorted(B), "o": o, "d": d})
                            continue
                        # root strips that dominate, with the cut B redone in the residual
                        dom = set()
                        for (e1, s1, m1), (bp, Q) in root_strips.items():
                            pos2 = [q for q, w in enumerate(Q[0]) if w == "S"]
                            ridx2 = run_index(Q[0])
                            if len({ridx2[q] for q in pos2}) < 2:
                                # single-run residual: its bound is its base; record separately
                                if bp + F(*Q) >= v:
                                    dom.add((e1, s1, m1, "single"))
                                continue
                            for d1 in range(1, k - 1):
                                _, _, v2 = cut(F, Q[0], Q[1], B, o, d1, k)
                                if bp + v2 >= v:
                                    dom.add((e1, s1, m1, d1))
                        if not dom:
                            stats["undominated"] += 1
                            if len(examples["undominated"]) < 8:
                                examples["undominated"].append({"word": word, "maxima": list(maxima), "block": sorted(B), "o": o, "d": d, "value": v, "rest_opt": sorted(opt)})
                            continue
                        stats["dominated"] += 1
                        stats["only_single_run_residual"] += all(x[3] == "single" for x in dom)
                        dom_two = [x for x in dom if x[3] != "single"]
                        # the mirror rule, term by term: root strip = the rest part's optimal strip (e, s, m), block coupling d;
                        # (1) base(B in σ) <= base(B in σ'), (2) base(e in R) <= base(e in σ), (3) bound(R minus e) <= bound(σ' minus B)
                        for (e2, s2, m2) in opt:
                            bp_root, Q = root_strips[e2, s2, m2]
                            pos2 = [q for q, w in enumerate(Q[0]) if w == "S"]
                            ridx2 = run_index(Q[0])
                            if len({ridx2[q] for q in pos2}) < 2:
                                continue
                            bp_rest, Q_rest = rs[e2, s2, m2]
                            A2, R2, v2 = cut(F, Q[0], Q[1], B, o, d, k)
                            t1 = F(*A) <= F(*A2); t2 = bp_rest <= bp_root; t3 = F(*Q_rest) <= F(*R2)
                            stats["mirror_total"] += bp_root + v2 >= v
                            stats["mirror_t1"] += t1; stats["mirror_t2"] += t2; stats["mirror_t3"] += t3
                            stats["mirror_termwise"] += t1 and t2 and t3
                            stats["mirror_checked"] += 1
                            if not (t1 and t2 and t3) and bp_root + v2 >= v and len(examples["mirror_not_termwise"]) < 8:
                                examples["mirror_not_termwise"].append({"word": word, "maxima": list(maxima), "block": sorted(B), "o": o, "d": d,
                                                                        "strip": [e2, s2, m2], "t": [t1, t2, t3],
                                                                        "A": [F(*A), F(*A2)], "e": [bp_rest, bp_root], "rest": [F(*Q_rest), F(*R2)]})
                            break
                        for name, rule in rules.items():
                            stats["rule_" + name] += any(rule(opt, e1, s1, m1, d1, d) for (e1, s1, m1, d1) in dom_two)
                        if not any(rules["same_end_same_side_both_within_1"](opt, e1, s1, m1, d1, d) for (e1, s1, m1, d1) in dom_two) and len(examples["needs_more"]) < 10:
                            examples["needs_more"].append({"word": word, "maxima": list(maxima), "block": sorted(B), "o": o, "d": d, "value": v,
                                                           "rest_opt": sorted(opt), "dominating": sorted(dom, key=str)[:10]})
    out = {"case": args.case, "parameters": vars(args) | {"output": str(args.output)}, "stats": dict(sorted(stats.items())), "examples": examples}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=1, default=list) + "\n")
    print(json.dumps({"case": args.case, **dict(sorted(stats.items()))}), file=sys.stderr)


if __name__ == "__main__":
    main()
