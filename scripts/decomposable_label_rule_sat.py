#!/usr/bin/env python3
"""Label sets as a function of context features, by SAT (note 0123).

Variables w[phi, x]: label x (a string over {L,U} of length k-2) belongs to the label set
of every context with feature vector phi.  Constraints, over all contexts reachable from
the root (a, u, k) with s child letters by any partition, orientation and coupling:

  leaf (one child letter, positive limits): its label set is nonempty;
  split sigma -> (A, R): L(A) and L(R) are disjoint and both inside L(sigma);
  root: at most T(a, u, k) labels (or the given --colors).

--features chooses phi:
  context : the whole (word, maxima)            (the bare label-set conjecture)
  limits  : (number of child letters, cl, pl)   the run limits of single-run contexts,
            and the whole context otherwise
  sides   : limits plus the sides of the levels (innermost first)
  maxima  : sides plus the sibling maxima
  word    : limits plus the whole word (positions and sides), but not the maxima
SAT exhibits a rule; UNSAT says the labels must depend on more than phi.
"""
from __future__ import annotations

import argparse
import itertools
import json
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decomposable_depth2_tables import limits_from_signature  # noqa: E402
from decomposable_label_coloring import build, CADICAL, fmt  # noqa: E402
from decomposable_recursive_formula import T  # noqa: E402


def features(ctx, a, u, k, mode):
    word, maxima = ctx
    if mode == "context":
        return ctx
    p, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
    n = sum(1 for w in word if w == "S")
    if p != 1:
        return ("multi",) + ctx
    cl, pl = int(cup_limit[0][0]), int(cap_limit[0][0])
    base = (n, cl, pl)
    side_at = {}
    for w in word:
        if w != "S":
            side_at[w[0]] = w[1]
    if mode == "limits":
        return base
    if mode == "word":
        return base + (word,)
    if mode in ("levels", "flags"):
        first = min(i for i, w in enumerate(word) if w == "S")
        last = max(i for i, w in enumerate(word) if w == "S")
        per = []
        for l in range(1, len(maxima) + 1):
            b = sum(1 for i, w in enumerate(word) if w != "S" and w[0] == l and i < first)
            e = sum(1 for i, w in enumerate(word) if w != "S" and w[0] == l and i > last)
            side = side_at.get(l, "-")
            per.append((side, b, e) if mode == "levels" else (side, b > 0, e > 0))
        return base + (tuple(per),)
    sides = tuple(side_at.get(l, "-") for l in range(1, len(maxima) + 1))
    if mode == "sides":
        return base + (sides,)
    return base + (sides, tuple(maxima))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", required=True)
    ap.add_argument("--s", type=int, default=4)
    ap.add_argument("--colors", type=int, default=None)
    ap.add_argument("--features", choices=("context", "limits", "sides", "maxima", "word", "levels", "flags"), default="context")
    ap.add_argument("--root-window", action="store_true",
                    help="pin the root's label set to the canonical window (fixed trailing U's in the choose regime)")
    ap.add_argument("--exact", action="store_true",
                    help="single-run contexts get exactly their threshold value many labels")
    ap.add_argument("--exact-max-levels", type=int, default=None,
                    help="with --exact: only contexts with at most this many levels")
    ap.add_argument("--tight", action="store_true",
                    help="single-run contexts get at most their threshold value many labels")
    ap.add_argument("--any-cylinder", action="store_true",
                    help="with --cylinders: allow any cylinder with budgets at most the limits and any fixed positions")
    ap.add_argument("--single", action="store_true", help="with --cylinders: exactly one cylinder per class")
    ap.add_argument("--prefix", action="store_true", help="with --cylinders: fixed positions are a prefix 0..f-1")
    ap.add_argument("--tight-budgets", action="store_true", help="with --cylinders: budgets equal cl-1, pl-1")
    ap.add_argument("--rule", choices=("inner", "outer", "near", "far", "free"), default=None,
                    help="with --cylinders: force the fixed prefix letters to the sides of the levels in this order "
                         "(inner = level 1 first; outer = highest level first; near = level whose letter is nearest the run first; far = farthest first), tight budgets")
    ap.add_argument("--pad", default="L", help="with --rule: letter used when more fixed positions than levels")
    ap.add_argument("--backbone", type=Path, default=None,
                    help="with --rule free: for every single-run class test each letter tuple (forced true) and write the feasible ones")
    ap.add_argument("--cylinders", action="store_true",
                    help="every single-run context's set is a tight cylinder: fixed letters on f = max(0, m-(cl-1)-(pl-1)) "
                         "positions chosen by the solver, #L(free) <= cl-1, #U(free) <= pl-1")
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    a, u, k = (int(x) for x in args.case.split(","))
    m = k - 2
    nlab = 1 << m
    colors = args.colors or T(a, u, k)
    started = time.time()
    contexts, splits, leaves, dead = build(a, u, k, args.s, True)
    phi_index = {}
    phi_of = []
    for ctx in contexts:
        phi = features(ctx, a, u, k, args.features)
        if phi not in phi_index:
            phi_index[phi] = len(phi_index)
        phi_of.append(phi_index[phi])
    nphi = len(phi_index)
    def w(f, x): return 1 + f * nlab + x
    clauses = []
    for c in leaves:
        clauses.append([w(phi_of[c], x) for x in range(nlab)])
    seen = set()
    for (i, ia, ir) in splits:
        key = (phi_of[i], phi_of[ia], phi_of[ir])
        if key in seen:
            continue
        seen.add(key)
        fi, fa, fr = key
        for x in range(nlab):
            clauses.append([-w(fa, x), w(fi, x)])
            clauses.append([-w(fr, x), w(fi, x)])
            clauses.append([-w(fa, x), -w(fr, x)])
    extra_vars = [nphi * nlab]      # counter for auxiliary variables
    def newvar():
        extra_vars[0] += 1
        return extra_vars[0]
    cylinder_choice = {}            # feature class -> list of (P, Q, var)
    if args.cylinders:
        seen_phi = set()
        for i, ctx in enumerate(contexts):
            f_ = phi_of[i]
            if f_ in seen_phi:
                continue
            seen_phi.add(f_)
            word, maxima = ctx
            p_, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
            if p_ != 1:
                continue
            cl, pl = int(cup_limit[0][0]), int(cap_limit[0][0])
            if min(cl, pl) < 1:
                for x in range(nlab):
                    clauses.append([-w(f_, x)])
                continue
            ell, ups = cl - 1, pl - 1
            fx = max(0, m - ell - ups)
            choices = []
            shapes = []
            if args.rule:
                side_at = {}
                first = min(i_ for i_, w_ in enumerate(word) if w_ == "S")
                last = max(i_ for i_, w_ in enumerate(word) if w_ == "S")
                dist = {}
                for i_, w_ in enumerate(word):
                    if w_ != "S":
                        side_at[w_[0]] = w_[1]
                        d_ = first - i_ if i_ < first else i_ - last
                        dist[w_[0]] = min(dist.get(w_[0], 10 ** 9), d_)
                levels_ = sorted(side_at)
                if args.rule == "inner":
                    order = levels_
                elif args.rule == "outer":
                    order = levels_[::-1]
                elif args.rule == "near":
                    order = sorted(levels_, key=lambda l_: (dist[l_], l_))
                else:
                    order = sorted(levels_, key=lambda l_: (-dist[l_], l_))
                if args.rule == "free":
                    letter_options = list(itertools.product("LU", repeat=fx))
                else:
                    letters = [("L" if side_at[l_] == "lower" else "U") for l_ in order][:fx]
                    letters += [args.pad] * (fx - len(letters))
                    letter_options = [tuple(letters)]
                P = tuple(range(fx))
                free = m - fx
                for letters in letter_options:
                    bits = tuple(1 if c_ == "L" else 0 for c_ in letters)
                    members = set()
                    for x in range(nlab):
                        if any(((x >> pos) & 1) != b for pos, b in zip(P, bits)):
                            continue
                        nL = sum((x >> pos) & 1 for pos in range(m) if pos not in P)
                        nU = free - nL
                        if nL <= ell and nU <= ups:
                            members.add(x)
                    v = newvar()
                    choices.append((P, bits, v, members))
                clauses.append([v for _, _, v, _ in choices])
                for i1 in range(len(choices)):
                    for i2 in range(i1 + 1, len(choices)):
                        clauses.append([-choices[i1][2], -choices[i2][2]])
                for x in range(nlab):
                    ins = [v for _, _, v, mem in choices if x in mem]
                    clauses.append([-w(f_, x)] + ins)
                    for v in ins:
                        clauses.append([-v, w(f_, x)])
                cylinder_choice[f_] = choices
                continue
            if args.any_cylinder:
                for f2 in range(fx, m + 1):
                    for e2 in range(ell + 1):
                        for u2 in range(ups + 1):
                            if args.tight_budgets and (e2, u2) != (ell, ups):
                                continue
                            shapes.append((f2, e2, u2))
            else:
                shapes.append((fx, ell, ups))
            seen_members = set()
            for (f2, e2, u2) in shapes:
                free = m - f2
                for P in itertools.combinations(range(m), f2):
                    if args.prefix and list(P) != list(range(f2)):
                        continue
                    for bits in itertools.product((0, 1), repeat=f2):
                        members = set()
                        for x in range(nlab):
                            if any(((x >> pos) & 1) != b for pos, b in zip(P, bits)):
                                continue
                            nL = sum((x >> pos) & 1 for pos in range(m) if pos not in P)
                            nU = free - nL
                            if nL <= e2 and nU <= u2:
                                members.add(x)
                        key = frozenset(members)
                        if not members or key in seen_members:
                            continue
                        seen_members.add(key)
                        v = newvar()
                        choices.append((P, bits, v, members))
            clauses.append([v for _, _, v, _ in choices])          # at least one cylinder chosen
            if args.single:
                for i1 in range(len(choices)):
                    for i2 in range(i1 + 1, len(choices)):
                        clauses.append([-choices[i1][2], -choices[i2][2]])
            for x in range(nlab):
                # w[f,x] <-> OR of chosen cylinders containing x
                ins = [v for _, _, v, mem in choices if x in mem]
                clauses.append([-w(f_, x)] + ins)
                for v in ins:
                    clauses.append([-v, w(f_, x)])
            cylinder_choice[f_] = choices
    if args.exact:
        seen_phi = set()
        for i, ctx in enumerate(contexts):
            f_ = phi_of[i]
            if f_ in seen_phi:
                continue
            seen_phi.add(f_)
            word, maxima = ctx
            p_, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
            if p_ != 1:
                continue
            cl, pl = int(cup_limit[0][0]), int(cap_limit[0][0])
            cap = 0 if min(cl, pl) < 1 else (1 if min(cl, pl) == 1 else T(pl + 1, cl + 1, k))
            n_ = sum(1 for w_ in word if w_ == "S")
            cap = min(cap, n_)           # a context with n child letters holds at most n vertices
            if args.exact_max_levels is not None and len(maxima) > args.exact_max_levels:
                continue
            if cap < nlab:
                for sub in itertools.combinations(range(nlab), cap + 1):
                    clauses.append([-w(f_, x) for x in sub])
            if cap > 0:
                for sub in itertools.combinations(range(nlab), nlab - cap + 1):
                    clauses.append([w(f_, x) for x in sub])
    if args.tight:
        seen_phi = set()
        for i, ctx in enumerate(contexts):
            f_ = phi_of[i]
            if f_ in seen_phi:
                continue
            seen_phi.add(f_)
            word, maxima = ctx
            p_, cup_limit, cap_limit = limits_from_signature(word, maxima, a, u, k)
            if p_ != 1:
                continue
            cl, pl = int(cup_limit[0][0]), int(cap_limit[0][0])
            if min(cl, pl) < 1:
                cap = 0
            elif min(cl, pl) == 1:
                cap = 1
            else:
                cap = T(pl + 1, cl + 1, k)
            if cap < nlab:
                for sub in itertools.combinations(range(nlab), cap + 1):
                    clauses.append([-w(f_, x) for x in sub])
    # root cardinality: at most `colors` labels
    froot = phi_of[0]
    if args.root_window:
        free = min(m, a + u - 4)
        fixed = m - free
        for x in range(nlab):
            nL = bin(x & ((1 << free) - 1)).count("1")
            nU = free - nL
            trailing_ok = (x >> free) == 0          # fixed positions carry U
            inside = trailing_ok and nL <= u - 2 and nU <= a - 2
            clauses.append([w(froot, x)] if inside else [-w(froot, x)])
    elif colors < nlab:
        for sub in itertools.combinations(range(nlab), colors + 1):
            clauses.append([-w(froot, x) for x in sub])
    nvars = extra_vars[0]
    if args.backbone:
        import subprocess as sp
        base_path = Path(tempfile.mkdtemp()) / "base.cnf"
        body = "".join(" ".join(map(str, cl)) + " 0\n" for cl in clauses)
        feasible = {}
        forced = {}
        done = 0
        started_bb = time.time()
        inv_phi = {f_: phi for phi, f_ in phi_index.items()}
        for f_, choices in cylinder_choice.items():
            phi = inv_phi[f_]
            n_, cl_, pl_, word_ = phi
            wd = "".join("S" if w_ == "S" else f"{w_[0]}{'L' if w_[1] == 'lower' else 'U'}" for w_ in word_)
            feas = []
            for P, bits, v, members in choices:
                letters = "".join("L" if b else "U" for b in bits)
                with open(base_path, "w") as fh:
                    fh.write(f"p cnf {nvars} {len(clauses) + 1}\n")
                    fh.write(body)
                    fh.write(f"{v} 0\n")
                proc = sp.run([str(CADICAL), "-q", str(base_path)], capture_output=True, text=True)
                if proc.returncode == 10:
                    feas.append(letters)
                done += 1
            key = f"{wd}|{cl_}|{pl_}"
            feasible[key] = feas
            if len(feas) == 1:
                forced[key] = feas[0]
        out = {"case": args.case, "s": args.s, "classes": len(feasible), "forced": len(forced),
               "solves": done, "seconds": round(time.time() - started_bb, 1), "feasible": feasible}
        args.backbone.write_text(json.dumps(out, indent=1) + "\n")
        print(json.dumps({k_: v_ for k_, v_ in out.items() if k_ != "feasible"}))
        return
    path = Path(tempfile.mkdtemp()) / "rule.cnf"
    with open(path, "w") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")
    proc = subprocess.run([str(CADICAL), "-q", str(path)], capture_output=True, text=True)
    sat = proc.returncode == 10
    if proc.returncode not in (10, 20):
        raise RuntimeError(proc.stderr[-500:])
    result = {"case": args.case, "s": args.s, "features": args.features, "colors": colors, "threshold": T(a, u, k),
              "contexts": len(contexts), "feature_classes": nphi, "leaves": len(leaves), "clauses": len(clauses),
              "sat": sat, "seconds": round(time.time() - started, 1)}
    print(json.dumps(result), flush=True)
    if args.output and not sat:
        args.output.write_text(json.dumps(result, indent=1) + "\n")
    if sat and args.output:
        pos = set()
        for line in proc.stdout.splitlines():
            if line.startswith("v "):
                pos.update(int(t) for t in line[2:].split() if t != "0" and int(t) > 0)
        def lab(x): return "".join("L" if x >> i & 1 else "U" for i in range(m))
        sets = {}
        for phi, f in phi_index.items():
            labels = [lab(x) for x in range(nlab) if w(f, x) in pos]
            key = fmt(phi[0]) + "|" + ",".join(map(str, phi[1])) if args.features == "context" else json.dumps(phi, default=str)
            sets[key] = labels
        result["label_sets"] = sets
        if cylinder_choice:
            chosen = {}
            for phi, f_ in phi_index.items():
                if f_ in cylinder_choice:
                    picks = [(P, "".join("L" if b else "U" for b in bits)) for P, bits, v, _ in cylinder_choice[f_] if v in pos]
                    chosen[json.dumps(phi, default=str)] = picks
            result["cylinders"] = chosen
        args.output.write_text(json.dumps(result, indent=1, default=str) + "\n")


if __name__ == "__main__":
    main()
