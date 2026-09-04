# Brief for Sol: the Erdős–Tuza–Valtr case with cap parameter 5

Workstream C of `research-plan-2026-09-03.md`.  Standing mathematical problem,
six-week timebox from the day it is handed over, with a written state of the
argument every week.  Draft prepared 4 September 2026 for Gavin to send.

## The problem

Erdős, Tuza, and Valtr define numbers that simultaneously avoid an `n`-gon, an
`a`-cap, and a `b`-cup, and conjecture an exact binomial-sum formula for them.
Their family of statements is equivalent to the Erdős–Szekeres conjecture
through a monotone implication scheme, so each proved case is progress on the
destination itself.  Baek proved the first genuinely new case, cap parameter
4, in 2025 and formalized it in Lean 4
(<https://github.com/jcpaik/erdos-tuza-valtr>, Apache-2.0).

The target for this workstream is the next value:

> For every `n ≥ 5`, every set of `decomposableThreshold 5 n n + 1` points in
> general position contains a 5-cap, an `n`-cup, or a convex `n`-gon.

`decomposableThreshold` is defined in `ErdosSzekeres/Decomposable.lean`
(line 245): with `a = 5`, `u = n`, `k = n` it is the Pascal window
`∑_{j = n-5}^{n-2} C(n-2, j)`, so the first values are

| n | threshold + 1 |
|---|---|
| 5 | 9 (this is ES(5), proved) |
| 6 | 16 |
| 7 | 27 |
| 8 | 43 |

Parameter 4 was proved by an elementary combinatorial argument in which the
cap size is used concretely; the project's audit (ticket 0106) found the cap
size hard-coded in the source mechanism it examined.  Parameter 5 is the first
open value, and the first where the interaction between short caps and the
polygon becomes non-trivial.  This is the one workstream where a new idea would
be a real theorem rather than evidence for one.

## What to do, in order

1. **Read Baek's proof from the Lean code, not the paper.**  Ticket 0106
   could not authenticate a final primary text of either the 1996 ETV article
   or the 2025 paper, but the Lean development is the proof.  Clone it
   read-only next to `EmptyHexagonLean`, find `theorem main` and the cup–cap
   theorem, and write down every lemma with the exact place the number 4
   enters.  Deliverable: a one-page lemma ladder for parameter 4.
2. **Write the parameter-5 analogue of every lemma** and find the first one
   that fails.  That lemma, stated precisely with the smallest configuration
   that breaks it, is the week-1 deliverable.  Do not patch around it yet.
3. **Compute the exact numbers at small `n` before theorizing.**  Done for
   `n = 6` on 4 September (experiment 0112): the signotope-tier number is
   exactly 16, so the parameter-5 case holds at `n = 6`, and the 15-point
   extremal coloring is in `data/derived/etv-signotope-n6-a5-b6.json`.  The
   encoding reproduced the cup–cap (4,4) number, ES(5), and Baek's (6,4,6)
   before it was trusted.  At `n = 7` (Tseitin encoding, unanchored) 26 points
   are satisfiable with a checked coloring, so the signotope number is at
   least the conjectured 27; the 27-point refutation did not finish in three
   hours of CaDiCaL and needs cube-and-conquer.  At the
   signotope tier (triple colorings with the four-index one-change law) the
   instance for `N` points is: variables the increasing triples; clauses the
   one-change law on every four indices; for every 5-subset, not all ten
   triples right turns (no 5-cap); for every `n`-subset, not all triples left
   turns (no `n`-cup); for every `n`-subset, not a strong set (no convex
   `n`-gon).  The largest satisfiable `N` plus one is the signotope-tier
   number; compare it with the table above and extract the extremal
   colorings.  `n = 6` is minutes of solver time; `n = 7` needs the Tseitin
   encoding in `scripts/generate_etv_tseitin_sat.py` (strong-set and cup
   hierarchies; validated against the same gates).  Do **not** use the
   anchoring normalization of `AnchoredPresentation.lean` here: it preserves
   strong sets and the one-change law, which is all the ES(6) certificate
   needed, but a projective re-indexing does not preserve which chains are
   caps or cups, so anchored cap/cup instances are unsound (an anchored
   26-point instance came back UNSAT on 4 September, which would contradict
   the formula; unanchored is the only valid form).  Signotope numbers bound
   the planar ones from above; if they disagree with the table, say which
   tier the disagreement lives in.
4. **State the falsifier before any proof attempt.**  The cheap one: a
   realizable configuration of `threshold + 1` points with no 5-cap, no
   `n`-cup, and no convex `n`-gon at some `n ≤ 8`, found by the same solver
   with the realizability check of experiment 0108's tooling.  The structural
   one: the first failing lemma from step 2 restated as a concrete family of
   configurations.

## Rules for this workstream

- Planar or realizable-order-type tier only.  Anything proved at the abstract
  signotope tier must carry the realizability hypothesis or be flagged.
- No Lean until the statement has a parameter in it, a named consumer in the
  tree (`decomposableThreshold` and `SweepExactUpperAt` are the candidates),
  and a falsifier that has already been run.  Baek's configuration API is the
  leading reuse candidate; audit its toolchain before depending on it.
- Every Lean build goes through `scripts/guarded_lake_build.sh`; no solver run
  outside a `systemd-run --user --scope -p MemoryMax=…` cgroup.  See
  `docs/plans/weekly-plan-2026-09-03.md` for the incident that made this a
  rule.
- No `sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound`,
  and `native_decide` only under the guarded `make test` path.
- A negative result is one paragraph in the weekly note, not a ticket.

## Weekly state of the argument (format)

One page, every Friday, in `docs/plans/etv-parameter-5-week-N.md`:

1. Lemma ladder status: which parameter-5 analogues are proved, which fail,
   and the current first failure.
2. The candidate mechanism, stated with its parameter.
3. Falsifier status: what was run, what survived.
4. Numbers: any new exact value or extremal configuration.
5. What would make you stop early.

## Stop condition

At six weeks, one of: a parameterized partial result (for example the
parameter-5 case for all `n ≤ n₀` by a uniform argument, or a lemma ladder
with exactly one missing rung stated precisely), or a written obstruction that
explains why the parameter-4 argument does not lift and what a different
argument would need.  Either is a deliverable; continuing past the timebox
without one is not.
