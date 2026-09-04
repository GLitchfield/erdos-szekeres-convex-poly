# Outline: a formalization paper on the Erdős–Szekeres problem in Lean 4

Workstream G, first deliverable of Weeks 2–4 of `research-plan-2026-09-03.md`.
Drafted 4 September 2026.  Target venue: ITP or CPP (the plan's estimate);
the contribution is the verified development and its certificate pipeline,
independent of what happens to the conjecture.  Every theorem named below
compiles today on `main`; names are the Lean identifiers.

## 1. Introduction

- The happy-ending problem and the exact conjecture `ES(k) = 2^(k−2) + 1`;
  what is known (exact through `k = 6`, Suk's `2^(k+o(k))`, HMPT's
  `2^(k+O(√(k log k)))`); what a formalization contributes: one model in
  which the exact cases, the lower construction, and the asymptotic bounds
  are stated and proved on the same definitions, plus a certificate pipeline
  that scales to seven-hundred-thousand-variable refutations.
- Contributions list (one line each): the planar statement and sweep
  bridge; exact `ES(3)`–`ES(6)`; the all-`k` lower bound; Tóth–Valtr, Suk,
  HMPT; the decomposable class with its realization lemma and kernel-checked
  exact cases; the fixed-six predecessor-half theorem; the anchoring
  normalization; the checkpointed LRAT pipeline; the trust surface.

## 2. The planar statement and the sweep model

- `ForcesConvexPolygon n N`, `HasSharpnessExample n N`,
  `ErdosSzekeresFormulaAt n` (`Basic.lean`): convex position via convex
  hulls over `ℝ²`, general position, no combinatorial shortcut in the
  statement.
- Swept configurations, triple colorings, the one-change (rank-three
  signotope) law (`Sweep.lean`); `exists_sweptPresentation`
  (`Presentation.lean`) and
  `containsConvexSubset_iff_exists_isStrongPolygonOn` (`StrongPolygon.lean`):
  convex position of a subset is exactly a strong set of the coloring.
- What the model does not do: it is a sweep model, not an order-type model;
  the anchoring lemma (§6) is where projective freedom enters.

## 3. Exact small cases

- `erdosSzekeresFormulaAt_three`, `_four` (`SmallCases.lean`): elementary.
- `erdosSzekeresFormulaAt_five` (`ES5Certificate.lean`): 84 variables, 2,016
  clauses, one committed LRAT trace, a compiling bridge from every clause to
  the sweep axioms.
- `erdosSzekeresFormulaAt_six` (`ES6Certificate.lean`): the project's own
  certificate, no external axiom; 680 variables, 217,176 clauses; refuted in
  five minutes after anchoring; 59,684-clause dependency core replayed
  through 192 kernel checkpoints (§6, §7).  Axioms: `propext`,
  `Classical.choice`, `Quot.sound`.

## 4. The lower bound and the classical upper bounds

- `classical_lower_sharpness` (`Extremal.lean`): the Erdős–Szekeres
  construction as an actual planar sharpness witness of size `2^(n−2)` for
  every `n ≥ 3`, via Pascal-row cup–cap stacking.
- `classical_binomial_upper` (`CupCap.lean`): the cup–cap bound.
- `tothValtr_upper`, `tothValtr_strictly_improves_classical`
  (`TothValtrUpper.lean`): the `−1` improvement, source-authenticated.

## 5. Quantitative bounds

- `suk_explicit_upper` (`SukPositiveFractionExplicitUpper.lean`): a
  concrete bound for every `n ≥ 65` from a conservative formalization of
  Suk's positive-fraction route (region geometry, consecutive raw pools,
  chain-run or antichain-packing dichotomy).
- `hmpt_explicit_upper` (`HMPTExplicitUpper.lean`): for every `n ≥ 3`,
  `2^(n + 32·Nat.sqrt(n·Nat.clog 2 n) + 128)` points force a convex
  `n`-gon; the published `2^(n+O(√(n log n)))` order with an explicit
  constant, on the unchanged carrier.  State plainly that neither is an
  asymptotic improvement.

## 6. The anchoring normalization

- `AnchoredPresentation.lean`: every swept configuration re-indexes so that
  vertex 0 sees every later pair as a right turn, with strong polygon sets
  preserved (quarter turn about the leftmost point, a shear, the Tóth–Valtr
  projective chart); `forcesConvexPolygon_of_anchored`.
- Why it is the right normalization for SAT: it breaks the symmetry that
  made the unbroken seventeen-point instance unsolvable in an hour, and it
  is sound for exactly the constraints that are preserved (strong sets, the
  one-change law) and unsound for caps and cups, a point worth a remark.

## 7. The certificate pipeline

- From CNF to Lean: dependency-core extraction with dense renumbering,
  checkpoint splitting with carry manifests, Mathlib's LRAT checker per
  segment (`lrat_checkpoint_segment`, `lrat_checkpoint_final_segment`),
  semantic clause lemmas connecting propositional atoms to the coloring,
  balanced rejection trees over semantic segments, and the final theorem
  that reads the refutation back as a statement about colorings.
- Engineering facts worth reporting: segment granularity versus memory
  (192 segments at 8–18 GiB each for ES(6); 256 for Fin15); proof-term
  sizes (private oleans of 23 GB and 36 GB for the two certificates); the
  generated-proof shapes that do and do not scale (`rfl` on
  `powersetCard`'s multiset versus case splits; one `absurd` per branch
  versus `simp_all`); a sequential axiom audit (`scripts/AxiomAudit.lean`)
  for developments whose proof terms exceed memory.
- Build discipline: cgroup-guarded builds, one plan driver; reproducibility
  hashes recorded per experiment.

## 8. The decomposable class and the predecessor-half theorem

- The abstract class `IsDecomposableOn` (`Decomposable.lean`), the
  realization lemma `IsDecomposable.isSweepRealizable`
  (`DecomposableRealization.lean`), and the exact cases
  `decomposableExactUpperAt_five`, `_six` with the E3 state certificates.
- The observation that the literal scalar induction of the published
  proof of the decomposable-set theorem does not close at `(4,5,5,1,3)`,
  kernel-checked (`published_induction_boundary_regression`), with the
  theorem nevertheless holding there.  Present as a verified fact about the
  argument, not as a claim about the authors' intended proof; the exhaustive
  small-world tables of Workstream B belong here if they exist by then.
- `PredecessorHalfSubsetAt k` and the doubling consumer
  `sweepExactUpperAt_of_predecessorHalfSubset`; the theorems at
  `k = 4, 5, 6`, the last composed from the ES(6) ceiling and the anchored
  Fin15 certificate (`PredecessorHalfSix.lean`).

## 9. Trust surface

- Axioms: `propext`, `Classical.choice`, `Quot.sound` for every theorem
  named above (audit method: §7).
- `native_decide`: one built module (`CommonAnchorPermutationOrder`),
  labelled finite computational evidence in the tree, not on the path to
  any theorem in this paper; state the audit result explicitly.
- No external axioms; the earlier plan to import the Isabelle/HOL `ES(6)`
  archive was abandoned in favour of §3's own certificate.
- Scale: 10,217 modules, 14 million source lines, almost all generated; 118
  GB of compiled proof terms; what that costs and what Workstream G's
  package split does about it.

## 10. Related formalizations

Baek's Erdős–Tuza–Valtr `(n,4,n)` development in Lean 4; the empty-hexagon
`h(6) = 30` verification; the Isabelle/HOL happy-ending formalizations.
Compare the trust route of each (external checker versus kernel replay).

## 11. What is not claimed

The conjecture is open.  Nothing in the paper depends on the decomposable
route being the way to it, on the predecessor-half conjecture, or on the
Erdős–Tuza–Valtr cases beyond Baek's.

## Open items before drafting

- The Workstream B tables and, if it lands, the profile-carrying theorem.
- A one-paragraph account of the abstract signotope tier versus the planar
  tier, with the anchored cap/cup caution as the worked example.
- Timing tables from `guard.log` for the two certificate builds.
- Decide whether the fixed-six predecessor-half theorem is a section or a
  remark; it is the one result here with no analogue in the literature.
