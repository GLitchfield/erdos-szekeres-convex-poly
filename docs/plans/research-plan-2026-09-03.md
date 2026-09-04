# Erdős–Szekeres research plan (3 September 2026)

What to work on, in what order, and what would make us stop. Written for Gavin, Sol, and whichever agents execute; it assumes the 3 September review (`review-2026-09-03.md`) and the repository at `c74c737`.

## Premise

The destination is unchanged: a compiling proof of `ErdosSzekeresConjecture`. The plan is built around two facts that the review surfaced and that the current ledger does not reflect.

**The ledger's intermediate edges collapse at the critical cardinality.** The doubling consumer uses `PredecessorHalfSubsetAt k` only at `n = 2^(k-2)+1`, where "no strong k-set" is the negation of ES(k); given ES(k-1) the two are equivalent there. `TargetReflectingDecomposableNormalizationAt k` says, unpacked, that whenever a target-free realizable coloring on `n` vertices exists, a target-free decomposable one on `n` vertices exists; given `D-DECOMP` that is ES(k) restated. So neither "route" is a smaller theorem than the destination. What can be smaller is a *mechanism*: a uniform argument that produces the half support, or a descent that produces the decomposable coloring, without knowing whether the input exists. Finite evidence should be aimed at mechanisms, and theorem targets should carry a parameter.

**The decomposable class is thin.** Most pentagon-free 8-point sets are not decomposable in the sweep direction they are given, and three quarters admit no deep-below split at all. The class is still the right place to look for structure (every known extremal construction lives in it), but "push arbitrary sets into it" is not a plan until someone shows a single non-decomposable extremal set being normalized, or shows that a change of sweep direction repairs decomposability.

Everything below is organized so that the next three months produce theorems that exist independently of whether the conjecture falls: exact ES through `n = 6`, the decomposable theorem with a correct proof, an Erdős–Tuza–Valtr case, and either a surviving or a dead predecessor-half conjecture.

## Workstreams at a glance

| Workstream | Deliverable | Effort | Stop when |
| --- | --- | --- | --- |
| **A** Exact six | `erdosSzekeresFormulaAt_six`; `PredecessorHalfSubsetAt 6` decided | 2–4 weeks, mostly compute | done, or the Fin15 instance is SAT with a realizable model (then B/E change) |
| **B** Decomposable theorem | author answer; a correct uniform proof of Theorem 8 in Lean, or a note documenting the gap with the kernel-checked cases | 4–8 weeks | proof compiles for all `(a,u,k)`, or a third independent invariant family fails its all-root gate |
| **C** Erdős–Tuza–Valtr next case | a proof (then formalization) of the case with cap parameter 5, or a documented obstruction | open-ended; timebox 6 weeks | timebox, unless a partial result with a parameter appears |
| **D** Structure of extremal sets | exact censuses: decomposability by direction, half-supports, hull structure at k = 5, 6; tests on Baek–Balko constructions at k = 6, 7 | 1–2 weeks scripting | never; this is the cheap instrument for redirecting B, E, F |
| **E** Predecessor-half conjecture | public statement; survives or dies on constructions and on the Fin15 instance | 1–2 weeks compute after D | a counterexample ends it; survival hands it to F |
| **F** Uniform mechanisms | candidate producers with an all-root gate and a parameter in them | continuous, capped at one slot | never more than one slot; each candidate has a falsifier before code |
| **G** Publication and build hygiene | formalization paper; certificate packages split out of the main build; process cut to what produces theorems | 2 weeks, then maintenance | — |

## Workstream A — Close n = 6 in the project's own model

**Goal.** `ForcesConvexPolygon 6 17` and hence `ErdosSzekeresFormulaAt 6`; then `PredecessorHalfSubsetAt 6` as an unconditional theorem.

**Why.** It is the only destination-level theorem available at low cost, it removes the `StrongSixCardinalityCeiling` hypothesis from the fixed-six composition, and it gives the formalization paper a headline.

1. Pull [EmptyHexagonLean](https://github.com/bsubercaseaux/EmptyHexagonLean) and read `gon_6_theorem` and its encoder. Their orientation variables and 4-point consistency clauses are a signotope encoding; map their clause semantics onto `OneChangeOn` and their `HasConvexKGon` onto `IsStrongPolygonSet`. Their symmetry breaking (a fixed sweep order and a leftmost-point normalization) is what makes 17 points tractable; adopt it rather than the repo's unbroken encodings.
2. Decide the trust route. Fast: accept their `cake_lpr`-checked unsatisfiability as an explicitly labelled external axiom inside a separate module and prove the bridge. Policy-conformant: regenerate their CNF, solve with LRAT output, replay through `lrat_checkpoint_reify`. The Fin13 and state-566 replays were bigger than this one should be. Do the fast route first so the theorem exists, then upgrade.
3. Decide the Fin15 endpoint. Run the corrected 4,823-variable, 62,218-clause instance with no proof logging on several solvers to learn its truth value; this has never been done because every run carried a proof-size cap. If UNSAT, cube on strong-five atoms or on the choice of the 7-point maximum support (the compiled obstruction theorem licenses adding the 7-support/8-exterior structure as clauses), give leaves generous allowances, and replay leaf by leaf. If SAT, extract the model, test it for realizability with the rank-three bracket tools, and go to E.
4. Compose: `predecessorHalfSubsetAt_six_of_cardinalityCeiling_of_middle` with the ceiling from step 2 and the endpoint from step 3. Write the two-line `Nat.le_induction` that turns the base and step into `∀ k, (∀ j ≤ k, PredecessorHalfSubsetAt j) → SweepExactUpperAt k`, and the generic bridge `SweepExactUpperAt k → ForcesConvexPolygon k (2^(k-2)+1)`, both of which are missing.

## Workstream B — Settle the decomposable-set theorem

**Goal.** A correct, uniform, compiling proof of `∀ a u k, DecomposableStateUpper a u k` (Baek–Balko Theorem 8) in the abstract class, or a published note that the literal induction does not close and the theorem is kernel-checked through k = 6.

**Why.** It is the one theorem with a parameter that the project is already most of the way to; it is the natural home of every structural idea developed in August; and the ambiguity about the published proof is a distraction that one email can remove.

1. Write to Baek and Balko now. Include the `(4,5,5,1,3)` arithmetic, the singleton-below-extremal example, the six-point split-gon example showing Theorem 8 is not a corollary of the split theorem, and the census of 652 unclosed rows through k = 12. Ask specifically how children below the Pascal window are handled.
2. Meanwhile, reframe the induction around the phenomenon that breaks it. The boundary failure is an external-endpoint effect: a vertex deep below a subtree extends every cap of the subtree that lies on one side of it, and vertices at different tree levels stack. So the child state has to carry, per vertex, the longest cap and cup that can be attached from outside on each side. Freeze that as the candidate state and run the existing all-root census machinery (186,888 eight-vertex colorings at k = 6, the k = 7 roots) to test whether it is a congruence with a k-only bound before writing any Lean.
3. Whichever proof emerges, formalize it as one parameterized theorem, not as more states. State 567 and `(5,7,8)` are instances; do not spend further certificate budget on them unless a uniform argument needs exactly that base case.
4. If both the authors' argument and the reframed state fail, write the note. The corrected small cases, the realization lemma, and the census are already a paper's worth of verified content.

## Workstream C — The next Erdős–Tuza–Valtr case

**Goal.** Prove that `decomposableThreshold 5 n n + 1` points in general position contain a 5-cap, an n-cup, or a convex n-gon, for every n; formalize it on top of Baek's [erdos-tuza-valtr](https://github.com/jcpaik/erdos-tuza-valtr) development.

**Why.** The ETV family is equivalent to the conjecture as a whole, so each case is progress on the destination itself rather than evidence for it. Baek's case fixed one chain parameter at 4 with an elementary combinatorial argument; 5 is the first open value and is where the interaction between short caps and polygons first becomes non-trivial. This is the one workstream where a new idea would be a real theorem.

1. Read Baek's proof for the parameter-4 case closely and isolate the step that uses 4 (the audit found the cap size hard-coded). Write the parameter-5 analogue of every lemma and find the first one that fails.
2. Compute the exact ETV numbers for parameter 5 at small n by SAT at the signotope tier (through n = 8 or 9 is cheap) and extract extremal colorings; they will show what structure a proof must handle.
3. Give this to Sol as the standing mathematical problem, with a six-week timebox and a weekly written state of the argument.

## Workstream D — Instrument the extremal world

**Goal.** Exact answers to the structural questions the routes silently assume, using the order-type data the project already has and Baek–Balko's constructions.

1. For all 77 pentagon-free 8-point order types: is the sweep coloring decomposable in the given direction; is it decomposable in *some* direction (the finitely many combinatorially distinct sweep directions of the point set); does it admit a top-level deep-below split at all. Same for a sample of the 88,423 hexagon-free 9-point types.
2. Implement Baek–Balko's new extremal constructions (the constructions section of the SoCG paper) at k = 6 (16 points) and k = 7 (32 points). For each: decomposable or not; does it contain a strong-five-free 8-subset (respectively a hexagon-free 16-subset). A 16-point hexagon-free realizable set with no pentagon-free half would settle Fin16 negatively without any SAT, and a 32-point one would kill the predecessor-half conjecture at k = 7.
3. Record, per extremal set, the convex-hull layer sizes, the maximum cap and cup, and the number and location of deep-below splits under all directions. This is the dataset that any proposed uniform mechanism must be checked against first.

## Workstream E — State the predecessor-half conjecture and try to kill it

Conjecture: every set of n points in general position with no convex k-gon contains ⌈n/2⌉ points with no convex (k-1)-gon. It implies the Erdős–Szekeres conjecture by doubling; it is proved for k ≤ 5 and for k = 6, n ≤ 14 at the signotope tier; it is not known from the literature. Publish it as a short note or a MathOverflow question so that other people try to break it. Internally, attack it at k = 6, n = 15, 16 (Workstream A step 3) and at k = 7 on every structured 7-gon-free set of size 25–32 that can be built (Workstream D step 2, plus Horton-type sets and double chains). Survival on all of these earns it one slot in F; a counterexample is a result and ends the route cleanly.

## Workstream F — Uniform mechanisms, one slot, falsifier first

This is where the actual conjecture lives, and it is where August's effort went with nothing uniform to show. Keep exactly one candidate mechanism active at a time, and require three things before any Lean: the exact producer statement with a parameter in it; the smallest hostile world it must survive (from D); and the all-root gate that would refute it. Candidates in order of preference: the external-endpoint-rank state for the decomposable induction (B step 2); a direction-choosing normalization, meaning a proof that some sweep direction makes a target-free set decomposable, if D step 1 shows that holds for all extremal order types at k = 5; and, only if E survives, a half-support producer built from hull layers or from the maximum-support obstruction. Retire the state-578 tree-reservoir family, the transition-Hall family, and the prime-mutation descent unless one of them is reborn as a parameterized statement that passes a gate on the D dataset.

## Workstream G — Publish, and make the build serve the mathematics

- Write the formalization paper now: planar statement and bridge, ES(3)–ES(6), the lower bound, Tóth–Valtr, Suk, HMPT, the decomposable class with its realization lemma and the kernel-checked exact cases, the certificate pipeline. That is an ITP/CPP-scale contribution regardless of what happens to the conjecture, and writing it forces the trust surface to be stated exactly (the three `native_decide` modules, the generated families, the external ES(6) axiom if used).
- Split the ~11,000 generated certificate modules into separately built Lake packages with cached oleans, so that `lake build` of the mathematical development does not time out in `HalfPureSingletonFanFin10ClauseChunk46`. New theorems have been checked only by the language server for two weeks because of this.
- Process: stop the idea generator and scheduler; drop failure genomes, hash-frozen packets, and per-lane proof allowances for exploratory computation; keep the adversarial review, but only on frozen theorem statements and on route retirement. Replace tickets with one weekly plan and one weekly reconciliation per workstream. Keep the six-field proof-movement accounting; it is the part of the process that told the truth.

## The questions, and what each one is for

Tags: **settle now** (an answer is a lookup, an email, or a bounded computation), **theorem target** (a parameterized statement worth months), **conjecture** (state publicly, try to kill), **hold** (do not spend on it until something above changes).

- **Q1 · settle now.** Does Baek–Balko's proof of Theorem 8 handle children below the Pascal window? Ask the authors; the repo's transcription says it does not.
- **Q2 · settle now.** Is the Fin15 endpoint (every 15-point strong-six-free signotope has a strong-five-free 8-subset) true? One unlogged solver run answers it; the kernel proof follows if yes.
- **Q3 · settle now.** Are there extremal k-gon-free sets that are decomposable in no sweep direction? Census over the 77 order types at k = 5. If every extremal type is decomposable in some direction, a direction-choosing normalization becomes a real candidate; if not, retire `D-NORMALIZE` as an edge and keep the decomposable class as a source of structure only.
- **Q4 · settle now.** Do Baek–Balko's new extremal constructions at k = 6 and 7 have (k-1)-gon-free halves? Direct test of E at the sizes that matter.
- **Q5 · theorem target.** `ErdosSzekeresFormulaAt 6` in the project's model (Workstream A).
- **Q6 · theorem target.** `∀ a u k, DecomposableStateUpper a u k` with a uniform proof (Workstream B).
- **Q7 · theorem target.** The ETV case with cap parameter 5 (Workstream C).
- **Q8 · theorem target.** A parameterized structural theorem about deep-below splits: for example, that in any decomposable set the external cap and cup extension ranks of a subtree are bounded by a function of k alone, or that some direction splits every extremal set. Whatever survives D becomes the statement.
- **Q9 · conjecture.** The predecessor-half conjecture (Workstream E).
- **Q10 · conjecture.** Every extremal k-gon-free set is decomposable in some sweep direction. Cheap to test at k = 5 and on every k = 6 example that can be built; if true it is the most promising bridge between the decomposable theorem and the conjecture that anyone has, and if false it closes a route.
- **Q11 · conjecture.** Abstract ES(7) at the signotope tier: do all 33-point `OneChangeOn` colorings contain a strong 7-set? Open, distinct from Balko–Valtr's refutation (which concerns arbitrary triple colorings), and probably a cluster-scale computation. Worth a conversation with Heule's group rather than a local run; a negative answer would be the first place realizability becomes load-bearing for every route in this repository.
- **Q12 · hold.** State 567, state `(5,7,8)`, `PascalTailTwoSideBound 5 6 7`, the two-cap-free-sides bound. Instances of Q6; do not fund separately.
- **Q13 · hold.** Prime-mutation descent, transition-Hall slotting, gap-token conservation, tree reservoirs, Monge energies, tope gatedness, Varchenko nerves, and the rest of the discovery-cycle pool. Each is retained as negative knowledge; none has a parameter or a consumer.
- **Q14 · hold.** Improving the HMPT exponent. State of the art, no evidence of an opening; keep the formalization as an asset.

## Schedule

- **Week 1.** Send the Baek–Balko email (Q1). Stop the generator and scheduler; write the weekly plan. Start the EmptyHexagonLean bridge (A1–A2). Run the unlogged Fin15 solve (Q2). Script the order-type census (Q3) and implement the Baek–Balko constructions (Q4).
- **Weeks 2–4.** Finish `erdosSzekeresFormulaAt_six`. Depending on Q2: cube-and-replay Fin15, or analyze the model. Report D results and decide Q10's status. Sol starts C with Baek's proof; B step 2 census runs against the frozen external-endpoint state. Draft the formalization paper outline.
- **Weeks 5–8.** B: formalize whichever proof of Theorem 8 is available, or write the note. C: weekly state of the argument; stop at the timebox unless a parameterized partial result exists. E: publish the conjecture with the evidence from A and D. Split the certificate packages out of the main build.
- **Weeks 9–12.** One F slot, chosen from what survived D and E. Formalization paper submitted. Reassess the ledger with only parameterized statements on it.

## Working rules

A theorem target must have a parameter, a named consumer already in the tree, and a falsifier that can run before the proof is attempted. Finite certificates are funded only when they close a named base case of a uniform argument or decide a stated conjecture; proof-shrinking, seed changes, and cube refinements are not funded. Computation for truth discovery runs without proof logging and without artificial caps; computation for kernel proofs runs with them. Every negative result is recorded in one paragraph in the workstream's weekly note; the genome apparatus is retired. Reviews by Sol or Fable audit frozen statements and route retirements, and the human decides slates. The proof-movement accounting stays, and "forward" continues to mean that a named parameterized dependency closed.

## What success looks like in three months

At minimum: `ErdosSzekeresFormulaAt 6` compiled; the Fin15 question decided either way; the decomposable theorem either proved uniformly in Lean or documented as a gap with the authors' knowledge; the extremal-structure dataset in the repository with Q3, Q4, Q10 answered exactly; the predecessor-half conjecture public with its evidence; a formalization paper submitted. Good: a proof of the ETV parameter-5 case, or a surviving mechanism in F with a parameter and an all-root gate behind it. The conjecture itself is not a three-month goal, and the plan does not pretend otherwise.

## Sources and dependencies

- Baek and Balko, *The Erdős–Szekeres Conjecture Revisited*, SoCG 2025 (<https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SoCG.2025.13>); JCTA 222 (2026) 106195.
- Subercaseaux, Nawrocki, Gallicchio, Codel, Carneiro, Heule, *Formal Verification of the Empty Hexagon Number*, ITP 2024 (<https://www.cs.cmu.edu/~mheule/publications/ITP24.pdf>); repository <https://github.com/bsubercaseaux/EmptyHexagonLean> (`gon_6_theorem`).
- Baek, <https://github.com/jcpaik/erdos-tuza-valtr>.
- The 3 September review (`review-2026-09-03.md`) and the repository at commit `c74c737`.
