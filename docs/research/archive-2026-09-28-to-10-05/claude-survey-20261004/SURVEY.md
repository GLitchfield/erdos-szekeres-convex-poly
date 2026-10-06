# Survey of combinatorial tools for the lock (MIXED ROOT / BDL), 2026-10-04

Coordinator synthesis of six area surveys and my own probes. Problem statement: `PROBLEM.md`. Area reports:
- `A-erdos-szekeres-literature.md`
- `B-extremal-set-theory.md`
- `C-posets-tableaux.md`
- `D-existence-methods.md`
- `E-oriented-matroids.md`
- `F-substitution-automata.md`

Scripts and outputs are next to the reports and in `probes/`. Every computation is diagnostic, not Lean.

## Bottom line

**No known tool proves MIXED ROOT off the shelf, and the survey produced no proof idea for it.** What it did produce:

- **A sharper statement of the obstacle,** reached independently from three directions (§1).
- **Two exact reformulations of Theorem 8 that need no choice** (§2). Both appear to hold for *general* signotopes,
  so they are Erdős–Szekeres-strength and do not by themselves exploit decomposability.
- **A clear verdict on each family of generic tools** (§3). Every canonical or generic mechanism tested works on B
  alone and fails exactly at the mixed root.
- **Concrete next tests for the surviving leads** (§4). Baek's a = 4 technique was checked and does not transfer.
  Purity (Gavin's add-a-point route) was tested and holds
  in its easy half only.

**Current proof idea for the target:** none. The obstacle every attempt hits is the same as before (§1).

## 1. What the survey established about why the lock is hard

1. **The canonical layering fails only at "overfull" points.** This is the Erdős–Szekeres 1935 endpoint argument,
   iterated, as used by Baek–Balko for split k-gons (SoCG 2025, LIPIcs 332:13, Thms 4 and 6).
   - **Rule:** band(v) = clamp(cupEnd(v) − 1).
   - **[P, hand proof]** It gives a valid BDL partition unless some point has cupEnd(v) + capEnd(v) ≥ k + 2.
   - **[C]** Exhaustive check on decomposable sets with n ≤ 7: 0 failures without an overfull point, out of 23,286
     cases.
   - **Where overfull points come from:** in a decomposable set they come from Lemma DS, i.e. an A-point extending a
     B-cap. That is the mixed cap of MIXED ROOT.
   - **[C] The repair is not local:** in 386 of 1,778 failures, no minimum repair lies inside the overfull set.
2. **A root split cuts the Boolean window at one level (B).**
   - **[P]** With p = cup A: T(a, p+1, k) + T(k−p, u, k) = T(a, u, k) for k−a < p < u−1. Checked for all k ≤ 12,
     660 cases. So Lemma DS plus induction proves Theorem 8 at every such split. This is the Pascal-window step of
     Baek–Balko's published proof.
   - **The lock is the single degenerate level p = k−a.** There A's share of the window is empty, yet A can hold
     C(k−3, p−1) points, exactly a star of one element in level p of B_{k−2}.
   - **In Boolean terms, MIXED ROOT says: A must displace a star of level p.**
   - **[C]** In the tight corpus, 247 of 345 root splits are exact level cuts; all 98 others are this degenerate cut.
   - **[C]** A one-band star exchange works on all 57 small tight lock splits but fails on cex40 (n = 40). There the
     displacement propagates across several bands.
3. **The choice on A is cheap; the real content is re-partitioning B (D).**
   - **[C]** On configH's hard nodes, the feasible keep/lift vectors depend only on how many A-points are kept, and
     local rules force that count ("≤ 1 kept", "lift all", "exactly one kept").
   - What has no local rule is how B must re-band to make room.
4. **The arithmetic is easy; the difficulty is purely existential (F).**
   - **[C]** The chain type τ (longest cup and cap on every x-interval, plus strong) is an exact composition
     congruence that does not depend on k, with few reachable states.
   - Theorem 8 itself is a statement about τ; BDL is not.
   - **[C]** Witness states for "a band partition exists" do not compress: one state per colouring.

**Synthesis.** The obstacle has the same shape from every angle. At the degenerate level, B must lose |A| points of
capacity, and the loss must be routed through B's bands by a global re-partition. Generic existence tools need some
local or lattice structure at exactly this point (pairwise conflicts, absorbing classes, lattice polymorphisms,
integrality, high connectivity), and the band families have none of it.

## 2. Choice-free reformulations

- **SH (canonical labels plus one matching).**
  - **Statement:** every Moshkovitz–Shapira label D(v) that lies outside the window can be matched to a distinct
    UNUSED window label contained in it.
  - SH implies Theorem 8, because D is injective and the window holds exactly T labels.
  - **[C]** It held on:
    - all decomposable sets with n ≤ 8 (118,536 cases with overfull points);
    - all 1,932 stored hard instances, including tight n = 14, 15, 25 with up to 10 overfull points;
    - X14;
    - random tight general signotopes.
  - **Limits:** the matching is not forced (712 of 776 tight cases have several), so no canonical fold map emerges.
    SH appears to be ES-strength.
  - **Why it is hard:** no strong k-set gives a *staircase* bound on (cup, cap) per start point, which yields only a
    Catalan count. The window needs a *box* bound on (cupEnd, capEnd). That gap is the Erdős–Szekeres difficulty
    itself.
- **Earlier choice-free targets** (Q12: Φ ≥ 0, densities, numeric PSL) belong to the same class.

## 3. Tool-by-tool verdicts (details in the area files)

| Tool | Verdict | Why |
|---|---|---|
| Suk / HMPT, FPSS, Eliáš–Matoušek, Szekeres–Peters | no | asymptotic, or no window; HMPT's gluing is Lemma DS, but nothing is chosen |
| Moshkovitz–Shapira labels | language | the bijection behind C(a+u−4, a−2); BDL = graded MS labelling; ignores the strong bound |
| Shifting / compression | no | about 21% of adjacent swaps raise cup, cap or strong; it is the failed rectification |
| Kruskal–Katona, LYM, Sperner, Harper | no | no intrinsic rank meets the level capacities (at most 109/345 tight sets) |
| Symmetric chain decompositions (BTK step) | template | the lock is the BTK step at level p; untested beyond the star form |
| Greene–Kleitman, Gansner, Frank, RSK/Schensted | no | saturation fails (witness n = 8); needs binary-relation chains |
| Mirsky window band ∈ [cupEnd−1, k−1−capEnd] | **refuted** | holds for n ≤ 7, fails on 13/1,116 configH sets (n = 21) |
| Scarf, fractional kernels | no | gives only the fractional partition (X14 has one); integrality is the content |
| Galvin kernel peel | **refuted at the lock** | bottom-peel holds on all 25 hard B, fails at 4/4 mixed roots |
| Gale–Shapley / deferred acceptance | partial | covers all hard B; at the mixed root at least one point stays unmatched for every A-priority |
| Topological Hall, Sperner/parity, Borsuk–Ulam | no | connectivity hypothesis false already at n = 6; no parity invariant |
| Combinatorial Nullstellensatz, Alon–Tarsi | no | degree 1.3–8.8× too high; coefficient vanishes on feasible sets |
| Entropy, containers, flag algebras | no | o(1) slack |
| Substitution decomposition, dendriform, WQO, kernel method | no | simple pieces unbounded; << is not associative; BDL not hereditary |
| Tree automata, MSO, regular cost functions | diagnostic | finite for each k, so says nothing; cost functions cannot tell T from 2T |
| Higher Bruhat orders, wiring diagrams | language | split = parabolic-type interval ≅ B(\|L\|,2)×B(\|U\|,2); no new invariant |

## 4. Ranked leads, each with its next test and decision rule

1. **Baek's exact a = 4 technique: checked 10-04, no transfer.** Source: "On the Erdős–Tuza–Valtr conjecture",
   EJC 124 (2025) 104085, arXiv:2206.04260 v2, read via HTML.
   - **Setting:** abstract configurations and weak gons.
   - **Induction on n:**
     - Δ = the leftmost point of each row of the (α,β)-plane, i.e. n−2 points.
     - S∖Δ has no (n−1)-cup.
     - The inductive interweaved laced (n−2)-cups are extended on the left by the Δ-points.
   - **So it is a canonical peel,** the kind of rule SAT already excludes for larger a. The author states it fails to
     extend beyond a = 4: it uses mirror symmetry and applies the inductive hypothesis twice, with only two label
     values. Its Conjecture 5 for a > 4 is open.
   - Our Lean a = 4 and a = 5 gates already go further for decomposable sets. Dropped.
2. **Purity / saturation (Area E; Gavin's add-a-point route): tested 10-04.**
   - **Background (Damásdi–Dong–Scheucher–Zeng, EJC 131, 2026, arXiv:2312.01223):**
     - the Erdős–Szekeres construction is saturated;
     - point sets have smaller saturated sets: (7/8)·2^{n−2} for convex n-gons with n ≥ 7, and sat_c(4,5) = 8 < 10
       for cups versus caps;
     - for abstract ordered hypergraphs, saturation equals the Ramsey number, proved with Moshkovitz–Shapira labels.
   - **[C] Result:** exhaustive over all decomposable sets with |X| ≤ 8, using restrictions of all 3,816,380
     decomposable colourings with n = 9 (job 20261004-091440-5dc49c, `probes/purity2_n9.out`). **0 violations.**
     Every set with no a-cap, no u-cup and no strong k-set, and fewer than T(a,u,k) points, has a one-point
     decomposable extension within the same limits, for every (a,u,k).
     - So the decomposable class has no small saturated sets in this range, unlike point sets (sat_c(4,5) = 8 there).
   - **Meaning for the add-a-point route:**
     - Theorem 8 is equivalent to "every TIGHT set is saturated", for all tight sets, not only the ES construction.
     - Purity (all saturated sets have equal size) plus "the ES construction is saturated" would give Theorem 8. Its
       remaining half, "saturated ⇒ ≤ T", is Theorem 8 itself, so purity helps only if an exchange-type argument
       proves it. None is in sight, and the constrained families are not matroids.
   - **Verdict:** a structural fact worth recording; not a route.
3. **Star displacement through bands (B; the SCD / BTK step): tested 10-04, closed.**
   - **Probe:** `probes/star_flow.py`, run on the 30 keep-failing cex40 placements with a 4-point A.
   - **Result:** relative to the best valid partition of B, the minimum number of B-points that must change band is
     **0** at every placement (5 optimal solutions each). A goes to bands (2,3,3,3) or (3,3,3,3), i.e. lifted to
     p+1, and B is unchanged.
   - **Meaning:** no multi-band displacement is needed once B's partition is chosen with A in view. The star form
     fails, but the lift form exists.
   - **Consequence:** the content is choosing B's partition knowing A's cut positions. That is the ZLOCK / two-sided
     tower existence statement (lift iff band p+1 has no (β−1)-cap ending before z and none starting after z), not
     a new flow structure. The SCD template is not needed.
4. **Deficiency counting at the lock, without partitions.**
   - **Statement:** if A sits in the core of B's β-caps, then |B| ≤ T − |A|.
   - This is what Theorem 8 needs at the lock. It is the old context-bound / kill-set route, which was exact on
     single-gate profiles and failed on multi-gate ones.
   - **Test:** compute the exact maximum |B| with a given gap set by SAT, for small k. Check whether the deficiency is
     a submodular function of the gap set.
   - **Decision rule:** if it is submodular, the multi-gate failure becomes a rank-function question with
     polymatroid tools; if not, drop.
5. **Potential on τ (F) / learned all-k invariants (F).**
   - The most direct attack on uniformity in k, but costly, and the earlier context-bound statistic was one such
     potential and failed.
   - Lowest priority.

Dropped by this survey:
- shifting, LYM-type, kernel and topological approaches;
- substitution and WQO approaches;
- the one-band star exchange and the Mirsky window (refuted);
- linear-algebra dimension bounds (B's second lead). They have no candidate vectors, and I know of no
  linear-algebra proof even of the classical cups–caps bound.

## 5. Evidence

- **Probes (`probes/`):**
  - `split_layering.py`: overfull points and repairs;
  - `ms_labels.py`: MS labels on tight sets;
  - `ms_shrink_hall.py`: SH up to n ≤ 8 (job 20261004-090448-adf53e);
  - `ms_shrink_hard.py`, `ms_shrink_general.py`, `ms_shrink_unique.py`;
  - `purity2.py` (job 20261004-091440-5dc49c; output `purity2_n9.out`);
  - `star_flow.py`;
  - `ms_shrink_hall_n8.out`.
- **Area scripts:**
  - `F_t*.py`;
  - `d_*.py` with outputs `o_*.txt`;
  - `b_tests/`;
  - `C/`.
  - E's scripts were in /tmp and are lost.
