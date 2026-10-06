# ZLOCK (claude-zlock-20261003)

[P] = proved here by hand; [C] = exact computation (pysat or enumeration), diagnostic, not Lean.

**Setting.** ZLOCK is nontrivial only at k = β+2 (lo = 1) [P]: a core point keeps cap X = β, and 1+β ≤ k−1. **So
the audit's lo = 0 repair is vacuous here.** The stay/lift verdicts used below equal direct validity of X = {z}<<B at
all 34,457 pairs with |B| ≤ 7.

## 1. Truth: no counterexample

| corpus (every sub-node, mirror, core gap; ≥ 3 bands) | (B,z) | fails | lift-only |
|---|---|---|---|
| exhaustive \|B\| ≤ 8 | 565,147 | 0 | 0 |
| hard: TDF, osj25, trap14, residue, Q17 corpora | 42,129 | 0 | 4 |
| new {z}<<C samples, k = 6, 7, 8, n ≤ 34 | 16,123 | 0 | 11 |

- Band ≥ 3 is never needed. 2-band B is proved (§4). The 7 trap14 sets are boundary instances with all branches.
- **R25's n = 24 BRL+ counterexample** (the C of g657n25d1-32): ZLOCK holds at all 9 core gaps, with only lift at
  gaps 7–10 (re-checked with the audit's code).

**Where lift is needed.**
- **Mixed classes (R25's terms).** No z is non-mixed (lift would be free [P]). 21,914 z are mixed on one side, and
  stay always works there. 29,475 z are mixed on both sides, i.e. the X-core is degenerate at z; all 15 lift-only
  pairs are among these.
- **Every lift-only X is tight** (|X| = T(6,5,7) = 25). In a tight X, band 1 is a full maximum β-cap [P]. So stay ⟺
  that cap can be the **mixed** cap through z, and lift ⟺ it is a **pure** B-cap straddling z. Enumeration: every
  partition of these X has shape (5,10,10), a pure bottom cap, and z in band 2.

**Side result: P and BRL+ are false [C, re-checked].**
- P (both sides) fails from n = 13 (tight566/656/666 and TDF g556n14 sub-nodes).
- BRL+ (either side) fails at n = 24 (6 sets).
- All 33 failures have lo = 1. **At lo ≥ 2, P held at all 1,697 (B,k) and at all 7,754 core gaps.**

## 2. The reduction is void as stated; case R needs one point

- **[P]** cup A = lo, so |A| = 1 ⟺ lo = 1, and ZLOCK *is* case R at lo = 1. Multi-point A have lo ≥ 2, where ZLOCK
  is trivial.
- **[P]** No later A-point is a lower singleton of the grown part. The triple (b,a′,a) with a′ in the middle is a cup
  in X but a cap under {a}<<rest. Every |A| = 2 node is a witness, e.g. n = 7, mask 7499038345.
- **[P] Exact joint criterion** (Lemma DS; matches all 523,264 (map, lift-set) pairs at n ≤ 8). Keep K in band lo and
  lift Lf to band lo+1. This is valid iff:
  - band lo straddles no lo-cup of K; and
  - cap Lf ≤ β−1; and
  - no (β−1)-cap of band lo+1 lies right of min Lf or left of max Lf; and
  - no (β−2)-cap of band lo+1 lies between min Lf and max Lf.

  So lifting is a two-point condition and keeping is an interval condition.
- **What closes case R [P+C].** If B's bottom band lies left of min A (or right of max A), keeping ALL of A in band
  lo is valid. So lo ≥ 2 follows from **P at the outermost A-point**. No order and no lifts are needed.
  - OUTER held on both sides at all 2,020 multi-point case-R nodes (1,759 of the 1,786 classified are mixed).
  - A's lo-cups share no point at 510 of them.
  - Lift-all fails at 598 and a single lifted point at 978.
- **Case R ⟸ ZLOCK (lo = 1) + P (lo ≥ 2).** BRL+ survives exactly where ZLOCK is not needed.

## 3. CORE: no implication

- **Maps tried.** M1 (blue = band 1), M2, M3 (per-band first points of max caps) and M4.
- **|B| = 7 (24,002 pairs).** Each map gives PSL⁺ for some ZLOCK map, never for all.
- **Rigid sets (185 pairs, all maps enumerated).**
  - M1 never gives PSL⁺.
  - M3 does at 173 pairs, mostly via **lift** maps.
  - At 12 pairs no ZLOCK map's M3 colouring is PSL⁺, although CORE holds.
  - At the lift-only gaps every PSL⁺ colouring splits the bottom band of every lift map.

## 4. Composition and proof status

- **[P] 2-band ZLOCK** (any signotope).
  - F = the first points of the β-caps, which lie ≤ L* < z.
  - F has no 3-cup: such a cup would yield a 4-cup or a (β+1)-cap.
  - B∖F has cap ≤ β−1. The same argument gives P.
- **[P] Wide–wide.** cap B2 ≤ cap B1 − 2, so ZLOCK(B1, z) ⇒ ZLOCK(B, z).
- **[P] {z′}<<C concatenation.** Take band 1 = {z′}.
- **[P] Lower classic absorbed sibling.** It is a single point.
- **Single-point absorption {z′}<<C (also C<<Z absorption).** ZLOCK(C, ·) is not a closed hypothesis.
  - n ≤ 7: it fails at 1,676/5,558.
  - n = 8 exhaustive: it fails at 111,346 of 169,606 pairs.
  - hard corpora: it closes only at 385/6,879.
  - **A fixed branch at one point (z or z′) always closes; two points are never needed.**
  - At 2,999 pairs the point must be z′.
  - At 3,220 pairs only an oriented stay works, and oriented stay is false in general.
  - So orientation must be carried, which is Q17's tower.
- **No direct argument for ≥ 3 bands.** The F-rule fails because first points of β-caps contain 3-cups. Stay fails
  exactly where z starts and ends β-caps of X.
- **Open.** ZLOCK at tight, two-sided mixed z; P at lo ≥ 2.

## Evidence

Jobs (prefix 20261003-):
- truth: 221655-c0f0ed, 221957-182fd0, 224619-44d6da, 225638-71c623
- re-checks: 224509-edb04e, 225310-34bada
- reduction: 223851-ea4b66, 223951-1044bd, 224902-9a0a20, 225050-ccbd59, 225516-b26977
- CORE: 230804-d3aa34
- composition: 223739-f4aab8, 224820-4c71f4

Code and outputs are `*.py` and `o_*.txt` in this directory.
