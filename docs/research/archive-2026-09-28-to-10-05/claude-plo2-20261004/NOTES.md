# P at lo >= 2 (claude-plo2-20261004)

[P] = proved by hand here; [C] = exact computation (pysat, cross-checked by library backtracking), diagnostic, not Lean.

**Setting.** B is decomposable, σ(B) ≤ s, β = cap B, l = s−β ≥ 2, α ≥ l+3, and the cap core is open (L* < R*).

## 1. Exact statement

| form | status |
|---|---|
| both sides at the core boundary (bottom ⊆ [0,L*] AND some partition with bottom ⊆ [R*,max]) | **FALSE** at l = 2, 3 [C] |
| U: some valid partition with cup(X_l ∪ X_{l+1}) ≤ l+2 | FALSE (same witnesses) |
| **S1: bottom ⊆ [0,L*] OR bottom ⊆ [R*,max]** (BRL+ at l ≥ 2) | held at every instance |
| S2: for every core gap g, bottom one-sided w.r.t. g | held at every gap |

- **Data.** About 4,700 (B,k) pairs with l ≥ 2 were tested.
  - They come from max-size and near-max open-core sets, forced by a two-zone SAT profile: k = 7 with β = 4, n = 17–22; k = 8 with l = 3 at n = 29–32, and l = 2 at n = 40.
  - All sub-nodes and colour mirrors were included, plus the earlier 1,697 sets.
  - The both-sided form failed 24 times, each time with exactly one side true.
- **Minimal witness, n = 19** (none in 600 samples at n = 17, 18): oc456n19-77, k = 7, α = 5, β = 4, σ = 6, core (8,13).
  - Labels: `1111 11011 1101010 1101011 01011 010100 011 01000 010101 1110 1001 1000 101 0000 01001 001 1100 0001 110100`.
  - No partition has bottom ⊆ [0,8]. The partition `3333333334444222224` has bottom ⊆ [13,18].
  - The open-core maximum at (β,α,s) = (4,5,6) is 21, which equals R25's CD bound 25 − C(4,1).
- **What case R needs.** Keeping A in band l works iff c(A ∩ span(bottom)) ≤ l−1 (R25).
  - S1 implies this.
  - S2 at a gap g implies it only when every l-cup of A crosses g, for example when A lies in one B-gap [P]. Otherwise S2 is not enough.
  - **So the lemma to prove is S1.** The l ≥ 2 hypothesis is essential: S1 fails at l = 1 (n = 24).

## 2. Mechanism

- **The hard core is configuration H.** B = P << Q with c(P) = l+1, d(P) = β, c(Q) = α, d(Q) = β−1, and c(P) + d(Q) = s.
  - P is "one-band": it fits exactly band l.
  - 23 of the 24 failures are H; the 24th is H << {point}.
  - The l = 1 BRL+ failures (n = 13; n = 24: g657n25d1-32, -6, osj25) are H with P a β-cap.
- **[P] In H, the natural composed partition always straddles the core.** That partition puts P in band l and Q in bands ≥ l+1, and P contains β-caps of B.
- **[C] How the one-sided partitions look in H** (74 H instances):
  - Whenever a side holds, there is a partition whose bottom contains F_P (first points of P's β-caps; cup(F_P) ≤ l by the endpoint lemma, which is paper81's set): 126 of 126 sides.
  - At 122 of 126, bottom ∩ P = F_P exactly.
  - The rest of the bottom is Q-points beyond F_P on the outer side (the "fold"). It is always available, and needed at 77 of 126.
- **What changes at l = 1.** A bottom band that contains Q-points is then a cap [x]+D_Q+[x′], so it holds at most one P-point on the inner side. The fold degenerates to D_Q+f. At l ≥ 2 the bottom holds the whole cup-l set F_P plus a Q-tail. This is an observed difference, not a proof.

## 3. Proved pieces [P]

- **Lemma H.** Suppose F ⊆ [0,L*], cup F ≤ l+1, and F meets every β-cap. Then BDL(B∖F) gives a partition on [l+1, α−1] (B∖F has cap ≤ β−1, or is classic and fits one band there), and F becomes the bottom, so P_L holds.
  - The lemma is not necessary. At n = 7, labels `101 0101 00 011 11 100 0100`, k = 7, the β-caps are (x,4,5,6) with x in the 4-cup {0,1,2,3}. There is no such F, yet P_L holds by splitting the caps across bands 3 and 4.
- **H, one mixed type absent.** If B has no β-cap D′+x′ (D′ ⊆ Q, x′ ∈ P), then F = P ∩ [0,L*] satisfies Lemma H, so P_L holds. Dually, if there is no x+D, P_R holds.
- **Retained-cap roots** (d(Q) = β, so P is nested in Q's core, and c(P) ≤ l). Start from Q's left-sided partition.
  - P ∩ [0,L*_B] joins band l.
  - P_> = P ∩ (L*_B, ∞) lifts to band l+1 **iff** band l+1 has no (β−1)-cap ending before max P_>. Every other condition is automatic, because caps starting in P_> have length ≤ β−1.
  - The mirror statement holds for the right side.
- **U.** U implies P_L and P_R (F-rule on the merged bottom). U(B) implies BDL(A<<B) and U(A<<B) at every retained-cap root, including case R. U is nevertheless false (§1).

## 4. The gap

**There is no complete proof idea for S1.** The induction S1(children) ⇒ S1(B) stops at two steps. Both are an obstruction one band higher.

1. **Retained cap.** A (β−1)-cap of band l+1 that ends before a lifted lower point. This is the tower again.
2. **H with both mixed kinds** (all one-sided failures are here). S1-L(B) follows from S1-L(B⁻), where B⁻ = (P∖F_P) ∪ Q, together with compatibility: B⁻'s bottom creates no (l+2)-cup q + C + q′ with the P-points of the bottom.
   - [C] B⁻ is two-sided at all 73 H instances where its cap stays β.
   - So B's orientation is decided by this cup compatibility. The orientation bit survives at l ≥ 2.

## Evidence

- **Jobs, prefix 20261004-:**
  - 005209-3a4ac5 (k = 7)
  - 005214-1132ff (k = 8)
  - 005923-ae569e (450 more max-size samples)
  - 011806-7fe9b8 (H structure)
- **Outputs:** `o_job{A,B,C,D}.txt`, `o_n1{7,8,9}.pkl`, `samples/*.pkl`.
- **Code:** `gen2.py` (two-zone open-core sampler, built on psat), `t7.py` (P and cut forms), `t9.py` (U), `t12–t15.py` (configuration H), `plib.py`, `rootinfo.py`.
