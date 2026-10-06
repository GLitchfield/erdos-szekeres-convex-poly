# R2 at u = k through Baek's induction: three steps repaired, one step fails (claude-r2c-20261002)

N = k = u. U = P|Q with P = p_1..p_a. s_Q(x) is the longest Q-cup starting at x. pen(C) is the second-to-last point of C. Every 4-cap starts in P. No proof. All evidence is Python/SAT; nothing is Lean-checked.

## Proved by hand (0 failures on 630 gon-free samples, N = 5, 6, 7)
- **Lemma J.** Let r ∈ Q end an (N-1)-cup C whose last three points c'', c', r are in Q, and start an (N-1)-cup X = r x_2 … x_e. Then U has an N-cup or a strong N-set.
  - (c_1, r, x_2) is a cap, else c_1·X is an N-cup.
  - If (c'', c', x_2) is a cup, r is a cap apex over (C−r)·x_2.
  - Otherwise (c', x_2, x_3) is a cup (c'' ∈ Q) and (c', r, x_e) is a cap, so r is an apex over c'·(X−r).
  - With only the last two points in Q, the statement fails (43 samples).
- **Deletion lemma D'.** For gon-free U and N ≥ 5, let D be the last point of each s_Q-row, s ≤ N-2. Then U − (D ∪ {p_1}) has no (N-1)-cup.
  - A cup with two or more P-points: prepend p_1.
  - Otherwise the last three points are in Q: use Lemma J, or append r's row-mate.
  - No join-WLOG is needed.
- **Lemma 5.2+ (repaired lacing).**
  - Left potential e*(x): the longest cup ending at x whose second-to-last point is in Q (1 on P). Right potential: s_Q.
  - If p<q<r<s, C1 = p→r and C2 = q→s are (N-1)-cups, pen(C1) ∈ Q, and both pairs are laced for (e*, s_Q), then U has an N-cup or a strong N-set. The case q = r is Lemma J.
  - Proof: Baek's case split. Every 4-cap that could break a glued cup starts at pen(C1), pen(cp) or pen(cq), all in Q.
- **Lifting.** The mirror lift C1' ↦ C1'·o keeps these hypotheses.

## What fails
1. **Lemma 5.2 verbatim.** Counterexample B (`counterexamples.txt`), a gon-free (6,6) set.
   - C1 = (3,4,8,9,11) and C2 = (5,6,8,9,12) are laced and interweaved.
   - The prefix cup (0,1,2,3) cannot be glued: (2,3,5,6) is a 4-cap.
   - So the α raised by P counts but cannot be glued.
2. **Mirror WLOG.** Lifting needs s_Q(r') ≤ N-2. Baek gets this by mirroring, but the R2 class is not mirror-closed.
   - The non-mirror Δ_Q extends cups leftward into P's 4-caps.
   - The lift is blocked in 31 of 65 oversized (6,a) cases.
3. **Decisive: Baek's Theorem 5.10 (oversized ⇒ interweaved laced pair) has no analogue.** Counterexample A: (N,a) = (5,4), |U| = 9 = bound+1, R2-class, no 5-cup.
   - Its only 4-cups are P, q1q2q3q4 and q1q2q3q5. None interweave, so there is no laced pair of any kind.
   - Its gons:
     - 4-cap p1q1q4q5 with cup p1q3q5;
     - 4-cap p1q2q4q5 with cup p1q3q5;
     - cap q1q4q5 with cup q1q2q3q5.
   - Starting from a = k-1 the induction passes through (5,4).
   - The derived U' has no laced pair in 52/294 oversized (6,5) samples and 3/53 oversized (7,6) samples.
   - The sound witness exists in only 8/200 at (5,4), 85/300 at (6,5) and 39/60 at (7,6).
4. **Lemma C as a sub-step.** Applied after one Δ-step, it gives |U| ≤ C(N-1,2)+2N-5, which is N-2 short.

**SAT (exact).** For a ≥ N-2, R2 at bound+1 needs strong sets with every left end p_1..p_{N-2}.

## Proof idea and obstacle
- P lengthens cups through Q, but the extra length cannot be glued because the 4-caps start in P.
- Discarding it gives a sound lacing lemma, but the gons of oversized sets are then "P-heavy", with caps from p_1. No laced pair produces them.
- **Open question.** Find a second witness that lifts when p_1 is deleted. Adding one deleted point to a strong set of U' fails in 20/200 cases at (5,4).

## Files
- Lemma checks: `claimD.py`, `sound52.py`.
- Induction-step tests: `wlift.py`, `uprime_laced.py`, `complete52.py`, `minL.py`.
- `counterexamples.txt` holds counterexamples A and B; `verify_cex.py` re-checks them.
- `over_*.pkl` and `r2_*.pkl` are the samples.
