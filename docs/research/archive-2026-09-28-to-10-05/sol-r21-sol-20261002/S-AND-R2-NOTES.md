# (S) and R2 (claude-r2-20261002)

## (S): proved, by a published theorem
(S) for u <= k-1 is the classical cup–cap bound. For u = k it is exactly **Baek, Theorem 2.7**: J. Baek,
"On the Erdős–Tuza–Valtr conjecture", *European J. Combin.* 124 (2025) 104085, arXiv:2206.04260.
- **Statement.** Any configuration of size C(n-1,2)+2 contains a 4-cap, an n-cup, or a (3,n-1)-gon. A configuration
  is an arbitrary 2-colouring of ordered triples; cups and caps are defined by consecutive triples.
- **Why it covers us.** Signotopes are configurations. In a signotope every triple of a cup is a cup, so the cap
  apex lies off the cup and Baek's weak gon is our strong set. Taking n = k gives |X| <= 1+C(k-1,2) = T(4,k,k).
- **Proof idea.**
  - The (α,β)-plane injects X into {1 <= α <= β <= n-1}.
  - Two interweaved *laced* (n-1)-cups force an n-gon (Lemma 5.2).
  - Induction: delete Δ, the leftmost point of each row β = 1..n-2, after a mirror WLOG. The remainder is
    (n-1)-cup-free, and a laced pair found there lifts back.
- **Replays.**
  - SAT: T+1 points is UNSAT at k=5,6.
  - Theorem 5.10 held on all 300 samples (`s_laced1.py`).
  - `s_baekdelta.py`: Δ makes S\Δ (k-1)-cup-free in 150/150 tight sets, but it misses some strong (k-1)-set in
    43/150. Baek's induction is **not** a hitting-set deletion, so the deletion-lemma framework asks for more than
    the known proof gives.

## R2: not proved. Verified facts and the obstacle
**Equivalent forms.** R2 says |U| <= C(k,2)-2 for u = k, and |U| <= C(k,2)-3 for u = k-1. For u = k, in Q's
(α,β)-plane this reads holes(Q) >= |P|+2. Because |Q| <= T, a counterexample has |P| >= k-3.

**Symmetric generalisation R2S (SAT-exact, diagnostic).**
- Setting: P (a-cup) | Q | R (c-cup). U is 5-cap-free, every 4-cap starts in P or ends in R, there is no u-cup and
  no strong k-set.
- Claim: |U| <= T(4,u,k) + min(a,k-4) + min(c,k-4).
- Checked exact for every (a,c) at (5,6) and (6,6), and at sampled splits at (6,7) and (7,7) (`sym_table*.py`).
- It fails at k = 5: the maximum is T+1, not T+2.
- Why it matters: each side cup adds at most k-4 independently, and the class is closed under mirroring, which
  restores the WLOG step Baek's induction needs.

**Lemma (strict 5.2; proved by hand, any signotope).**
- **Definitions.** Let β\*(x) be the longest cup ending at x whose last edge starts no 4-cap. Let s\*(y) be the
  longest cup starting at y whose first edge ends no 4-cap. An (n-1)-cup from x to y is *strictly laced* if
  β\*(x)+s\*(y) >= n-1.
- **Claim.** With no n-cup, interweaved strictly laced (n-1)-cups p→r and q→s with p<q<r<s give a (3,n-1)-gon:
  pqr is a cap, or qrs is a cap.
- **Proof.**
  - If qr starts no 3-cap: pq must start a 3-cap (p,q,d). If pqr is a cup, then C_p·q·C_r is an n-cup. The only
    possible break is a 4-cap (c,p,q,d), which strictness excludes.
  - Otherwise qr ends no 3-cap, or qr both starts and ends one. Then rs must end a 3-cap (w,r,s). If qrs is a cup,
    then C_q·r·C_s is an n-cup. The only possible breaks are 4-caps (c_q,q,r,d) or (w,r,s,s₂), and strictness
    excludes both.
- **Degenerate case q = r (Lemma 5.1).** It holds unless C1's penultimate edge (a′,a) starts a 4-cap (a′,a,b,d).
- **Replays.**
  - 193 pairs in random 5-cap-free signotopes, 0 failures (`strict52_replay.py`).
  - In gon-free R2 sets, the only strictly laced pairs are degenerate: 57 pairs, all with q = r (`r2_T1.py`).
- **Contrast.** Plain laced pairs do occur in gon-free R2 sets (86/300, `r2_laced.py`). Baek's Lemma 5.2 fails
  verbatim there; the 4-caps from Z break "a label-2 edge extends a cup".

**Small proved observation.** Suppose some (u-1)-cup C in Q has a first edge (x,x₂) that starts a 3-cap in Q.
Then P ∪ {x} is a cup, since otherwise there is a 5-cap (p_i,p_j,x,x₂,y).

**Obstacle.**
- **No Theorem 5.10 analogue.** Oversized R2-type sets (gons allowed) often contain no good pair. Example: n = 6,
  |P| = 3, |Q| = 11 gives 17/60 (`r2_lemA.py`, `r2_T2*.py`). Their gons are (3,n-1)- or (4,n-2)-gons not produced
  by laced pairs. The positive invariant Baek's induction needs is missing: it must also cover 4-cap gons and must
  lift through Δ.
- **Deletion is not canonical.**
  - Δ_Q plus one P-point hits all strong (k-1)-sets in only 24 to 62 of 100 tight instances (`r2_delta.py`).
  - Hitting sets of size k-1 are plentiful but have no evident rule (`r2_hits.py`).
- **The trade-off is exact but not localised.** holes(U\Z) = |Z|+2 in every tight u = k sample (`r2_coll.py`),
  but the hole positions vary (`r2_holes.py`).

**Proof idea for R2 (none complete).** Run Baek's Δ-induction on R2S, deleting Δ_Q together with one point of P
and one of R. The bookkeeping matches: the bound drops by (n-2)+1+1. What is missing is an invariant that implies
a gon and lifts.

All evidence is diagnostic Python/SAT (pysat CaDiCaL); nothing is Lean-certified. Scripts are in this directory,
and `common.py` holds the shared helpers.
