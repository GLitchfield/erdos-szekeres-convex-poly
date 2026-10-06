# Two-cup-block lemma: a uniform proof (claude-cupblock-20261002)

Status: a proof by hand for every k >= 5. Every step was also replayed by a script, on all two-cup-block
signotopes with n <= 8 (14,753 (signotope, split) pairs) and on about 1,300 random blocks with 9-12 points,
including tight ones (n=10, maxconv 6; n=12, maxconv 7). The replays are diagnostics, not Lean proofs.

Setting: U = P|Q, P = p_1<...<p_a and Q = q_1<...<q_b are cups, there is no 4-cap, and "convex" means a cup
and a cap that share exactly their two endpoints. The proof uses only two consequences of the signotope
axiom, both given in the task: in a cup every triple is a cup, and the two definitions of convex position
agree. The second was checked on all blocks with n <= 8. Decomposability is never used.

## Step 0. Shape of convex sets
With no 4-cap, a cap has at most 3 points. So a convex set S is either a cup, or S = C ∪ {x} where C is a
cup from l = min S to r = max S and (l,x,r) is a cap. Every triple inside P or inside Q is a cup, so l ∈ P
and r ∈ Q. Conversely, every such C ∪ {x} with x ∉ C is convex, by the definition.

## Step 1. Claim D (the deletion lemma, with a canonical choice)
Let D = {p_2, q_{b-1}}, keeping whichever of the two exist. **If S ⊆ U \ D is convex and |S| >= 5, then U has
a convex set of size |S|+1.** So every maximum convex set meets D once maxconv(U) >= 5, and deleting the
second point and the second-to-last point of U lowers maxconv by at least 1.

Proof. Two moves on a cup C keep it a cup, because every new consecutive triple lies inside P (or inside Q):
(M1) inserting a point of P below the second-to-last P-point of C, when C has >= 2 P-points; and
(M2) prepending p_1, p_2 when C has >= 2 P-points, all at or after p_3.
Their mirror images on Q are (M1') and (M2').

- Case A: S is a cup, with h points in P and g points in Q. If h >= 3, then p_2 < s_{h-1}, so S ∪ {p_2} is a
  cup by (M1). If g >= 3, the same holds for q_{b-1}. Otherwise |S| = h+g <= 4.
- Case B: S = C ∪ {x}, where C has c points s_1<...<s_c in P and g points t_1<...<t_g in Q.
  - If c >= 2 and s_1 >= p_3, then {p_1,p_2} ∪ C is a cup of size |S|+1 by (M2). So if c >= 2, then s_1 = p_1.
  - If c >= 3, insert p_2 between s_1 and s_{c-1}. This uses (M1) and keeps both endpoints, so the cap (l,x,r)
    survives and S ∪ {p_2} is convex.
  - The mirror moves handle Q.
  - What remains is c, g <= 2, so |S| <= 5. Equality forces C = {p_1, s, t, q_b} with s >= p_3 and
    t <= q_{b-2}. If chi(p_2,s,t) is a cup, then S ∪ {p_2} is convex (the cup C ∪ {p_2} keeps its ends). If
    chi(s,t,q_{b-1}) is a cup, then S ∪ {q_{b-1}} is convex. Otherwise p_2 < s < t < q_{b-1} is a 4-cap,
    which is a contradiction. ∎

Claim D is false at size 4. For example, in a (3,3) block with maxconv 4, the 4-gon {0,2,3,5} avoids
D = {1,4} (see `base_replay.py`). The obstruction is the cup {p_1, s, t, q_b}. No fixed deletion pair works
for every block at K = 4, which is why k = 5 needs its own base case.

## Step 2. Base case k = 5, by hand
Take a block with |P| = 4 and |Q| = 3 and no 4-cap. It always contains a convex 5-set:
- (a) If chi(p_3,p_4,q) is a cup for some q, then P ∪ {q} is a 5-cup. Otherwise chi(p_3,p_4,q) is a cap for
  every q.
- (b) Because there is no 4-cap, chi(p_4,q,q') is a cup for all q < q'.
- (c) If chi(p_1,p_4,q_1) is a cup, then {p_1,p_4,q_1,q_2,q_3} is a 5-cup.
- (d) If chi(p_3,q_1,q_2) is a cup, then the cup {p_3,q_1,q_2,q_3} plus the apex p_4 is convex; its cap is
  (p_3,p_4,q_3).
- (e) Otherwise the absence of a 4-cap at (p_2,p_3,q_1,q_2) makes chi(p_2,p_3,q_1) a cup. Then the cup
  {p_1,p_2,p_3,q_1} plus the apex p_4 is convex; its cap is (p_1,p_4,q_1), from (c).

The (3,4) case follows by left-right reversal. Any block with |U| >= 7 contains a 5-cup or a (4,3) or (3,4)
sub-block, so no 4-cap and no convex 5-set give |U| <= 6.

## Step 3. Induction
Let k >= 6, and suppose U has no 4-cap and no convex k-set. Then maxconv(U) <= k-1. If maxconv(U) = k-1 >= 5,
Claim D shows that U \ D has no convex (k-1)-set; if it is smaller, that holds trivially. U \ D is again a
two-cup block with no 4-cap. By induction |U| - 2 <= |U \ D| <= 2(k-1) - 4, so |U| <= 2k-4. ∎

Why it is true: a maximum convex set is a cup with at most one apex. Maximality forces its P-part to be an
initial run of P (starting at p_1 or p_2) plus one more point, and its Q-part to be a final run of Q plus one
more point. A run of length >= 2 contains p_2 or q_{b-1}. Only the 2+2(+apex) shape escapes, and the no-4-cap
condition on (p_2, s, t, q_{b-1}) blocks it. Each pair of "second-from-the-end" points therefore carries one
unit of convex size.

## Evidence
- `cb.py`: an exact DFS generator of two-cup blocks with no 4-cap, plus convexity checks.
- `gen_all.py` writes `inst_all8.pkl`, which holds all blocks with n <= 8.
- `inst_small.pkl`: the tight sets. k=5: (3,3) 54, (4,2) 27. k=6: (5,3) 954, (4,4) 1908, (3,5) 954. The
  sets (4,3),(3,4) at K=4 and (5,4),(4,5) at K=5 are empty.
- `rules.py`: for each (a,b,K), the deletion pairs that are always valid. The pair (point 1, point n-2) is in
  every list with K >= 5, and no pair works for every block at K = 4.
- `proof_replay.py`: the constructive witness of Claim D, plus agreement of the two convexity definitions, on
  all blocks with n <= 8.
- `replay_random.py`: the same checks, plus maxconv >= n/2+1, on random blocks with n = 9..12.
- `base_replay.py`: steps (a)-(e) on all 602+602 blocks of shapes (4,3) and (3,4).
