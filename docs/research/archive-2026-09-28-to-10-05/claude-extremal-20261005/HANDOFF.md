# Research handoff: F and the structure of extremal sets (2026-10-05)

Node: ErdosSzekeres.decomposable_extremal_insertion (F). Inserting any point into a decomposable 2^(k−2)-point
k-gon-free set forces a k-gon.

Direction from Gavin: characterize the extremal sets (2^(k−2) points, no convex k-gon) and use that for F.

Living document: PICTURE.md. Detail: gluing/GLUING.md, extension/EXTENSION.md, extension/TRANSFER.md. Everything
below is diagnostic computation [C] or a hand proof [P]; nothing is in Lean.

## Open obligation (unchanged)

F for k ≥ 7. F implies the diagonal case of Theorem 8 [P], because subsets of decomposable sets are decomposable. So F
cannot avoid B's lock by tree induction.

**Current proof idea:** none.

## What was learned

**1. Census.**
- k = 5 is complete: 19,870 extremal signotopes (4,994 orbits), all realizable; 14% decomposable.
- k = 6: about 10^15–10^18 (Knuth estimate).
- k = 7: no 33-point heptagon-free extension of the 171 known or walked 32-sets (5,643 SAT instances, UNSAT).

**2. A universal counting skeleton,** on every extremal set tested:
- cup = cap = k−1;
- a full band stack C(k−2, j) of classical extremal blocks;
- a halving into two extremal (k−1)-sets;
- a cube labelling X ≅ {0,1}^(k−2), the ES construction's skeleton.

Each exists in thousands of ways. Nothing finer is universal: decomposability, flags, layer profiles, rigid blocks and
simple gluing all fail.

**3. FBDL** (full-range band partitions of every k-gon-free set) holds on everything tested. That includes X14 and the
k = 7 tight sets, which failed only because their range was restricted. FBDL implies ES; extremal sets are its full
case.

**4. Gluing.**
- k = 5 has an exact pairwise rule [P].
- Twin lemma [P, given ES(k−1)]: halves must twist through each other.
- From k = 6 the obstruction is not pairwise.

**5. Extension.**
- Extensions are slope orders π [P].
- q outside conv X: F ⟺ C1 (extremal sets have a (k−1)-cup) ⟺ the ETV(k; k−1, k) instance [P for point sets].
- The two-halves recursion fails: the forced k-gon splits across a halving like a random set.

**6. Transfer (continuation).**
- At segment crossings, births are exactly the opposite-side gons with edge xy [P].
- At one-sided edges the transfer IS F [P].
- One-sided edges are 33–51% of non-hull gon-edges, and the share rises with k. Interior coverage comes from global
  "survivors", not births: safe moves reach 0–1.2% of interior cells.

## The obstacle every attempt hit

The k-gon forced by a new interior point is not localised. Halves, bands, half-planes and crossed edges all miss it,
and the pocket covering is global. The same globality shows up as: the non-pairwise gluing at k = 6, the
random-like split across halvings, and the survivor phenomenon.

## Failed approaches and their failure modes

| approach | how it fails |
|---|---|
| deep-below gluing | twin lemma |
| two-halves gluing, forms (a)–(c) | fails; (d) is generic |
| band staircase | holds for 72% of (stack, q) pairs, never for a whole stack at every q |
| canonical blocking family | not canonical |
| TSE | false at 33–51% of edges |
| reach lemma | fails 979,206 times |
| safe-path continuation | reaches 0–1.2% of interior cells |
| chart counting | the far side can be a single point |

## Unresolved questions

1. A canonical survivor (TRANSFER.md, open question 1).
2. A covering potential (TRANSFER.md, open question 2).
3. Whether the cube labelling exists for every k-gon-free set at its own size (FBDL/PSL). This is ES-strength.
4. The k = 6 gluing rule.

## Evidence paths

All under runs/claude-extremal-20261005/:
- k5.json, s16_3000.jsonl, fw7.jsonl;
- gluing/, extension/, extension/transfer/;
- the scripts listed in each write-up.

Jobs logged in es journal under the F node, 10-05.
