# Experiment 0127: the structure of extremal sets (2^(k−2) points, no convex k-gon), and Workstream F

Date: 2026-10-05. Status: complete as a characterization study. F remains open, and no proof idea exists for an
interior new point.

**Source documents** (archive `docs/research/archive-2026-09-28-to-10-05/claude-extremal-20261005/`):
- `PICTURE.md` and `HANDOFF.md`;
- `gluing/GLUING.md`;
- `extension/EXTENSION.md` and `extension/TRANSFER.md`.

**Data:** `data/derived/extremal-sets-20261005/`.
- the complete k = 5 extremal family: 4,994 orbits, 19,870 signotopes;
- 3,000 k = 6 samples;
- 152 k = 7 flip-walk sets;
- scripts.

## Results

**Census [C].**
- k = 5 is complete: all extremal 8-point signotopes are realizable; 14% are decomposable; convex layers 3-4-1 or
  4-4.
- k = 6: about 10^15–10^18 (Knuth estimate).
- k = 7: no 33-point heptagon-free one-point extension of the 171 known or walked 32-sets (5,643 SAT instances,
  UNSAT).

**Universal counting skeleton [C, on every extremal set tested].**
- cup = cap = k−1;
- a full band stack C(k−2, j) of classical extremal blocks;
- a halving into two extremal (k−1)-sets;
- a cube labelling X ≅ {0,1}^(k−2), which is the ES construction's skeleton.

Each structure exists in thousands of ways. Nothing finer is universal: decomposability, the ES flag, layer
profiles, rigid blocks and simple gluing all fail.

**FBDL** (full-range band partitions of every k-gon-free set) holds on all data. It implies ES.

**Gluing.**
- Exact pairwise rule at k = 5 [P], via arc separation.
- Twin lemma [P, given ES(k−1)]: halves must twist.
- Not pairwise from k = 6.

**Extension.**
- Extensions are slope orders [P].
- F at q outside conv X ⟺ C1 ⟺ the ETV(k; k−1, k) instance [P for point sets].
- The two-halves recursion fails: the forced k-gon splits like a random set.

**Transfer.**
- F ⟺ C1 + transfer at line crossings [P].
- The transfer is F itself at one-sided edges.
- TSE is false at 33–51% of edges.
- Interior coverage comes from global survivors: safe moves reach 0–1.2% of interior cells.

**Obstacle.** The pocket covering for interior q is global, the same globality as exp 0125.
