# Q24: rectification by local moves (claude-rectify-20261003)

Tags: **[P]** proved by hand here, **[C]** computed (diagnostic, not Lean).

**States and moves.** States are decomposable colourings, so representation changes that keep the colouring
(rotations) are free.

| move | what it does |
|---|---|
| M1 | adjacent swap |
| M3 | block swap |
| M4 | L/U role flip |
| M6 | move a point in x, tree kept |
| M7 | re-graft a leaf, x kept |
| M8 | delete a point and re-insert it anywhere |

**Monotone** means (cup, cap, strong) never increases. **NI** means non-interleaved.

**Potentials:**
- Φ_min = min over representations of Σ over nodes of the (L,U) pairs out of order (Φ_min = 0 ⟺ NI);
- δ = n − |largest NI subset|.

## 1. Global version [C]: holds

For every decomposable X with n ≤ 8 there is an NI Y of the same size with params ≤ those of X (62, 718,
10 596 and 186 888 colourings at n = 5..8). This was the expected sanity check.

## 2. Move version [C]

Exhaustive for n ≤ 8, over all 17.3M representations at n = 8. Each cell gives the number of colourings with
no monotone path to NI; in brackets, those where one-step Φ_min descent fails.

| moves | n=6 | n=7 | n=8 |
|---|---|---|---|
| M1 | 12 (68) | 302 (776) | 3832 (9034) |
| M1+M3+M4 | **4** (24) | 44 (296) | 124 (3332) |
| M6 / M7 alone | 0 / 0 | 8 / 6 | 204 / 46 |
| **M6+M7** | 0 (0) | 0 (0) | 0 (0) |

**Minimal obstruction for M1–M4 (n = 6).** X = p2 << ((p1<<p4) << (p3<<(p0<<p5))), params (4,3,4), not tight.
- Its only monotone move goes to its mirror image.
- It fails even the weak form, where every state need only stay ≤ the start parameters.

**One-step potential lemmas all fail:**
- Φ from every representation: fails at n = 6.
- Φ from minimal representations: fails at **n = 9**. X = (11,10101,10100,1011,011,010,00,1001,1000) has 32
  minimal representations and no descent from any of them.
- Φ_min at colouring level with M6+M7: fails at **n = 14**. Take the tight (5,5,6) set
  `0010 00110 00111 000 01101 01100 0111 010101 010100 01000 1 01011 010011 010010`. Its 56 172
  representations allow 49.5M moves, giving 71 colourings within the parameters, none with Φ_min < 4.
- δ by M8: fails at **n = 8**, for 68 tight (4,4,4) sets with δ = 2.

**Survives every test:** path existence with M6+M7, and Φ_min-descent with M8. At the n = 14 set,
re-inserting the locked point gives Φ_min = 1.

**Large samples:**
- Greedy descent reaches NI from 566/583 case-R residue sets and from 312/522 tight or T−1 sets (n ≤ 30).
- The stuck states are resolved at colouring level, except seven n = 14 states.
- Best-first search shows these are plateaus, not traps: all 7 reach NI in 2–3 moves, the first one
  sideways.

## 3. Case R

**Lemma S [P]** (from Lemma DS). For X = A<<B:
- strong X = max(sA, sB, cupA+capB), independent of the interleaving;
- cup X = max(cup B, max over cups C of A of |C| + [min B < first C] + [max B > last C]);
- cap X is the dual.

Only the four extreme points matter. Consequences:
- **(S1)** A crossing root sorts to a separated one monotonically.
- **(S2)** A nested root un-nests monotonically unless it is **locked**: the inner child lies strictly inside the
  core of the outer child's max caps (or of its max cups), and the outer child carries that number. Locked is
  case R without strong-tightness.
- **(S3)** Inside a lock, sorting is free. Rotation dissolves the lock iff the carrier splits at the gap.

So un-nesting needs a change to the carrier or a re-attachment, never a slide.

**Data [C]:**
- re-grafting the carrier's core point L* or R* descends in 550/583 residue sets;
- moving a nested point descends in 503/583.
- The rescuing point can be far away. At n = 9 the only one-move rescue is B's far-left point, outside the core.

**The n = 14 trap.** X = L << {u}, with u at the core boundary of L's 4-cups and defect set δ = 2 = {u, R*}.
The escape moves u three times: a free slide inside the core, a re-graft, a slide (Φ_min 4 → 4 → 2 → 0).

## 4–5. Verdict

**No local monotone move lemma:**
- M1–M4 fail at n = 6;
- single-point moves fail with every natural potential (n = 8, 9, 14);
- what survives has no proof idea, since Lemma S only settles unlocked roots.

**Reduction [P].** The final step of any single-point path extends an NI (n−1)-set to an NI n-set inside the
parameter box. By NI Theorem 8 this needs n−1 < T. So rectification at best reduces Theorem 8 to:
- **Theorem 8 for one-defect sets** (NI set plus one point);
- **NI saturation** (every non-tight NI set extends by one NI point within its parameters [C: m ≤ 7]);
- a move lemma down to δ = 1.

**The obstacle.** The hard core of the first item is the trap: a point locked against its carrier's max-chain
core boundary. This is the nested split again.

## Evidence

**Code:** `mg.c`, `ana2.py` (exhaustive); `nb.c`, `stuck_best.py`, `m8detail.py` (n = 14); `big_run.py`,
`big_cont.py`, `caser_run.py`; `delta.py`, `ni.py`.

**Outputs:** `o_mg8.txt`, `o_ana8b.txt`, `o_big.txt`, `o_caser.txt`, `o_stuck14_67.txt`, `o_best7.txt`,
`o_m8detail.txt`, `o_delta.txt`.

**Jobs:**

| job | what |
|---|---|
| 20261003-180627-587277 | n = 7 |
| 20261003-181307-3006a5 | n = 8 enumeration |
| 20261003-184947-d8a4b0 | n = 8 analysis |
| 20261003-181611-3093fc | greedy descent |
| 20261003-183336-aabfb4 | case R |
| 20261003-184736-d1f033 | breadth-first search |
| 20261003-185059-9fb65a | best-first search |
| 20261003-185409-65ad68 | best-first search, 7 states |
| 20261003-185106-eca131 | M8 check |
| 20261003-185444-108964 | M8 detail |
| 20261003-185754-f831fd | δ |
