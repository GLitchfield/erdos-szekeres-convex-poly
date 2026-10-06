# Experiment 0126: survey of combinatorial tools for the MIXED ROOT lock

Date: 2026-10-04. Status: complete. No tool proves the lock (exp 0125).

## Source documents

Archive: `docs/research/archive-2026-09-28-to-10-05/claude-survey-20261004/`.
- `SURVEY.md`: the ranked synthesis.
- `PROBLEM.md`: the self-contained problem statement.
- Six area reports, A–F:
  - A: Erdős–Szekeres literature;
  - B: extremal set theory;
  - C: posets and RSK;
  - D: global existence methods;
  - E: oriented matroids;
  - F: substitution decomposition and tree automata.

## Results [C diagnostic, P where marked]

**Obstacle, located three ways.**
- Canonical cupEnd layering fails only at overfull points (cupEnd + capEnd >= k+2) [P]. These come from mixed caps.
- A root split cuts the window at one level [P]. The lock is the degenerate level p = k−a, where A displaces a star
  of level p.
- The keep/lift choice on A is locally forced. At cex40, zero B-points move relative to the best B-partition.

**Choice-free SH.** Canonical Moshkovitz–Shapira labels plus one matching hold everywhere tested, including general
signotopes and exhaustively for n <= 8. SH is ES-strength.

**Purity, easy half.** Exhaustive for |X| <= 8 over all 3.8M decomposable 9-point colourings: every constrained set
below T extends by one point. Point sets differ: Damásdi–Dong–Scheucher–Zeng, EJC 131 (2026), arXiv:2312.01223.

**Refuted or closed.**
- the Mirsky window (n = 21);
- Greene–Kleitman saturation (n = 8);
- kernel bottom-peel at mixed roots;
- the one-band star exchange;
- Baek's ETV peel, which stops at a = 4.

**Dead families.**
- Scarf;
- Gale–Shapley;
- topological Hall;
- Nullstellensatz;
- shifting;
- LYM/Sperner;
- substitution;
- WQO;
- regular cost functions.

## Data

- Probes are in the archive's run directory: split_layering, ms_labels, ms_shrink_*, purity2, star_flow.
- Job IDs are in the journal export.
