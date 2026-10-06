# Coordinator note 2 (2026-10-03 ~14:45)

Findings since your launch (details in the main checkout's runs/claude-general-picture/GENERAL-PICTURE.md):

- **Audit.** BDL and P are verified exhaustively to n = 9 (runs/claude-audit-bdl-20261003/AUDIT.md).
- **Reduction.** BDL ⇐ G (runs/claude-bdl-induct-20261003/NOTES.md). But G AS STATED FOR ALL t IS FALSE: a tight
  (5,6,7) set with n = 25 and EMPTY cores (runs/claude-bandrule-20261003/q9/cex_osj.txt). Restate G with the core
  hypothesis (t inside a nonempty cap core), which is the only form case R uses.
- **No top-down rule.** Top-down DS induction with bounded intrinsic contexts is impossible because of lookahead
  (Q7c). Universal partitions do not compose (Q9b). Point insertion has unbounded repair distance (Q11).
- **Wide–wide splits compose** (Q9c, proved): concatenating one-sided partitions of two wide children gives a
  joint. The single open step is CLASSIC-BLOCK INSERTION: a classic (one-band) sibling block Z of a wide W. This
  contains case R.
- **PSL is stronger than BDL** (runs/claude-psl-20261003/NOTES.md). Its obstruction is one-coloured, and its
  context is a separable cap profile, a class closed under DS (Q6).
