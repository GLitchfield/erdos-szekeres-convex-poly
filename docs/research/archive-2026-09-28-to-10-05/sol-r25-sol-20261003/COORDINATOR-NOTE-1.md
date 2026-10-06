# Coordinator note 1 (2026-10-03 ~13:10): an input for case R

The k=∞ run (/home/gavin/git/erdos-szekeres-convex-poly/runs/claude-kfree-20261003/NOTES.md, §4) proved a
ROTATION LEMMA. If X = A<<B, A is cut as A1|A2 and B lies entirely in the x-gap between them, then the same
colouring has a non-interleaved tree, A1<<(B∪A2) or A2<<(A1<<B). Check its exact hypotheses there.

Case R is the mirror situation: A nested in the core of B's β-caps. If A lies within a single x-gap of B and B's
tree permits the cut there, X may re-root into a non-nested split, where BDL already closes. Then the genuine
residue of case R is B-points inside A's span.

A Claude subagent (runs/claude-bdl-induct-20261003 in the main checkout) is testing this computationally. An
independent audit of BDL is running in runs/claude-audit-bdl-20261003.
