# Balanced residue transition laws

Date: 2026-08-05

## Question

Can two vertices in the balanced `11+11` branch be coupled when they select
the same three-vertex cap residue or five-vertex strong-six residue on the
opposite side?

The frozen review packet has SHA-256
`0ad00008195890af8dad2510d588787d17ab889c02814c4389f07858f138eaed`.
Its two exact contracts were a monotone pair profile for a shared cap residue
and a discrepancy transition for a shared strong residue.

## Route review

Claude Fable 5 returned `partially_supported` at medium confidence, and Codex
Sol returned `partially_supported` at high confidence. Both judged the two
contracts correct but insufficient for a fiber bound. Both independently
recommended the outcome-completion lemmas now proved below: an all-right cap
profile completes a cap five, while constant/agreed strong extensions complete
a strong seven. Fable additionally proposed the elementary three-five-subset
overlap theorem. The review is advisory and does not certify any result.

## Compiling Lean results

`StructuralChargingResidueTransitions.lean` proves the following without
`sorry`, an external oracle, or a new axiom.

1. If `q < r` precede a common cap residue, then the colors of triples
   `(q,r,x)` can change only from left to right as `x` advances through the
   residue. On three ordered vertices the exact possible words are `LLL`,
   `LLR`, `LRR`, and `RRR`. The mirror orientation also compiles. An `RRR`
   profile glues the two cap extensions into a cap five, so it is excluded in
   the active no-cap-five branch.
2. If two strong-six extensions over a common base disagree on an extension
   color, one-change forces the first two external-pair colors to agree with
   the earlier extension color.
3. Strong extensions agree automatically at every base middle having an
   earlier vertex in the common base. Any extension disagreement is therefore
   confined to the first base middle.
4. Two strong-six extensions over a common five-residue glue to a strong
   seven when their external-pair profile is constant and their extension
   colors agree. Consequently the no-strong-seven branch forces either pair
   variation or a first-middle extension disagreement. A first-middle
   disagreement propagates across the whole base and forces the pair profile
   to be constant, giving an exact two-state dichotomy.
5. Among any three five-subsets of an eleven-set, two intersect in at least
   two vertices. This supplies the first choice-independent overlap theorem
   for distinct strong residues.

The final two statements are also specialized to the ordered two-side cut,
so they can be applied directly in the balanced branch.

## Bounded countercontrols

`scripts/check_repeated_residue_fibers.py` generates deterministic CNFs, and
`scripts/verify_repeated_residue_model.py` independently reconstructs and
checks every reported SAT assignment. The models impose one-change, cap-four
avoidance on both blocks, and ambient avoidance of cap five, cup six, and
strong seven.

In the minimal fixed-residue tests, a common cap residue survives with ten
external vertices and a common strong residue survives with all eleven. The
eleven-external cap instance is UNSAT, but this has no checked proof
certificate and is only advisory evidence. The cap and strong summary hashes
are respectively
`42716f3c31a5f40b474bedeb7dc6b193bf76341effc6f6d0940e39971a503cf3`
and
`cdd21d36fcca87d66d6f103521f8679b88c434f6884337d2556d70e94085361e`.

The stronger `11+2` and `11+3` controls retain the full eleven-vertex opposite
side and additionally forbid an internal strong six there. Both cap-residue
and strong-residue repetitions remain SAT and independently validate. Their
summary hashes are
`9925239d0a0811a7d3e10766980ca47c02ef3f00804b716acd8987d2fd11bfd8`
and
`d6730d9730d80fdf2d8cc87cdd6bfd6ec9625ff6ce3a9e0258d81e97fd4c1913`.

Thus the new transitions are genuine structure but not standalone fiber
bounds. The unused vertices of the eleven-side still do not force an outcome
from two or three repetitions of one residue.

## Next theorem

The next balanced target must exploit the proved pair overlap between distinct
strong residues. The generic discrepancy transition already applies when two
different bases share only the probed pair; its agreement case still needs a
third base vertex or a crossing strong six supplied by the 22-point packing
theorem. A useful next statement should connect that packing to at least three
strong-residue witnesses on one side. Any stronger intersection claim should
first be tested on the validated `11+3` controls.
