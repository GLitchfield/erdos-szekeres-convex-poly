# Optional upper gates

Updated2026-10-03T06:06Z. Both exact lower gates and both upper gates
are accepted, committed and released CLOSED. Upper predecessor check
20261003-010620-a45c42, hashf3116a1be4927653, commit
cb87071e20d5a1199e014e943c267ddd729d357a. Upper diagonal check
20261003-013823-62cacb, hashf4788b174428c98, commit
c79e55d04dffaa123194174c3a282374132654c2. No live job or claim remains.
FINAL-MATHEMATICAL-REVIEW.md and FINAL-CODE-MAINTENANCE-REVIEW.md record
the completed receipt/source and code reviews. The proof plan below was
implemented without changing its mathematical route or assumptions.

The existing singletonUpperPascalTailGate_iff_lower_dual in
ErdosSzekeres/StructuralChargingPascalTailGates.lean:332 swaps the cap/cup
parameters. Its side conditions are2<=a,2<=u,a<=k,u<=k, all immediate
under k>=6 for these two targets.

- Predecessor upper target: k>=6 implies SingletonUpperPascalTailGate
  (k-1)5k. Apply the iff at a=k-1,u=5 to the accepted unconditional
  singletonLowerPascalTailGate_five_pred_of_six_le.
- Diagonal upper target: with the exact same uniform hblocks/hbaek
  statement shapes as the lower diagonal gate, k>=6 implies
  SingletonUpperPascalTailGate k5k. Apply the iff at a=k,u=5 to the lower
  diagonal theorem instantiated with those inputs.

No colour-dual assumptions need separate signatures because both original
inputs are uniform over every TripleColoring. Colour duality swaps root
children, cups/caps and reservoir formulas while preserving strong sets
and decomposability. No order reversal or new case analysis is needed.

Before writing proofs, es search 'singleton upper Pascal tail five
predecessor diagonal dual gates' returned no hits. Cite SEARCHES.md if a
PR is later prepared. Register each statement only through es node add,
one node/ branch, then original-source check, proof capture, commit and
claim release with evidence. Their large import closure likely needs full
28G extraction; measure/review against previous matched full runs rather
than choosing a deadline. Final mathematical/code review and library
maintenance usage window remains separate from research.
