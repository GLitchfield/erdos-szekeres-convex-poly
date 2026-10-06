# Accepted upper diagonal gate

2026-10-03T05:56Z. `singletonUpperPascalTailGate_diag_five_of_six_le_of_inputs`
is accepted and committed at `c79e55d04dffaa123194174c3a282374132654c2`
on `node/SingletonUpperPascalTailGateDiagFiveOfSixLeOfInputs`.

Exact statement: the same uniform R20 cupblock and R21 Baek hypothesis
shapes as the accepted lower diagonal gate, k>=6, conclusion
SingletonUpperPascalTailGate k5k. Full original-source check
`20261003-013823-62cacb` confirms locked hash `f4788b174428c98`, CLOSED,
no sorry, no nonstandard axioms, only propext/Classical.choice/Quot.sound.
Receipt `upper-diag-original-source-receipt.json`; job893.4s,peak5684MiB,
build6.933s. Source compiled first try; changed audit clean.

Proof idea: existing singletonUpperPascalTailGate_iff_lower_dual at
(a,u)=(k,5) turns the accepted lower diagonal theorem into this upper gate.
k>=6 supplies all four arithmetic side conditions. The exact external
inputs are uniform over every colouring, so the same inputs cover the
colour-dual instance. No new hypothesis or mathematical case was added.

Capture `20261003-015344-5fc88b` saved fixture
`b6cfeee3a45fb24a11c29974eea88a5ec6426a8c5ee7b91d4c5c5d3118357f99`.
Commit `20261003-015354-a4d87f` completed with no uncommitted files.
An early file read was empty while capture was still running, and commit
was queued before terminal confirmation; this workflow ordering error
was logged and resolved before release. Both terminal outputs were read.
Fixture metadata names the exact parent, whole-declaration scope,
type hash and standard axioms. Its source hash
`50d5e50ae3ca9eb7b135927251eee00e546f38a0cf680204f2192134a3af43b2`
matches sha256sum of the committed working file. No source mutation
occurred after the accepted check. No failed mathematical route occurred.

All approved R22 gate obligations, including the optional duals, now have
accepted exact receipts and commits. No mathematical obstruction remains
for these targets. Final separate upper mathematical review, code inventory
refresh, late usage reconciliation and fixed-deadline consolidation remain.
The native goal stays active until the fixed research deadline. The global
conjecture remains open; coordinator input instantiation after integration
is documented as an uncompiled sketch in INTEGRATION-NOTES.md.
