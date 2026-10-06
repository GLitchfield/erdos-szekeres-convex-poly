# Accepted exact strong coupling

2026-10-03 19:16 UTC. General theorem
`ErdosSzekeres.deepSplit_strong_avoidance_iff`, module
ESBlueprint/B/DeepSplitStrongAvoidanceIff.lean, locked type
`c70c7da9646129a5`. CLOSED, no sorry, standard axioms only
(propext, Classical.choice, Quot.sound). Full finalization accepted;
one-node commit `1a83a00102042ea006a59da2465810644212290e`, basef31b9fbf,
branch node/DeepSplitStrongAvoidanceIff. Commit job20261003-151654-6c5a61
changed exactly the module, root import, lock, index and status; no uncommitted
tracked files remain. No merge or push.

For every natural s and arbitrary deep-below split L/U, parent avoidance
of a strong(s+1)-polygon is equivalent to child avoidance plus
|C|+|D|<=s for every cup C in L and cap D in U. Empty chains and children
are included. There is no one-change, sweep-realizability, order-separation
or positivity assumption.

Forward hereditary avoidance and existing cup-plus-cap gluing give the
coupling. Backward, a crossing strong set has cup/cap intersections by the
existing exact characterization; their disjoint partition has size s+1,
contradicting coupling. A noncrossing strong set lies within one child.
This certifies the strong component of DS-COMPOSITION-PROOF.md. Joint
endpoint-profile placement/occupancy and a closed loss invariant remain open.

Receipts:

* Registration20261003-145551-6da113,86s/2298MiB; fixture
  5c81333c2f57221075d5394618d97ecbf667fee8ae476c5b04bc188ab4e631b1.
* First isolated body20261003-145808-24b7c0,5.513s/2101MiB;
  receipt8ff18d25d8ff30828857b06894011d9410078634d6adb243a785c6824bb5a81f.
* Final operationop-ce11a60fd9034d29 succeeded. Candidate
  20261003-145827-2b9f72; original-source20261003-145838-fb67d5,
  receipt9253bb5dc714be5df40f323d89b4258d93026b0bc8085a00b27e7067670e0cb1.
* Full extraction20261003-145923-2b6154,958.779s/5663MiB;
  receipt5feca2747e9974c666e3d6d28e80ddc2ddf6755cf99b1063455a7bd9b0ec39fb,
  fresh frontier/problems[], treecb88435af7a69081.4560d6f33c43b8ee.
* Audits20261003-151528-2972ad, no axiom/layer violations;
  receipt501feea1747e65f147321d1a9201321868d85b5a53bdcb5a7e10920ae47b1fcc.
* Review20261003-151542-8f4e59,
  receipt165ce779089e9f363cabdac61458d21c4339e9a7a4dda181c5f9e21a8a8bdd8c.

Source SHA16638bce03e2c2916ef172d57f4e58d4ed898f1cd645cd08628172e5b06d066d;
body3132db495de0e3964225adb75e0a64a922c3ea286218a8dfc6a7902542999a24.
Search receipt4ad47e5e4bdc73d121722809190cf95c0d5c0ce8577a0ea09ce59116fcdd6b2f.
Durable exact operations in strong-composition-final-operation.json and
strong-composition-isolated-operation.json. Fixed native deadline remains
01:52:46.857271UTC; research/reporting continue, no merge or push.
