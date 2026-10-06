# Inactive insertion does not preserve recursive positivity

Kernel-closed node ctx_inactive_child_insertion_bound_zero_counterexample,
type dfd8a94981aa38aa. Explicit WF oldσ/newτ have globals4/4/4 and equal
maxima[2,1,1,1]. Oldword1L,2U,1L,1L,3U,4L,S; newword1L,2U,S,1L,3U,4L,S
is exactly oldword.set2child. Oldchildren[6], newchildren[2,6]/twoactualruns.
Insertedchild2cup0cap1; survivingchild6 has cup=cap1 in both contexts.
Oldfullbound1, newfullbound0. This rejects recursive lower transport based
only on stable surviving point capacities and insertion of inactive children.

It does not contradict ctx_bound_mono_of_zero_capacity_marker_inclusion:
that theorem's target-marker-position-subset hypothesis fails for this
marker-to-child replacement. No unrestricted maximal-segment FLIP failure
or geometric Erdős–Szekeres counterexample is asserted.

First proof check071708-8601bf passed:44.6s2343MiB/OOM0/budgetfalse,
innerbuild4.227200747s. Full receiptCHECK.inactive-insertion-v1.json,
FILE SHA378cb1c3d7d7fc4a68754664957025dc1cccaa383a5e507ec928018902004bcd
recordsclosed/Std/noSorry/locktrue/blocks[]/errors[]/targeted+incrementaltrue.
Checked sourceINACTIVE-INSERTION.candidate-v1.txt SHA
42eb5c3509ae4d4dd4bb8d033a1058fd85ecc72ed853127fa9304aaae8860b0b.
Explicit seven-position WF proofs plus ordinary kernel decide for two-child
arithmetic; no helper overlay/C/native_decide/axiom/sorry. Fixture
07469fa87ab7944535188125f8a15cc48399a7dafb1720f8b34ca42211379d43
(9081B) captured registered stub before proof. Registration071420-76930a
on independent-main branch created by071345-42a67b. Diagnostic probe
070437-9c68ee/.002804327s, inactive-insertion-timing.json, motivated the
claim but gives no theorem credit independently. No failed proof attempt.

Open: positive-k>=4 paired uncrossing for entire maximal membership segments.
Stable exterior trace lemmas may help compute capacities, but require an
additional full recursive comparison with actual cut structure. Positive
part implies a source-history ceiling; that proposed reduction is not yet
registered or kernel-certified. All proof/probe artifacts remain under R15.

One-node commit completed by071842-80549a:
86937b3f8b3507dfc1e4cd8b44fba3318042c46e on
node/CtxInactiveChildInsertionBoundZeroCounterexample. Exactly ownmodule,
rootimport,lock,index,status records; no uncommitted source remains.
