# Two-axis near-saturated boundary histories: closed

Node ctx_bound_zero_of_both_sides_near_saturated_boundary_histories,
type c152a4d63bf7a6eb, commit4e91b41d985b3702b39302fe0e8c2b32b22ce20c.
Own main-based node branch b99a1d; commitdf6fc3done0 includes exactly own
module/root/lock/index/status. Two exact accepted source overlays excluded
and removed afterward: boundary18 commit1ea1e06b and CutUpper05165669.
Integration must supply those closed dependency commits before this node.

Exact hypotheses: raw positive actual external labels; at least two child
runs; for each side s there exist indexed levels J<M on s and an actual
J-marker x before all source children or after all source children, with
maximumAt M >= k-3. Witness levels, marker and boundary direction may differ
between the two sides. Globals, history length and unused indexed levels
are unrestricted; no WellFormed assumption. Conclusion σ.bound=0.

Proof: every proper part on either side omits an actual source child,
so boundary18 gives full part zero independently of the new maximum.
Each proper interval block has an omitted source r and a retained b.
The block/complement parts in all four orientations vanish.
Accepted all-interval-cut upper characterization implies full source zero.
Source BOTH-BOUNDARY-ZERO.candidate-v1.txt SHA
b016de198b48ff28071a1a4168691f5e7f160ca2d4684f659160c0587b8820a2.

Registration054634-1beac3done0/104.2s/2349MiB/OOM0.
Minimal stub omitted the closed CutUpper import; targeted registration
reported that declared dependency unknown. Own forced claim explicitly
limited to this import/index setup, then capture
0b7c5ce4a9972ed5a5c6de898d020a85c077befc910cb0f69df7783745aea0fe
10175B before adding exact closed import and proof. Statement unchanged.
First proof check054947-c4168bPASS46.6s/2348MiB/OOM0/build3.022862434s.
Complete3876B receipt
de3c573ca84467ba20b01828bf7096cfb8c108d584d64b09d30563ffd25c348a
saved CHECK.both-boundary-zero-v1.full.json:
closed/Std/noSorry/locktrue/blocked[]/tagerrors[]/targeted+incrementaltrue.
No compiler failure, native_decide, axiom or generated certificate.
Search found no exact both-axis boundary-near-zero duplicate.

Open obligation: full positive any-length maximal-segment FLIP at k>=4,
arbitrary WF context/keep/history with free right orientation/coupling.
The new zero criterion strengthens the prior k-2 both-axis zero mechanism
to k-3 with younger exterior markers; it does not prove positive exchange.
Next finite lower-shortcut certificate:4/4/4
word1L,2U,S,3L,4U,S/maxima1,1,1,1/kids2,5/full0/allpointcup=cap1
(diagnosticfef51f only currently). A direct ordinary kernel decide on two
children can certify this independently of the generic zero proof.

Pending diagnostic job20261001-055028-bb1ff0 must be followed to terminal:
k4-six-all-sample.json,576retained rows/16canonical interleaved classes
per row (9216planned), all maximal homogeneous segment flips, free
coupling/orientation against exact old maximum. Existing frozen profile
b761f2c3 reused; new driverbd9cd8fa... adds only κ4-six modes.
Structural validation0aa99c578shapes/legacy generators equal archive,
16classes per row; timingd84d0b2rows/32classes/28positive/4zero/0misses,
algorithm0.899246662s/outer1.2s254MiB/OOM0. Estimate6–10min including
growing JSON prefix I/O, review5; no chosen time kill. No sample result
or Lean theorem credit until terminal output inspected. Source/archive,
validation/timing and inline commands remain durable under this run.
Claim release concerns the closed theorem; reporting turn stays open
and stored jobbb1ff0 remains the ongoing research obligation.
