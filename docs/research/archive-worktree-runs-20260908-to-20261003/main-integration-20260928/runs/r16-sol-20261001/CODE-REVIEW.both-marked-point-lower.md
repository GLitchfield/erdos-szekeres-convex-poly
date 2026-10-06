# R16 both-marked point-threshold lower review — 2026-10-01 09:02Z

Review window: window-ecd3e7c7b5434829. Configured Sol/xhigh self-review.
The repository requests an independent Astra review; the host explicitly permits
only Sol and forbids delegation/model changes. This records that limitation.

Accepted node: ctx_one_level_root_both_marked_point_threshold_lower.
Targeted check 20261001-045854-d7ff87; receipt
6cce41f51fd63866f6f6c9f89115ebf98ed0f11933f2228f04c559949129500d.
Locked type3cc8ecb823117d12; sorry=false; only propext, Classical.choice,
Quot.sound; no nonstandard/uncovered axioms. Build23.29229s,peak1942MiB,4G.
Closed fixture86944ce4838a63527c9f2e8039a08f8ac7eb96cf805bad175d393af6fc9e3545.
Frozen source Both-marked-point-lower.closed.lean SHA256
7554a9a5a42d60412b33c945c67ce113cd8d9fa9d0064db75512e85cb28c0f50.
Receipt-file SHA256
e4f26b0393ac808bf427a58f364546fd5f6a940e14ba34870d5a4b8d78c29746.

Exact hypotheses: 3<=A<=k,4<=G<=k,1<=m<=k-2,k>=3; uniform
child/ext1(side) word with first and last actual word positions marked and
at least one child. Relative opposite global is A,selected global G.
Conclusion T(A,min(G-2,k-m),k)<=root.bound on both axes,with arbitrary old
marker multiplicities and child-run lengths. No upper or selector premise.

Reviewed complete local reuse of independently certified adjacent absorption,
capacity-aware Pascal and short threshold symmetry, plus the new proof layers:
single-level extension primitives; positive/uniform letters; actual end brackets;
relative point capacities own=min(G-2,k-m)-1 and other=A-1; base equality;
first-child opposite leaf with c=k-A+1 and value T(A-1,V,k); proper singleton
block and complement=tail; positive two-level complement shape and MergeLevels.Inv;
absorption at1 with sole first-child marker and older first-word marker witness;
global G<=k; maximum=max(A-2,m+1),selected G-1; normalized root fields;
uniform level1 word,both marked ends,a surviving child; strong induction on G.
Both legal cut orientations and coupling complements are explicit.

Induction recurses only when W=min(G-3,k-max(A-2,m+1))>=2,which proves G-1>=4
and normalized maximum<=k-2. Otherwise W=1 and T(A,W,k)=0,so no inadmissible
IH is used. W=min(V-1,k-A+2),and Pascal supplies exactly the two terms.
The A>=3 premise makes c and A-2 admissible and avoids known A=2 lower failures.
No finite evaluator result or open theorem is used by the Lean proof.
The main source has no sorry/native_decide/axiom token; harness confirms closure.
Only one node is added; original statements remain unchanged; parent is approved5847.

Search/reuse: es searches for first-child singleton/complement limits, indexed
part shape, singleton threshold and first contiguous block. Exact singleton search
finds ctx_singleton_part_bound_eq_threshold. Existing part_other extension,
levelsOn and position APIs reused directly. No other registered first-child
absorption/shape/lower theorem was found. Imported duality module was rejected
by targeted4GiB closure guard (28.4GiB); short closed symmetry proofs reused locally
under thin imports instead. All meaningful compiler failures are journaled.

Ad hoc code review also covers the two extra both-marked upper diagnostic wrappers,
point_base_candidate.py,existing runner and prior snapshots,and recorded job argv.
The family wrapper checks exactly810k5+1728k6roots (opposite>=3,2..4runs,
run lengths1..2,<=4children,all legal globals/maxima,both sides). It pins sources
before/after, closes persistent C evaluators and explicitly enables the existing
closed unit-global zero rule. Fixed fixture wrapper checks four k5/6 maximal-global
both-axis roots. All results are finite diagnostic evidence only.
The completed9792-root one-marked five-child job's source hashes match launch;
its52.5-minute pass includes2992explicit unit-rule roots and6800C evaluations.
Original wrapper sources and result artifacts are preserved.

Library search/show: research.compiled-context-bound supplies the reusable
persistent evaluator; workflow.recursive-cut-probe has a fixed unrelated domain.
Consolidation adds optional --direction to the existing run-local point runner
(default one/upper,both/lower preserved) and before/after source hash assertion.
The exact earlier runner bytes are preserved in
probe_one_marked_point_base-before-upper-direction.py,SHA256
23c2b2b4cba253aadd0e3770b0ebd18768ffc2ceee54233e65948c8c9ba7598c.
Guarded validation jobs050229-2561cc (both upper),050229-9c43b4(default both lower)
passed810/810k5roots each,0violations,162explicit unit-rule roots each,matching
the prior k5 domains; about0.94s candidate/1.2s guarded,62/51MiB.
050229-b85510(default one-upper timing) passed1/1,0violations,0.02186s,35MiB.
All source hashes stayed fixed; output counts/directions and artifacts inspected.

No tracked Python/C/workflow source changed. No new recurring mathematical
algorithm needs generic promotion: independently certified Lean helpers already
have their own node commits. The run-local runner is consolidated instead of
creating further wrappers. Shared unit-global evaluator shortcut is deferred
to separate authorized library work; current evaluator contract remains unchanged.
Usage/resource coverage gaps for direct jobs remain explicit,not zero-work claims.

This lower theorem is a reusable proof component,not N_ends/N_root closure.
Common universal depth-zero inert-barrier upper and neither-marked selector remain open.
