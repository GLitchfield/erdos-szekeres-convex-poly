# R17 mathematical handoff — Done (narrowing)

Oct2 00:53 UTC: unchanged X has a compiling conditional proof at
ff30db6aabe274a5677bfc88b670351e6b821c4a/typea68960f119792789, with four
closed cases and exactly two new strict open residuals. It retains their
transitive sorryAx. Twelve independent nodes are fully closed/committed;
the proposed exact-difference finite selector certificate remains pending.
Historical findings are preserved in MATHEMATICAL-HANDOFF.history-before-0053.md.

Fix k>=3,1<=a,u<=k,1<=m<=k-2, and an old side b. Let left/right contain only
children S or physical markers E(1,b). Write
sigma.word=left++[S,S]++right, rho.word=left++[S]++right, maxima=[m].
Assume sigma has at least2 child runs, p is a child, source side s and
1<=c<=k-2. Map q=p when p<=length(left), otherwise q=p-1. Define
T_sigma(s,c) as decomposableThreshold(cap+1,cup+1,k) at singleton p in
sigma.part[p]s c. Define C_sigma(s,c) as the full bound of the complementary
part with opposite(s),k-1-c. X asks for one legal t,d satisfying

    T_sigma(s,c)+C_sigma(s,c) <= T_rho(t,d)+C_rho(t,d).

All terms, part histories and zero-valued children are retained. No replacing
T by an unaudited recursive bound, and no separate choice per summand.

The closed boundary for source-opposite<=2 works at the SAME side/coupling:
an actual fresh marker annihilates the SOURCE complement, then outside leaf
agreement or inside two-run leaf monotonicity yields full-sum transport.
It makes no target-complement monotonicity claim. The generic helper is
ctx_pair_contraction_singleton_value_mono_of_opposite_global_two,
a7e7b6b71bc3dbce0b16e459c4103c91b66ccc3a/typeef8f2f46dd387851. It requires
exact closed leaf inputs f3c21cb85f0eccc1a21ad2d5b1be4583f44e26d8 and
463b7f9d5fa23db7733a0fe8c0fa303f5fdbdeb6. The raw marker-zero fact is also
independently exposed as bb4647871239844a3438ab7b7c11418991b11443/type
dae6380c2e356e7c: actual indexed marker, consumed global<=2 implies zero
for every fuel and full bound, without WF/positivity/root/maximum premises.

The two remaining statements additionally require a,u>=2, old-marker
consumed axis>=3, and SOURCE-cut opposite global>=3. Old Lower consumes u,
old Upper consumes a; source Lower opposite is a, source Upper opposite is u.
The axes must be distinguished explicitly:

| Old marker | Consumed axis | Source side | Source-complement consumed axis |
| --- | --- | --- | --- |
| Lower | u | Lower | a |
| Lower | u | Upper | u |
| Upper | a | Lower | a |
| Upper | a | Upper | u |

These restrictions do not imply both axes>=3: oldLower/sourceUpper/a2/u4
is still in the residual domain. Do not discard the retained forced-flip
witnesses by confusing those axis tests.

Inside residual:
ctx_one_level_root_singleton_base_exchange_inside_pair_source_opposite_three,
commitb6c49e789a2cc62502e05ca956444a870f860856/typeb181a91c08f66627,
p=length(left) or length(left)+1. The full joint inequality above remains
missing. Leaf monotonicity alone does not absorb complement loss.

Outside residual:
ctx_one_level_root_singleton_base_exchange_outside_multirun_source_opposite_three,
commit66d99030d065cb12d3b00454d27a42bc5787509b/type9ea660e19ac2367a,
p differs from both pair indices, and the ACTUAL SOURCE complement has>=2
runs. Same-cut leaf equality is closed, but the complement can fall; a joint
legal orientation/coupling exchange remains missing.

Guarded k3..5 diagnostics passed48256/51968 selected cuts, not proofs. The
six-case pure partition removes27648 formerly open original k6 cuts. Earlier
broader residual statements/commits and X68 are preserved, not restated.
Integration: use eight exact dependency commits and the15-file archive
07bb915fa98f5fe672b6aa5532e7072d1ee633ca01405170e517dd3dab5116db,
MANIFEST.X-refined-dependencies.json/INTEGRATION.X-refined.md. Six dependency
nodes are closed/two open. X original targeted192553-ec5439 passed301.1s,
2386MiB/20G, with sourcefe0980 unchanged and exact original type. No global
index freshness claim:8 records absent; existing incremental4GiB limit
blocks unrelated28.4726GiB closure. Full extract/override is prohibited.

Selector limitations matter to a proof method. Leaf-only choice of orientation
is already kernel-refuted by3b8a2dce55b334284f9908183eb79df833d6b723.
Capping numerical axes at3 is kernel-refuted by
a1de7d72dd9f7f0c180a73bfffbbf8d6316bb300, even with exact compressed geometry:
wordS,1Lower,S,S; k6/m1; p=q=y2; sourceLower4; axes(4,5)/(5,4);
source7 each, but no common legal target rescues both. Each is individually
rescued. New saved-data models retaining order or exact axis difference also
fail on finite cells. The proposed identical-leaf claim was false:205141-5d41c3 rejected four
leafcap1/cup3 equalities. Actual limits are(2,2)/(3,2), so retaining actual
leaf limits may distinguish these roots. The mistaken registered statement
is preserved unedited on88a7946f6e5076e0bf193ea09bec5d2a1728e71a. A separate
corrected certificate and exact negative component are pending; no credit
until complete-parent and original-source closure.

The full numeric compressed-feature model has nonempty common rule sets on
1179648 cells covering1677312 combined cuts, plus compatible alternatives
for8 saved longer failures. The original frozen rule failed7220 new cuts.
This finite consistency is not an unbounded selector theorem or a proof of X.
Long-row cost precluded any broader7-child sweep. See SELECTOR-HANDOFF.md for
exact positive/negative scopes and saved root/data pins.

The next useful proof must bound C_sigma together with the target leaf gain,
using one legal target side and coupling. It cannot rely on leaf monotonicity,
a fixed default cut, axis caps/order/difference alone, or a finite-table axiom.
Preserve the original legal domains and physical marker/index hypotheses.
A future agent must claim its own node normally and preserve exact old
approvals; the assembly helper does not authorize impersonation. No further
trial, primary repairs, full extraction, merge/push or other-job control here.
