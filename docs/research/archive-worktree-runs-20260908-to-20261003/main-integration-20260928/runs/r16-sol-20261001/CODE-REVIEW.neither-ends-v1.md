# R16 neither-marked selector caller: Sol self-review

Reviewed probe_neither_global_ends.py, SHA256
4f3cb17e023bc62c3fe4865bd94f3cbd8874f5a7a1ca6acad56e3fcd8a99056a.
Same configured Sol/xhigh agent in separate setup window063e6ea07ca24bb6;
no independent Astra review under host no-delegation rule.

The caller reuses existing frozen root_words and shared singleton_cut_values,
compiled_evaluator and part implementation. No recurrence or cut algorithm
is reimplemented. Family: 2..4 runs, lengths1..3, <=5 children, neither word
end marked, both marker sides, all physical globals3..k and m1..k-2.
Every legal coupling and both orientations are retained; zero values included.
FIRST and LAST are tested separately against full bound. Paired global ends
and the previous fixed opposite coupling k-A+1 are separate auxiliary counts.
Auxiliary fixed-coupling failures do not fail the first/last candidate process.
Child positions exist and every word has>=2 runs/children by generator contract.
All C labels are indexed by the current maxima, positive and in supported range.
No unit-global substitution or raw unindexed C call occurs.

Timing-only is one longest declared word at a=u=k,m1. Uses persistent2M cache,
closed in finally. Source hashes before/after must agree. Results are durable,
explicit complete flag matches roots/total, and 100-root progress contains rate.
The caller owns execution/resource/reporting; guarded es jobs enforce memory.
No self-chosen computation deadline. No kernel proof credit from C output.

Timing20261001-074604-a78e99: k6 row,40cuts,0candidate/auxiliary failures,
0.589772s, result neither-ends-k6-timing.json, source hashes pinned.
Full k5 scope1242 and k6 scope2944 roots; pessimistic uncached estimates12.2min
and28.9min, reviewafter5min. Persistent memo likely reduces cost.

Reviewed new ad hoc caller and journaled command before further fullscope jobs.
Useful shared algorithms were reused. Promotion deferred: this is a one-off
selector predicate/refinement and adds no reusable mathematical algorithm;
original durable source retained. workflow.probe would require a registered
plugin not currently provided; existing guarded execution is appropriate.
