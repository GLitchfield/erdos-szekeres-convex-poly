Prove `ctx_bound_reverse`: reversing any well-formed context's word preserves
its recursive bound, including empty and single-run contexts. This supplies
reflection for the singleton-end sandwich argument. The proof transports legal
cuts and their parts, compares the single-run bases, then inducts on fuel and
uses reversal twice to obtain equality.

Search found no duplicate (`search-reflection.final-before-registration.json`).
The proof reuses the checked `ctx_reverse_extension_transport` and
`ctx_point_limits_eq_of_child_interval` nodes found by `es search`; their type
hashes are `4d6c2aaed124fffe` and `817ec12effbc65aa`. No other node statement is
changed.

Validation: guarded scratch audit `20260929-201544-f6a775`, targeted
registration `20260929-200349-567bbc`, isolated accepted proof
`20260930-015957-47d5b7`, and original-module targeted check
`20260930-020436-781047`. The last receipt
`492f82808b20c3216db2349a8bbf5fca32262d1b5788e4579dc8cf0855ec0dab` certifies
closed status, no sorry, matching type lock `4125616738b08f1d`, and only
`propext`, `Classical.choice`, `Quot.sound`. No full extraction was run.

Delivery limitation: Git metadata is mounted read-only, so this draft has no
commit or published PR. `ctx-bound-reverse.patch` preserves the exact theorem,
root import and statement-lock entry for a coordinator with writable metadata.
Generated index/status claim snapshots are excluded. Actual dependencies also
include the checked point-interval theorem and compiler-generated auxiliaries;
the declared tag lists reversal transport.
