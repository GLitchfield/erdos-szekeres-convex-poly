# Pair-limit proof and code review

2026-10-02 15:00 UTC, review window `window-882dc47915a3436d`.
Sol self-review under the fixed no-delegation contract; independent coordinator
review remains pending. The 10,000-output-token target is observational.

Reviewed pinned module at `c37f3751de15f776209110fdf31048fa3d8b2319`, frozen
fixture `5bca4fc196358a1fe58af1f8170650712fe69d57a1c7a59aafec7ee5eafc0477`,
body artifact, original-source result, changed tracked files, and inline
preservation/lock-comparison command. No new mathematical Python script or
tracked workflow script was introduced during this trial. The three earlier
ad hoc research scripts and tracked falsifier retain their first-pass review.

The argument covers arbitrary child indices, not only the first pair. The
finite-set order embedding is injective and strictly increasing. Its rank
identity is established by an exact set equality and cardinality of `Fin.Iio`;
it does not assume a dense ambient index set. Sorted child positions establish
the index ordering. Cardinality two follows from distinct embedded vertices.
The local no-triple argument is independent of coloring; both cup and cap
constraints are then applied. Empty sets and `n=0` introduce no exceptional
case because two distinct child positions are impossible under the length
equality. No WellFormed premise is smuggled into the proof.

The original-source check reports CLOSED, no sorry and standard axioms only;
the type hash and lock match. All 378 inherited lock records are compared as
parsed objects to the exact base, with only one new entry. The preservation
command copies the actual job result, verifies the closed/type/sorry fields,
and calls existing `es.artifacts.put_json/canonical`; no independent receipt or
execution mechanism was invented. Its durable result is receipt
`7835038cff4025744af5b60c676263d34ca8192bea6b0505951f369c424668d4`.

The heavy pair-lemma import was removed rather than altering extraction caps.
Local vacuity is preferable here to a duplicate exported theorem. A later core
layer cleanup may move the existing pair lemmas to a thinner module; that is
deferred because it is unrelated to this one-node proof and would broaden its
review scope. The rank argument is reusable Lean mathematics, already saved
as the registered theorem. No general Python/workflow promotion is warranted.

The result supplies a necessary condition for `Satisfies`, not a sufficient
condition or an actual geometric realization. The exact PEEL witness must be
checked against this condition separately. The witness's raw-context
refutation and the happy-ending conjecture have different scopes.
