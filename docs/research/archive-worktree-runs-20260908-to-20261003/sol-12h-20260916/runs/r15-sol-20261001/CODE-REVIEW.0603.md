# R15 certificate and probe self-review, 2026-10-01 06:03Z

Reviewed by the configured Sol agent in separate window
window-6d1f8cf4a4bf4f5f. The explicit Sol-only/no-delegation restriction takes
precedence over the AGENTS Astra-review workflow. This is a self-review, not
an Astra review. The native research goal remains active; clean Eight job
55bf5a and every-coupling five-child job1900fa are followed during this window.

Sources read completely: generate_eight_cut_dag.py, emit_eight_cut_proof.py,
project_eight_cut_bounds.py, emit_eight_projected_proof.py,
probe_segment_depth4.py, probe_fixed_coupling.py and
probe_reoptimized_coordinatewise.py. Original versions, source snapshots and
failed generated candidates are retained. Earlier falsifier/eight-family code
was covered by CODE-REVIEW.interim.md.

The DAG generator enumerates every proper nonempty child-order interval,
every legal coupling and both orientations. Subcontexts strictly reduce the
child count and include the unchanged globals, shifted external levels and
prepended sibling maximum in the memo key. Its C factory is fixed at(6,6,6),
so this remains a fixed-witness generator, not a generic parameter evaluator.
Point-sum equality and attaining cuts are untrusted hints. Leaf cases never
call a six-child exact evaluator; every proposed root/context has1–4children.

The projector separates upper and lower inequalities. Upper proofs cover all
cuts unless a point-sum or closed maximum bound suffices; lower proofs need
only one attaining cut, or Nat nonnegativity at zero. Slack is allocated only
to upper budgets, whose sum equals the parent budget. Memo keys include kind,
context and budget. The optional maximum shortcut selects only the shared
formula with reason indexed maximum at least k-2 and bound1; other exploratory
maximum formulas are not used. Defaults remain unchanged by regression.

Both emitters produce text candidates and perform no compilation, source
mutation or scheduling. Every numerical base/point-sum fact, literal part
equality, complete interval-block list and legal coupling is checked by Lean.
The scoped emitter uses ordinary as_aux_lemma proofs with closed literal
types. Last-use scheduling considers every explicit cut reference, asserts
earlier dependencies and preserves all upper/lower roots for the footer.
Clearing unused local hypotheses reduces elaboration memory; it is not a
claim that exported proof constants disappear. The full accepted receipt has
4209 actual direct dependencies, including numerical auxiliaries and CutLe.

The original global-let12007-fact and un-cleared4844-fact candidates were
cancelled at documented memory checkpoints, not elapsed time limits. Their
empty CHECK files and lack of receipts grant no theorem credit. Cancelled
wrapper peak0 means unavailable measurement. Final-phase memory increased
beyond the per-fact forecast; actual full c5a15f outer peak14553MiB is retained.
The duplicate namespace-end failure was caused by applying whole_span byte
offsets to decoded text. Corrected candidates slice bytes and assert exact
statement-prefix/suffix preservation and one namespace end.

The complete fixed Eight receipt0e443efc79ea0f9fb46f831d4180c3b7398877a44d63b11f673ac85c199041b6
is closed, no sorry, locked type8df31f7cd295f110, only propext/Classical.choice/
Quot.sound, no uncovered axioms or tag errors. Imported EndCut warnings do
not occur in the theorem's actual axioms. Progress IO is operational and
not a logical axiom, but an ignored runs path makes source nonportable. The
clean source removes264 exact two-line writes, retains4204facts and the
footer, and is undergoing a fresh complete targeted check before commit.

The depth4 sampler chooses four occupied levels, one side per level, mixed
maxima,4–6markers and at least two physical child runs. Five-child mode tests
all complementary interleaved classes. Six-child mode tests only010101,
whose original3/3 and flipped2/4 parts ensure every C query has at most4kids.
Default five/six candidate outputs match their preserved source versions.
The k3 modes reuse64 shapes with globals2/3, all maxima1 and mixed/uniform
side patterns; they test a zero-value strengthening separately from FLIP.
The completed768row/3840class diagnostic is not an all-context proof.

Fixed-coupling input extensions freshly recompute the original selected
maximum and both parts before testing flips. Every-coupling mode enumerates
all old d/orientations and compares matching d/orientations after every maximal
segment, retaining free-coupling counts separately. Zero old profiles are
reported explicitly. A fixed-coupling miss would refute only that strengthening,
and a coordinatewise miss does not refute the paired inequality. Input/profile
hashes and cold bounded memos identify semantics; audits verify structure and
reported arithmetic, not independent recursive values or Lean proofs.

Inline work reviewed: byte-splice/namespace corrections; exact source-hash
overlays; footer/root remapping; IO stripping; receipt pagination and field
checks; diagnostic domain/coupling/sum/count audits; cgroup memory checkpoints
and supported stopped-scope reconciliation. An accidental complete auxiliary
dependency print produced excessive output; later reports use counts and
external dependency summaries. No result relied on truncated JSON or a
successful process exit without the full receipt.

Reuse and maintenance: shared C evaluator, context-part, limits/threshold,
maximum_bounds and whole_span APIs were reused. No promotion is made now:
the mathematical generator is validated on one fixed theorem and its five
numerical roots, and footer assembly remains specific to that statement.
Generic certificate semantics and a second independent caller are not yet
established. Preserve artifacts rather than generalize one-off mathematics
solely to grow the catalog. The liveness algorithm is a candidate for later
promotion with a small fixture if another certificate needs it.

Automatic inventory ec9150e63ab655b2eb59f8ee80c96968134be3f83c730e1a1382679fb67114ad
was fetched completely. It hashes17artifact scripts and22tracked files relative
to host baseline95559e..., including other-agent main integrations. These are
not22R15 changes. Its native usage/proof and inline-command coverage is
unavailable, not zero. Separate es usage sync provides recorded session costs;
neither inventory nor this review adds theorem credit or establishes savings.
